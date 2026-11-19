/-
The Lean server of xlint. It reads one JSON request per line and writes one response per line.
The state before each theorem is kept, so a theorem can be checked again alone with edited
text. Offsets are bytes into the file.
-/
import Lean

open Lean Elab

namespace Xlint

structure Range where
  start : Nat
  stop : Nat
  deriving ToJson, FromJson, BEq

structure Edit where
  range : Range
  text : String
  deriving ToJson, FromJson

structure Piece where
  kind : String
  text : String
  range : Range
  line : Nat
  deriving ToJson

structure Decl where
  key : String
  name : String
  range : Range
  line : Nat
  ok : Bool
  pieces : Array Piece
  deriving ToJson

/-- A theorem as loaded: its text and the state to check it from. -/
structure Loaded where
  decl : Decl
  before : Command.State

structure State where
  file : String := ""
  text : String := ""
  loaded : Array Loaded := #[]

def sub (text : String) (start stop : Nat) : String :=
  String.Pos.Raw.extract text ⟨start⟩ ⟨stop⟩

/-- The byte offsets of the line that holds `pos`: its start and the start of the next line. -/
def lineOf (text : String) (pos : Nat) : Nat × Nat := Id.run do
  let bytes := text.toUTF8
  let mut start := pos
  while start > 0 && bytes[start - 1]! != 10 do start := start - 1
  let mut stop := pos
  while stop < bytes.size && bytes[stop]! != 10 do stop := stop + 1
  return (start, if stop < bytes.size then stop + 1 else stop)

def blank (s : String) : Bool := s.all Char.isWhitespace

def lineNumber (text : String) (pos : Nat) : Nat :=
  (sub text 0 pos).foldl (fun n c => if c == '\n' then n + 1 else n) 1

def range? (stx : Syntax) : Option Range :=
  stx.getRange?.map fun r => { start := r.start.byteIdx, stop := r.stop.byteIdx }

/-- A `have` that fills its own lines goes with them. One that shares a line is left alone. -/
def havePiece (text : String) (stx : Syntax) : Option Piece := do
  let r ← range? stx
  let (first, _) := lineOf text r.start
  let (_, next) := lineOf text r.stop
  guard (blank (sub text first r.start) && blank (sub text r.stop next))
  let head := (sub text r.start r.stop).takeWhile (· != '\n')
  some { kind := "have", text := head.toString, range := { start := first, stop := next }, line := lineNumber text r.start }

/-- A lemma of a `simp [...]` list goes with one comma, the last one with the brackets. -/
def simpPieces (text : String) (list : Syntax) : Array Piece := Id.run do
  let args := list.getArgs
  let lemmas := (List.range args.size).filter (· % 2 == 0) |>.toArray
  let mut pieces := #[]
  for i in lemmas do
    let some r := range? args[i]! | continue
    let piece (range : Range) : Piece :=
      { kind := "fact", text := sub text r.start r.stop, range, line := lineNumber text r.start }
    if lemmas.size == 1 then
      -- ` [h]` goes whole, with the space before it
      let bytes := text.toUTF8
      let mut start := r.start
      while start > 0 && bytes[start - 1]! != '['.toNat.toUInt8 do start := start - 1
      let mut stop := r.stop
      while stop < bytes.size && bytes[stop]! != ']'.toNat.toUInt8 do stop := stop + 1
      if start > 1 && stop < bytes.size then
        let open_ := if bytes[start - 2]! == 32 then start - 2 else start - 1
        pieces := pieces.push (piece { start := open_, stop := stop + 1 })
    else if i + 2 < args.size then
      let some next := range? args[i + 2]! | continue
      pieces := pieces.push (piece { start := r.start, stop := next.start })
    else
      let some previous := range? args[i - 2]! | continue
      pieces := pieces.push (piece { start := previous.stop, stop := r.stop })
  return pieces

def isHave (stx : Syntax) : Bool :=
  stx.getKind.toString.startsWith "Lean.Parser.Tactic" && stx.getNumArgs > 0 && stx[0].isToken "have"

def isSimpList (stx : Syntax) : Bool :=
  stx.getNumArgs > 0 && stx.getArgs.all fun arg =>
    arg.isToken "," || arg.getKind == ``Lean.Parser.Tactic.simpLemma

partial def pieces (text : String) (stx : Syntax) : Array Piece :=
  let here :=
    if isHave stx then (havePiece text stx).toArray
    else if stx.getKind == nullKind && isSimpList stx then simpPieces text stx
    else #[]
  stx.getArgs.foldl (fun found arg => found ++ pieces text arg) here

partial def hasBy (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.byTactic || stx.getArgs.any hasBy

partial def declName (stx : Syntax) : Option String :=
  if stx.getKind == ``Lean.Parser.Command.declId then some stx[0].getId.toString
  else stx.getArgs.findSome? declName

def isTheorem (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Command.declaration &&
    (stx[1].getKind == ``Lean.Parser.Command.theorem || stx[1].getKind.toString.endsWith "lemma")

/-- A check fails on an error, and on `sorry`, which is only a warning. -/
def failure? (messages : MessageLog) : IO (Option String) := do
  for message in messages.toList do
    let text ← message.data.toString
    if message.severity matches .error then return some text
    if text.contains "sorry" then return some text
  return none

/-- Parse and elaborate the next command of `inputCtx`. -/
def step (inputCtx : Parser.InputContext) (state : Command.State) (parser : Parser.ModuleParserState)
    (cancel : Option IO.CancelToken := none) : IO (Syntax × Command.State × Parser.ModuleParserState) := do
  let scope := state.scopes.head!
  let pmctx := { env := state.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (stx, parser', messages) := Parser.parseCommand inputCtx pmctx parser {}
  let context : Command.Context :=
    { cmdPos := parser.pos, fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := cancel }
  let run := (Command.elabCommandTopLevel stx context).run { state with messages }
  match ← (EIO.toIO' run) with
  | .ok (_, state') => return (stx, state', parser')
  | .error e => throw <| IO.userError (← e.toMessageData.toString)

def load (file : String) : IO State := do
  let text ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext text file
  let (header, parser, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    let errors ← messages.toList.mapM (·.data.toString)
    throw <| IO.userError s!"{file}: cannot process the imports: {" ".intercalate errors}"
  let mut state := Command.mkState env {} {}
  let mut parser := parser
  let mut loaded := #[]
  repeat
    let before := state
    let (stx, state', parser') ← step inputCtx state parser
    state := { state' with messages := {} }
    parser := parser'
    if isTheorem stx && hasBy stx then
      if let some range := range? stx then
        let ok := (← failure? state'.messages).isNone
        let decl : Decl :=
          { key := s!"{file}:{range.start}", name := (declName stx).getD "", range, line := lineNumber text range.start,
            ok, pieces := pieces text stx }
        loaded := loaded.push { decl, before }
    if Parser.isTerminalCommand stx then break
  return { file, text, loaded }

def applyEdits (text : String) (range : Range) (edits : Array Edit) : String := Id.run do
  let sorted := edits.qsort (·.range.start > ·.range.start)
  let mut stop := range.stop
  let mut out := ""
  for edit in sorted do
    out := edit.text ++ sub text edit.range.stop stop ++ out
    stop := edit.range.start
  return sub text range.start stop ++ out

/-- Check the theorem once with the edits. Returns the verdict and the wall-clock ms. -/
def runOnce (state : State) (l : Loaded) (edits : Array Edit) (timeoutMs : Nat) : IO (String × Nat × String) := do
  let source := applyEdits state.text l.decl.range edits
  let inputCtx := Parser.mkInputContext source state.file
  let cancel ← IO.CancelToken.new
  let finished ← IO.mkRef false
  let _timer ← IO.asTask (prio := .dedicated) do
    let mut waited := 0
    while waited < timeoutMs && !(← finished.get) do
      IO.sleep 20
      waited := waited + 20
    unless ← finished.get do cancel.set
  let start ← IO.monoMsNow
  let result ← (step inputCtx { l.before with messages := {} } {} (some cancel)).toBaseIO
  let ms := (← IO.monoMsNow) - start
  finished.set true
  if ← cancel.isSet then return ("timeout", ms, "")
  match result with
  | .error e => return ("fails", ms, toString e)
  | .ok (_, after, parser) =>
    if !blank (sub source parser.pos.byteIdx source.utf8ByteSize) then
      return ("fails", ms, "the edited text is more than one command")
    match ← failure? after.messages with
    | some message => return ("fails", ms, message)
    | none => return ("closes", ms, "")

def answer (state : State) (question : Json) : IO Json := do
  let key := (question.getObjValAs? String "key").toOption.getD ""
  let reply (verdict : String) (ms : Array Nat) (message : String) : Json :=
    Json.mkObj [("response", "answer"), ("answer", Json.mkObj
      [("key", key), ("verdict", verdict), ("ms", toJson ms), ("message", message)])]
  let decl := (question.getObjValAs? String "decl").toOption.getD ""
  let some l := state.loaded.find? (·.decl.key == decl) | return reply "error" #[] s!"no declaration {decl}"
  if (question.getObjValAs? String "do").toOption != some "run" then
    return reply "error" #[] "only run is supported"
  let edits ← IO.ofExcept (question.getObjValAs? (Array Edit) "edits")
  let timeout := (question.getObjValAs? Nat "timeout_ms").toOption.getD 30000
  let runs := (question.getObjValAs? Nat "runs").toOption.getD 1
  let mut times := #[]
  for _ in [0:max runs 1] do
    let (verdict, ms, message) ← runOnce state l edits timeout
    if verdict != "closes" then return reply verdict #[ms] message
    times := times.push ms
  return reply "closes" times ""

def respond (state : IO.Ref State) (request : Json) : IO Json := do
  match (request.getObjValAs? String "request").toOption with
  | some "hello" =>
    return Json.mkObj [("response", "hello"), ("hello", Json.mkObj
      [("prover", "lean"), ("version", Lean.versionString), ("closers", toJson (#[] : Array String))])]
  | some "load" =>
    let file ← IO.ofExcept (request.getObjValAs? String "file")
    state.set (← load file)
    return Json.mkObj [("response", "loaded"), ("decls", toJson ((← state.get).loaded.map (·.decl)))]
  | some "ask" =>
    answer (← state.get) (← IO.ofExcept (request.getObjVal? "question"))
  | _ => return Json.mkObj [("response", "error"), ("message", "unknown request")]

partial def serve (state : IO.Ref State) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let line ← stdin.getLine
  if line.isEmpty then return
  let response ←
    try respond state (← IO.ofExcept (Json.parse line))
    catch e => pure (Json.mkObj [("response", "error"), ("message", toString e)])
  stdout.putStrLn response.compress
  stdout.flush
  serve state

end Xlint

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  Xlint.serve (← IO.mkRef {})
