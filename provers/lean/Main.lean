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
  deriving ToJson, FromJson, BEq, Inhabited

structure Edit where
  range : Range
  text : String
  deriving ToJson, FromJson

structure Piece where
  kind : String
  text : String
  range : Range
  line : Nat
  /-- Texts the definition lints try in place of the piece. -/
  replacements : Array String := #[]
  /-- The list the piece is an item of, with its brackets. -/
  whole : Option Range := none
  deriving ToJson

structure Step where
  text : String
  range : Range
  line : Nat
  candidates : Array String
  deriving ToJson, Inhabited

structure Decl where
  key : String
  name : String
  kind : String
  range : Range
  line : Nat
  ok : Bool
  steps : Array Step
  simps : Array Step
  pieces : Array Piece
  /-- What a probe may test: `vacuous`, or `always` and `never`. -/
  probes : Array String := #[]
  deriving ToJson

/-- A command like `#eval`, which proves nothing. Its range is the lines to delete. -/
structure Diagnostic where
  name : String
  text : String
  category : String
  range : Range
  line : Nat
  ms : Nat
  deriving ToJson

/-- A top-level command, with the ms it took when the file was loaded. -/
structure Timed where
  kind : String
  text : String
  range : Range
  ms : Nat
  deriving ToJson

/-- How often `simp` tried a rule in one theorem, and how often it rewrote with it. -/
structure Rule where
  name : String
  tried : Nat
  used : Nat
  deriving ToJson

/-- A theorem as loaded: the state to check it from, and the goal each step closed. -/
structure Loaded where
  decl : Decl
  before : Option Command.State
  goals : Array (ContextInfo × TacticInfo)
  /-- The goals before each of `decl.simps`. -/
  simpGoals : Array (ContextInfo × TacticInfo) := #[]
  /-- The constant the command added, and the environment with it. -/
  const : Name := .anonymous
  after : Option Environment := none

structure State where
  /-- The `-D` options the server was started with. -/
  options : Options := {}
  file : String := ""
  text : String := ""
  loaded : Array Loaded := #[]
  diagnostics : Array Diagnostic := #[]
  commands : Array Timed := #[]

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

/-- What deleting each item of a comma-separated list removes: the item with one comma, or
`whole` if it is the only one. -/
def itemRanges (args : Array Syntax) (whole : Range) : Array (Range × Range) := Id.run do
  let items := (List.range args.size).filter (· % 2 == 0) |>.toArray
  let mut found := #[]
  for i in items do
    let some r := range? args[i]! | continue
    if items.size == 1 then found := found.push (r, whole)
    else if i + 2 < args.size then
      let some next := range? args[i + 2]! | continue
      found := found.push (r, { start := r.start, stop := next.start })
    else
      let some previous := range? args[i - 2]! | continue
      found := found.push (r, { start := previous.stop, stop := r.stop })
  return found

/-- A lemma of a `simp [...]` list goes with one comma, and the last one left with the brackets
and the space before them. -/
def simpPieces (text : String) (list : Syntax) : Array Piece := Id.run do
  let some r := range? list | return #[]
  let bytes := text.toUTF8
  let space := fun (b : UInt8) => b == 32 || b == 10
  let mut start := r.start
  while start > 0 && space bytes[start - 1]! do start := start - 1
  let mut stop := r.stop
  while stop < bytes.size && space bytes[stop]! do stop := stop + 1
  -- `nontriviality α using a, b` has the same list without brackets
  unless start > 1 && stop < bytes.size && bytes[start - 1]! == '['.toNat.toUInt8 && bytes[stop]! == ']'.toNat.toUInt8 do
    return #[]
  let whole := { start := if bytes[start - 2]! == 32 then start - 2 else start - 1, stop := stop + 1 }
  return (itemRanges list.getArgs whole).map fun (item, range) =>
    { kind := "fact", text := sub text item.start item.stop, range, line := lineNumber text item.start,
      whole := some whole }

partial def hasAtom (atom : String) (stx : Syntax) : Bool :=
  stx.isToken atom || stx.getArgs.any (hasAtom atom)

/-- The handlers of a `deriving` clause or command. Other files can use a public type's
instances, so only a private type's are the file's own. -/
def derivingPieces (text : String) (isPrivate : Bool) (stx : Syntax) : Array Piece := Id.run do
  let args := stx.getArgs
  unless args.size > 1 && args[0]!.isToken "deriving" do return #[]
  let some classes := args.find? fun arg =>
    arg.getKind == nullKind && arg.getNumArgs > 0 && arg[0].getKind == ``Lean.Parser.Command.derivingClass | return #[]
  let some r := range? stx | return #[]
  let bytes := text.toUTF8
  let mut start := r.start
  while start > 0 && (bytes[start - 1]! == 32 || bytes[start - 1]! == 10) do start := start - 1
  let command := args.any (·.isToken "instance")
  let whole := if command then { start := (lineOf text r.start).1, stop := (lineOf text r.stop).2 } else { start, stop := r.stop }
  let kind := if isPrivate && !command then "deriving" else "public deriving"
  return (itemRanges classes.getArgs whole).map fun (item, range) =>
    { kind, text := sub text item.start item.stop, range, line := lineNumber text item.start, replacements := #[""] }

partial def binderNames (stx : Syntax) : Array String :=
  let here :=
    if stx.getKind == ``Lean.Parser.Term.explicitBinder then stx[1].getArgs.filterMap fun name =>
      if name.isIdent then some name.getId.toString else none
    else #[]
  stx.getArgs.foldl (fun found arg => found ++ binderNames arg) here

/-- A `termination_by` with its `decreasing_by`, to replace by structural recursion on one of
the `binders`, or on the first argument after the colon. -/
def terminationPiece (text : String) (binders : Array String) (stx : Syntax) : Option Piece := do
  guard (stx.getKind == ``Lean.Parser.Termination.suffix)
  let r ← range? stx
  let source := sub text r.start r.stop
  guard (source.startsWith "termination_by" && (source.splitOn "structural").length == 1)
  let on := binders.map ("termination_by structural " ++ ·)
  some { kind := "termination", text := (source.takeWhile (· != '\n')).toString, range := r,
         line := lineNumber text r.start, replacements := on.push "termination_by structural x => x" }

partial def definitionPieces (text : String) (isPrivate : Bool) (binders : Array String) (stx : Syntax) : Array Piece :=
  let here := derivingPieces text isPrivate stx ++ (terminationPiece text binders stx).toArray
  stx.getArgs.foldl (fun found arg => found ++ definitionPieces text isPrivate binders arg) here

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

/-- Tactics tried in place of a step. Those the file's imports do not know are dropped on load. -/
def closers : Array String :=
  #["simp", "simp_all", "omega", "grind", "decide", "rfl", "trivial", "assumption", "contradiction",
    "aesop", "linarith", "nlinarith", "positivity", "norm_num", "ring", "tauto", "abel", "gcongr", "fun_prop"]

/-- Tactics that take the step's own `[...]` list. -/
def listTactics : Array String := #["simp", "simp only", "simp_all", "norm_num"]

def parses (env : Environment) (tactic : String) : Bool :=
  (Parser.runParserCategory env `tactic tactic).isOk

/-- The step's `[...]` list, if its text has one at the top level. -/
def listOf (text : String) : Option String := do
  let parts := text.splitOn "["
  guard (parts.length == 2)
  let inner := (parts[1]!.splitOn "]")
  guard (inner.length == 2 && blank inner[1]!)
  some ("[" ++ inner[0]! ++ "]")

def candidates (known : Array String) (text : String) : Array String :=
  let own := match listOf text with
    | some list => listTactics.map (· ++ " " ++ list)
    | none => #[]
  (own ++ known).filter (· != text)

partial def tacticInfos (ctx? : Option ContextInfo) : InfoTree → Array (ContextInfo × TacticInfo)
  | .context c t => tacticInfos (c.mergeIntoOuter? ctx?) t
  | .node info children =>
    let here := match ctx?, info with
      | some ctx, .ofTacticInfo ti => #[(ctx, ti)]
      | _, _ => #[]
    children.foldl (fun found child => found ++ tacticInfos ctx? child) here
  | .hole _ => #[]

def blockKinds : List Name :=
  [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeqBracketed, ``Lean.Parser.Term.byTactic]

partial def hasNested (stx : Syntax) : Bool :=
  blockKinds.contains stx.getKind || stx.getArgs.any hasNested

/-- A step is a tactic of the source, with no tactic block inside, that closes the first goal and
leaves the others. -/
def isStep (ti : TacticInfo) : Bool :=
  (ti.stx.getHeadInfo matches .original ..) && !ti.stx.isAtom && ti.stx.getKind != nullKind &&
    !hasNested ti.stx &&
    match ti.goalsBefore with
    | goal :: rest => ti.goalsAfter == rest && !ti.goalsAfter.contains goal
    | [] => false

def steps (text : String) (known : Array String) (trees : Array InfoTree) :
    Array Step × Array (ContextInfo × TacticInfo) := Id.run do
  let mut found : Array (Range × ContextInfo × TacticInfo) := #[]
  for tree in trees do
    for (ctx, ti) in tacticInfos none tree do
      let some range := range? ti.stx | continue
      if isStep ti && !found.any (·.1 == range) then found := found.push (range, ctx, ti)
  let sorted := found.qsort (·.1.start < ·.1.start)
  let step (range : Range) : Step :=
    let source := sub text range.start range.stop
    { text := source, range, line := lineNumber text range.start, candidates := candidates known source }
  return (sorted.map (step ·.1), sorted.map fun (_, ctx, ti) => (ctx, ti))

/-- The `simp?` form of a simp call that has no `only`, which makes Lean propose one that has. -/
def asking (text : String) : Option String := do
  let name ← ["simp_all", "simpa", "simp"].find? (text.startsWith ·)
  let rest := (text.drop name.length).toString
  guard (rest.isEmpty || rest.startsWith " " || rest.startsWith "[" || rest.startsWith "\n")
  guard ((rest.splitOn " only").length == 1)
  some (name ++ "?" ++ rest)

/-- The simp calls of the source that `simp?` can narrow. One that ran on several goals is left
out, since each goal may need other rules. -/
def simpCalls (text : String) (trees : Array InfoTree) : Array Step × Array (ContextInfo × TacticInfo) := Id.run do
  let mut found : Array (Range × ContextInfo × TacticInfo) := #[]
  let mut again : Array Range := #[]
  for tree in trees do
    for (ctx, ti) in tacticInfos none tree do
      let some range := range? ti.stx | continue
      unless (ti.stx.getHeadInfo matches .original ..) && !hasNested ti.stx do continue
      unless (asking (sub text range.start range.stop)).isSome do continue
      if found.any (·.1 == range) then again := again.push range else found := found.push (range, ctx, ti)
  let sorted := (found.filter (!again.contains ·.1)).qsort (·.1.start < ·.1.start)
  let call (range : Range) : Step :=
    { text := sub text range.start range.stop, range, line := lineNumber text range.start, candidates := #[] }
  return (sorted.map (call ·.1), sorted.map fun (_, ctx, ti) => (ctx, ti))

partial def hasBy (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.byTactic || stx.getArgs.any hasBy

partial def declName (stx : Syntax) : Option String :=
  if stx.getKind == ``Lean.Parser.Command.declId then some stx[0].getId.toString
  else stx.getArgs.findSome? declName

/-- Mathlib's `lemma` is a command of its own kind. -/
def isTheorem (stx : Syntax) : Bool :=
  (stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.theorem) ||
    stx.getKind.toString.endsWith "lemma"

/-- Search commands are only of use while writing. -/
def exploration : List String := ["#find", "#loogle", "#leansearch", "#moogle", "#help"]

/-- These compute or check something, and may be meant as tests. -/
def tests : List String :=
  ["#eval", "#reduce", "#guard", "#guard_msgs", "#guard_expr", "#lint", "#test", "#assert_no_sorry", "#norm_num",
    "#simp", "#check_failure"]

partial def firstAtom (stx : Syntax) : Option String :=
  match stx with
  | .atom _ value => some value
  | .node _ _ args => args.findSome? firstAtom
  | _ => none

/-- A `#` command, with the whole lines it fills. -/
def diagnostic? (text : String) (stx : Syntax) (ms : Nat) : Option Diagnostic := do
  let name ← firstAtom stx
  guard (name.startsWith "#")
  let r ← range? stx
  let (first, _) := lineOf text r.start
  let (_, next) := lineOf text r.stop
  let whole := blank (sub text first r.start) && blank (sub text r.stop next)
  let category := if exploration.contains name then "exploration" else if tests.contains name then "test" else "noise"
  some { name, text := ((sub text r.start r.stop).takeWhile (· != '\n')).toString, category,
         range := if whole then { start := first, stop := next } else r, line := lineNumber text r.start, ms }

/-- `theorem`, `def` or `instance` for a declaration, also under `open ... in`, else the
command's own name, like `open`. -/
partial def commandKind (stx : Syntax) : String :=
  if stx.getKind == ``Lean.Parser.Command.in then commandKind stx[2] else
  let kind := if stx.getKind == ``Lean.Parser.Command.declaration then stx[1].getKind else stx.getKind
  match kind with
  | .str _ last => last
  | _ => kind.toString

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
  let run := ((Command.elabCommandTopLevel stx).run context).run { state with messages }
  match ← (EIO.toIO' run) with
  | .ok (_, state') => return (stx, state', parser')
  | .error e => throw <| IO.userError (← e.toMessageData.toString)

/-- The imports as one declaration, each import line a piece. A plain import of a `module` file
is private, so the file alone shows whether it can go. -/
def imports (file text : String) (stop : Nat) : Loaded := Id.run do
  let lines := (sub text 0 stop).splitOn "\n"
  let isModule := lines.any (·.trimAscii.toString == "module")
  let mut pieces := #[]
  let mut start := 0
  let mut number := 1
  for line in lines do
    let next := start + line.utf8ByteSize + 1
    let words := (line.splitOn " ").filter (· != "")
    if words.contains "import" && (words.head? == some "import" || words.head? == some "public" || words.head? == some "meta") then
      let own := isModule && words.head? != some "public"
      pieces := pieces.push
        { kind := if own then "import" else "public import", text := line, range := { start, stop := min next text.utf8ByteSize },
          line := number : Piece }
    start := next
    number := number + 1
  let decl : Decl :=
    { key := s!"{file}:imports", name := "imports", kind := "imports", range := { start := 0, stop := text.utf8ByteSize },
      line := 1, ok := true, steps := #[], simps := #[], pieces }
  return { decl, before := none, goals := #[] }

/-- Check a whole file's text. Returns its first error. -/
def checkFile (options : Options) (file source : String) (cancel : IO.CancelToken) : IO (Option String) := do
  unsafe Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext source file
  let (header, parser, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
  if let some error ← failure? messages then return some error
  let mut state := Command.mkState env {} options
  let mut parser := parser
  repeat
    let (stx, state', parser') ← step inputCtx state parser (some cancel)
    for message in state'.messages.toList do
      if message.severity matches .error then return some (← message.data.toString)
    state := { state' with messages := {}, infoState := { enabled := false } }
    parser := parser'
    if Parser.isTerminalCommand stx then break
  return none

/-- Run `x` in `env`, with the namespace and options of `scope`. -/
def runMeta (env : Environment) (scope : Command.Scope) (cancel : Option IO.CancelToken) (x : MetaM α) : IO α := do
  let core : CoreM α := (·.1) <$> x.run {} {}
  let (result, _) ← (withOptions (fun _ => scope.opts) core).toIO
    { currNamespace := scope.currNamespace, openDecls := scope.openDecls, fileName := "<xlint>", fileMap := default,
      cancelTk? := cancel }
    { env := env.setExporting false }
  return result

def constantOf (env : Environment) (scope : Command.Scope) (stx : Syntax) : Name := Id.run do
  let some id := declName stx | return .anonymous
  let found := ResolveName.resolveGlobalName env scope.opts scope.currNamespace scope.openDecls id.toName
  return (found.findSome? fun (n, fields) => if fields.isEmpty && env.contains n then some n else none).getD .anonymous

/-- In `h : A ⊢ False` the last binder is what the theorem refutes, so it is no premise. -/
def premises (xs : Array Expr) (body : Expr) : Array Expr :=
  if body.isConstOf ``False then xs.pop else xs

/-- `vacuous` for a theorem with hypotheses; `always` and `never` for a `Prop` or `Bool` function. -/
def probesOf (isTheorem : Bool) (c : ConstantInfo) : MetaM (Array String) :=
  Meta.forallTelescope c.type fun xs body => do
    if isTheorem then
      let hyps ← (premises xs body).filterM fun x => do Meta.isProp (← Meta.inferType x)
      return if hyps.isEmpty then #[] else #["vacuous"]
    if !xs.isEmpty && (body.isProp || body.isConstOf ``Bool) then return #["always", "never"]
    return #[]

/-- `vacuous`: the hypotheses imply `False`. `always`, `never`: the unfolded predicate holds for
every input, or for none. -/
def probeGoal (claim : String) (c : ConstantInfo) : MetaM Expr :=
  Meta.forallTelescope c.type fun xs body => do
    if claim == "vacuous" then return ← Meta.mkForallFVars (premises xs body) (mkConst ``False)
    let app := mkAppN (mkConst c.name (c.levelParams.map Level.param)) xs
    let app := (← Meta.unfoldDefinition? app).getD app
    let holds ← if body.isProp then pure app else Meta.mkEq app (mkConst ``Bool.true)
    Meta.mkForallFVars xs (if claim == "always" then holds else mkNot holds)

def probesFor (env : Environment) (scope : Command.Scope) (const : Name) (isTheorem : Bool) : IO (Array String) := do
  let some c := env.find? const | return #[]
  try runMeta env scope none (probesOf isTheorem c) catch _ => return #[]

def load (options : Options) (file : String) : IO State := do
  let text ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext text file
  let (header, parser, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
  if messages.hasErrors then
    let errors ← messages.toList.mapM (·.data.toString)
    throw <| IO.userError s!"{file}: cannot process the imports: {" ".intercalate errors}"
  let mut state := Command.mkState env {} options
  let mut parser := parser
  let mut loaded := #[imports file text parser.pos.byteIdx]
  let mut known : Option (Array String) := none
  let mut diagnostics := #[]
  let mut commands := #[]
  repeat
    let before := state
    let start ← IO.monoMsNow
    let (stx, state', parser') ← step inputCtx state parser
    let ms := (← IO.monoMsNow) - start
    let scope := state'.scopes.head!
    if let some found := diagnostic? text stx ms then diagnostics := diagnostics.push found
    if let (some range, false) := (range? stx, Parser.isTerminalCommand stx) then
      let head := ((sub text range.start range.stop).takeWhile (· != '\n')).toString
      commands := commands.push { kind := commandKind stx, text := head, range, ms }
    state := { state' with messages := {}, infoState := { enabled := true } }
    parser := parser'
    if isTheorem stx && hasBy stx then
      if let some range := range? stx then
        let ok := (← failure? state'.messages).isNone
        if known.isNone then known := some (closers.filter (parses state'.env))
        let trees := state'.infoState.trees.toArray
        let (steps, goals) := steps text (known.getD #[]) trees
        let (simps, simpGoals) := simpCalls text trees
        let const := constantOf state'.env scope stx
        let decl : Decl :=
          { key := s!"{file}:{range.start}", name := (declName stx).getD "", kind := "theorem", range, line := lineNumber text range.start,
            ok, steps, simps, pieces := pieces text stx, probes := ← probesFor state'.env scope const true }
        loaded := loaded.push { decl, before := some before, goals, simpGoals, const, after := some state'.env }
    else if let some range := range? stx then
      let found := definitionPieces text (hasAtom "private" stx[0]) (binderNames stx) stx
      let const := constantOf state'.env scope stx
      let probes ← if commandKind stx == "definition" then probesFor state'.env scope const false else pure #[]
      unless found.isEmpty && probes.isEmpty do
        let decl : Decl :=
          { key := s!"{file}:{range.start}", name := (declName stx).getD "", kind := "definition", range,
            line := lineNumber text range.start, ok := (← failure? state'.messages).isNone, steps := #[], simps := #[],
            pieces := found, probes }
        loaded := loaded.push { decl, before := some before, goals := #[], const, after := some state'.env }
    if Parser.isTerminalCommand stx then break
  return { options, file, text, loaded, diagnostics, commands }

def applyEdits (text : String) (range : Range) (edits : Array Edit) : String := Id.run do
  let sorted := edits.qsort (·.range.start > ·.range.start)
  let mut stop := range.stop
  let mut out := ""
  for edit in sorted do
    out := edit.text ++ sub text edit.range.stop stop ++ out
    stop := edit.range.start
  return sub text range.start stop ++ out

/-- Run `x` with a token that is set after `timeoutMs`. Returns whether it was set, and the ms. -/
def timed (timeoutMs : Nat) (x : IO.CancelToken → IO α) : IO (Bool × Nat × Except IO.Error α) := do
  let cancel ← IO.CancelToken.new
  let finished ← IO.mkRef false
  let _timer ← IO.asTask (prio := .dedicated) do
    let mut waited := 0
    while waited < timeoutMs && !(← finished.get) do
      IO.sleep 5
      waited := waited + 5
    unless ← finished.get do cancel.set
  let start ← IO.monoMsNow
  let result ← (x cancel).toBaseIO
  let ms := (← IO.monoMsNow) - start
  finished.set true
  return (← cancel.isSet, ms, result)

/-- Check the theorem once with the edits. Returns the verdict and the wall-clock ms. -/
def runOnce (state : State) (l : Loaded) (edits : Array Edit) (timeoutMs : Nat) : IO (String × Nat × String) := do
  let source := applyEdits state.text l.decl.range edits
  let some before := l.before
    | let (late, ms, result) ← timed timeoutMs (checkFile state.options state.file source)
      if late then return ("timeout", ms, "")
      match result with
      | .ok none => return ("closes", ms, "")
      | .ok (some error) => return ("fails", ms, error)
      | .error e => return ("fails", ms, toString e)
  let inputCtx := Parser.mkInputContext source state.file
  let (late, ms, result) ← timed timeoutMs fun cancel =>
    step inputCtx { before with messages := {} } {} (some cancel)
  if late then return ("timeout", ms, "")
  match result with
  | .error e => return ("fails", ms, toString e)
  | .ok (_, after, parser) =>
    if !blank (sub source parser.pos.byteIdx source.utf8ByteSize) then
      return ("fails", ms, "the edited text is more than one command")
    match ← failure? after.messages with
    | some message => return ("fails", ms, message)
    | none => return ("closes", ms, "")

/-- The rules under "tried theorems" in simp's diagnostics, as `name ↦ tried, succeeded: used`. -/
def triedRules (message : String) : Array Rule := Id.run do
  let mut found := #[]
  let mut tried := false
  for line in message.splitOn "\n" do
    if line.contains "theorems" && line.trimAsciiEnd.toString.endsWith ":" then
      tried := (line.splitOn "[simp] tried theorems").length == 2
    else if tried then
      if let [head, counts] := line.splitOn " ↦ " then
        let name := (head.splitOn "[simp] ").getLast!
        let number (s : String) : Nat := (s.takeWhile Char.isDigit).toString.toNat!
        let used := match counts.splitOn "succeeded: " with
          | [_, n] => number n
          | _ => 0
        found := found.push { name, tried := number counts, used }
  return found

/-- Check the theorem as written with simp's diagnostics on, and add up its counts per rule. -/
def ruleStats (state : State) (l : Loaded) (timeoutMs : Nat) : IO (String × Nat × Array Rule) := do
  let some before := l.before | return ("error", 0, #[])
  let counting (scope : Command.Scope) : Command.Scope :=
    { scope with opts := pp.fullNames.set (diagnostics.threshold.set (diagnostics.set scope.opts true) 0) true }
  let scopes := match before.scopes with
    | scope :: rest => counting scope :: rest
    | [] => []
  let source := sub state.text l.decl.range.start l.decl.range.stop
  let inputCtx := Parser.mkInputContext source state.file
  let (late, ms, result) ← timed timeoutMs fun cancel =>
    step inputCtx { before with messages := {}, scopes } {} (some cancel)
  if late then return ("timeout", ms, #[])
  let .ok (_, after, _) := result | return ("fails", ms, #[])
  let mut totals : Std.HashMap String Rule := {}
  for message in after.messages.toList do
    for rule in triedRules (← message.data.toString) do
      let sum := match totals[rule.name]? with
        | some r => { r with tried := r.tried + rule.tried, used := r.used + rule.used }
        | none => rule
      totals := totals.insert rule.name sum
  let verdict := if (← failure? after.messages).isNone then "closes" else "fails"
  return (verdict, ms, totals.toArray.map (·.2) |>.qsort (·.name < ·.name))

/-- Run `tactic` on the goal before a step. Returns the ms, the messages it wrote and the verdict,
which is `open` if goals are left. -/
def tacticOnce (ctx : ContextInfo) (ti : TacticInfo) (tactic : String) (timeoutMs : Nat) :
    IO (String × Nat × Array String) := do
  let .ok stx := Parser.runParserCategory ctx.env `tactic tactic | return ("fails", 0, #["does not parse"])
  let some goal := ti.goalsBefore.head? | return ("fails", 0, #["no goal"])
  let run : MetaM (String × Array String) := do
    let left ← (Term.withSynthesize (Tactic.run goal (Tactic.evalTactic stx))).run'
    let proof ← instantiateMVars (mkMVar goal)
    let messages := (← getThe Core.State).messages
    let texts ← messages.toList.toArray.mapM (·.data.toString)
    let verdict :=
      if messages.hasErrors || proof.hasSorry then "fails"
      else if left.isEmpty && !proof.hasExprMVar then "closes"
      else "open"
    return (verdict, texts)
  let core (cancel : IO.CancelToken) : IO (String × Array String) := do
    let x : CoreM (String × Array String) := (·.1) <$> run.run { lctx := {} } { mctx := ti.mctxBefore }
    let (result, _) ← (withOptions (fun _ => ctx.options) x).toIO
      { currNamespace := ctx.currNamespace, openDecls := ctx.openDecls, fileName := "<xlint>", fileMap := default,
        cancelTk? := some cancel }
      { env := ctx.env.setExporting false, ngen := ctx.ngen }
    return result
  let (late, ms, result) ← timed timeoutMs core
  if late then return ("timeout", ms, #[])
  match result with
  | .error e => return ("fails", ms, #[toString e])
  | .ok (verdict, messages) => return (verdict, ms, messages)

/-- The tactics Lean itself proposes for a step, from the `Try this` messages of `simp?`. -/
def suggest (ctx : ContextInfo) (ti : TacticInfo) (text : String) (timeoutMs : Nat) (mayLeaveGoals := false) :
    IO (Array String) := do
  let some asked := asking text | return #[]
  let (verdict, _, messages) ← tacticOnce ctx ti asked timeoutMs
  unless verdict == "closes" || (mayLeaveGoals && verdict == "open") do return #[]
  let mut found := #[]
  for message in messages do
    if let [_, proposal] := message.splitOn "Try this:" then
      let proposal := (proposal.splitOn "[apply]").getLast!
      let words := (proposal.split Char.isWhitespace).toList.map toString |>.filter (· != "")
      found := found.push (" ".intercalate words)
  return found

/-- Run `tactic` on the goal of a probe. `closes` means the claim holds. -/
def probeOnce (l : Loaded) (claim tactic : String) (timeoutMs : Nat) : IO (String × Nat × String) := do
  let (some env, some before) := (l.after, l.before) | return ("error", 0, "no environment")
  let some c := env.find? l.const | return ("error", 0, "no constant")
  let .ok stx := Parser.runParserCategory env `tactic tactic | return ("fails", 0, "does not parse")
  let run : MetaM (String × String) := do
    let goal ← Meta.mkFreshExprMVar (← probeGoal claim c)
    let left ← (Term.withSynthesize (Tactic.run goal.mvarId! (Tactic.evalTactic stx))).run'
    let proof ← instantiateMVars goal
    if (← getThe Core.State).messages.hasErrors || proof.hasSorry then return ("fails", "")
    if left.isEmpty && !proof.hasExprMVar then return ("closes", "")
    return ("open", "")
  let (late, ms, result) ← timed timeoutMs fun cancel => runMeta env before.scopes.head! (some cancel) run
  if late then return ("timeout", ms, "")
  match result with
  | .ok (verdict, message) => return (verdict, ms, message)
  | .error e => return ("fails", ms, toString e)

def answer (state : State) (question : Json) : IO Json := do
  let key := (question.getObjValAs? String "key").toOption.getD ""
  let reply (verdict : String) (ms : Array Nat) (message : String) : Json :=
    Json.mkObj [("response", "answer"), ("answer", Json.mkObj
      [("key", key), ("verdict", verdict), ("ms", toJson ms), ("message", message)])]
  let decl := (question.getObjValAs? String "decl").toOption.getD ""
  let some l := state.loaded.find? (·.decl.key == decl) | return reply "error" #[] s!"no declaration {decl}"
  let timeout := (question.getObjValAs? Nat "timeout_ms").toOption.getD 30000
  let runs := (question.getObjValAs? Nat "runs").toOption.getD 1
  let what := (question.getObjValAs? String "do").toOption.getD ""
  let goal? := (question.getObjValAs? Nat "step").toOption.bind (l.goals[·]?)
  let once : IO (String × Nat × String) :=
    match what, goal? with
    | "run", _ => do runOnce state l (← IO.ofExcept (question.getObjValAs? (Array Edit) "edits")) timeout
    | "probe", _ => do
      probeOnce l (← IO.ofExcept (question.getObjValAs? String "claim")) (← IO.ofExcept (question.getObjValAs? String "tactic")) timeout
    | "step", some (ctx, ti) => do
      let text ← IO.ofExcept (question.getObjValAs? String "text")
      let (verdict, ms, messages) ← tacticOnce ctx ti text timeout
      return (verdict, ms, if verdict == "closes" then "" else " ".intercalate messages.toList)
    | _, _ => return ("error", 0, s!"cannot {what}")
  if what == "suggest" || what == "narrow" then
    let index := (question.getObjValAs? Nat (if what == "narrow" then "call" else "step")).toOption.getD 0
    let (goals, texts) := if what == "narrow" then (l.simpGoals, l.decl.simps) else (l.goals, l.decl.steps)
    let (some (ctx, ti), some step) := (goals[index]?, texts[index]?) | return reply "error" #[] "no such step"
    let found ← suggest ctx ti step.text timeout (mayLeaveGoals := what == "narrow")
    return Json.mkObj [("response", "answer"), ("answer", Json.mkObj
      [("key", key), ("verdict", "closes"), ("ms", toJson (#[] : Array Nat)), ("message", ""),
        ("suggestions", toJson found)])]
  if what == "stats" then
    let (verdict, ms, rules) ← ruleStats state l timeout
    return Json.mkObj [("response", "answer"), ("answer", Json.mkObj
      [("key", key), ("verdict", verdict), ("ms", toJson #[ms]), ("message", ""), ("rules", toJson rules)])]
  let mut times := #[]
  for _ in [0:max runs 1] do
    let (verdict, ms, message) ← once
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
    state.set (← load (← state.get).options file)
    let loaded ← state.get
    return Json.mkObj [("response", "loaded"), ("decls", toJson (loaded.loaded.map (·.decl))),
      ("diagnostics", toJson loaded.diagnostics), ("commands", toJson loaded.commands)]
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

/-- Read `-Dname=value` arguments as `lean` does. -/
def parseOptions (args : List String) : IO Options :=
  args.foldlM (init := {}) fun options arg => do
    let key :: value :: rest := arg.splitOn "=" | throw <| .userError s!"expected -Dname=value, got {arg}"
    unless key.startsWith "-D" do throw <| .userError s!"expected -Dname=value, got {arg}"
    let name := (String.ofList (key.toList.drop 2)).toName
    let some decl := (← getOptionDecls).find? name | throw <| .userError s!"unknown option {name}"
    Language.Lean.setOption options decl name ("=".intercalate (value :: rest))

end Xlint

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  Xlint.serve (← IO.mkRef { options := ← Xlint.parseOptions args })
