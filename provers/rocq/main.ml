(* The Rocq server of xlint. It keeps the state before every sentence, so a question starts at
   its lemma. Offsets are bytes into the file. *)

let sub text start stop = String.sub text start (stop - start)

let is_blank c = c = ' ' || c = '\n' || c = '\t' || c = '\r'

let is_bullet c = c = '-' || c = '+' || c = '*'

let first_word sentence =
  let stop = ref 0 in
  let n = String.length sentence in
  while !stop < n && (match sentence.[!stop] with 'A' .. 'Z' | 'a' .. 'z' | '_' -> true | _ -> false) do incr stop done;
  String.sub sentence 0 !stop

let closes_proof word = List.mem word [ "Qed"; "Defined"; "Admitted"; "Abort"; "Save" ]

(* Commands that only print. A search is of use while writing a proof, a computation may be a test. *)
let exploration = [ "Search"; "SearchPattern"; "SearchRewrite"; "About"; "Locate"; "Check"; "Print"; "Show" ]

let tests = [ "Compute"; "Eval"; "Fail" ]

(* Tried in place of a closing step. One that needs a library the file lacks just fails. *)
let closers =
  [ "auto"; "eauto"; "easy"; "trivial"; "reflexivity"; "assumption"; "congruence"; "tauto"; "intuition";
    "firstorder"; "lia"; "nia"; "now auto" ]

(* running Rocq *)

let error_text = function Failure message -> message | e -> Pp.string_of_ppcmds (CErrors.iprint (Exninfo.capture e))

let depth (st : Vernacstate.t) =
  match st.interp.lemmas with
  | None -> 0
  | Some stack -> List.length (Vernacstate.LemmaStack.get_all_proof_names stack)

(* Goals of the innermost proof, with those a focus set aside and the shelved ones. *)
let open_goals (st : Vernacstate.t) =
  match st.interp.lemmas with
  | None -> 0
  | Some stack ->
    Vernacstate.LemmaStack.with_top stack ~f:(fun proof ->
        let Proof.{ goals; stack; sigma; _ } = Proof.data (Declare.Proof.get proof) in
        List.length goals + List.length (Evd.shelf sigma)
        + List.fold_left (fun n (left, right) -> n + List.length left + List.length right) 0 stack)

(* The next sentence of the stream, parsed in the state `st`, which must be the current one. *)
let parse (st : Vernacstate.t) stream =
  let mode = Option.map (fun _ -> Synterp.get_default_proof_mode ()) st.interp.lemmas in
  Procq.Entry.parse (Pvernac.main_entry mode) stream

let interp st command = Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st command

(* Run every sentence of `text` from `st`. `each` sees a sentence's range in `text` and the states
   around it, and says whether to go on. Returns the last state. *)
let run_text st text each =
  Vernacstate.unfreeze_full_state st;
  let stream = Procq.Parsable.make (Gramlib.Stream.of_string text) in
  let rec go st =
    match parse st stream with
    | None -> st
    | Some command ->
      let loc = Option.get command.CAst.loc in
      let after = interp st command in
      if each (loc.Loc.bp, loc.Loc.ep) st after then go after else after
  in
  go st

(* the loaded file *)

type sentence = {
  start : int;
  stop : int;
  before : Vernacstate.t;
  ms : int;
  goals : int;  (* open goals after it *)
}

type step = { sentence : int; from : int; till : int }

type decl = {
  key : string;
  name : string;
  kind : string;
  first : int;  (* index of its statement in the sentences *)
  last : int;
  ok : bool;
  steps : step list;
  pieces : Yojson.Safe.t list;
}

type loaded = { file : string; text : string; sentences : sentence array; decls : decl list }

let line_number text pos =
  let n = ref 1 in
  String.iteri (fun i c -> if i < pos && c = '\n' then incr n) text;
  !n

let range start stop = `Assoc [ ("start", `Int start); ("stop", `Int stop) ]

let first_line source = List.hd (String.split_on_char '\n' source)

(* The lines of a range that fills them, else the range. *)
let with_lines text start stop =
  let line_start = try String.rindex_from text (max 0 (start - 1)) '\n' + 1 with Not_found -> 0 in
  let line_stop = try String.index_from text stop '\n' + 1 with Not_found -> String.length text in
  let blank a b = String.for_all is_blank (sub text a b) in
  if (start = 0 || blank line_start start) && blank stop line_stop then (line_start, line_stop) else (start, stop)

let piece_json text kind start stop (from, till) =
  `Assoc
    [ ("kind", `String kind); ("text", `String (first_line (sub text start stop))); ("range", range from till);
      ("line", `Int (line_number text start)) ]

let tactic_piece text (s : sentence) =
  let word = first_word (sub text s.start s.stop) in
  let kind = if List.mem word [ "assert"; "pose"; "have"; "enough"; "specialize" ] then "have" else "tactic" in
  piece_json text kind s.start s.stop (with_lines text s.start s.stop)

let is_diagnostic text (s : sentence) =
  let word = first_word (sub text s.start s.stop) in
  List.mem word exploration || List.mem word tests

let is_tactic text (s : sentence) =
  let c = text.[s.start] in
  let word = first_word (sub text s.start s.stop) in
  not (c = '{' || c = '}' || is_bullet c || word = "Proof" || closes_proof word || is_diagnostic text s)

(* The first `word` of [from, till) that stands alone outside brackets, as its offset. *)
let find_word text word from till =
  let n = String.length word in
  let is_name c = match c with 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' | '.' -> true | _ -> false in
  let rec scan i depth =
    if i + n > till then None
    else
      match text.[i] with
      | '(' | '[' | '{' -> scan (i + 1) (depth + 1)
      | ')' | ']' | '}' -> scan (i + 1) (depth - 1)
      | _ when depth = 0 && sub text i (i + n) = word && (i = from || not (is_name text.[i - 1]))
               && (i + n = till || not (is_name text.[i + n])) -> Some i
      | _ -> scan (i + 1) depth
  in
  scan from 0

(* The items of [from, till), split at `separator` outside brackets, each trimmed. *)
let items text separator from till =
  let trim (a, b) =
    let a = ref a and b = ref b in
    while !a < !b && is_blank text.[!a] do incr a done;
    while !b > !a && is_blank text.[!b - 1] do decr b done;
    (!a, !b)
  in
  let rec scan i depth start found =
    if i >= till then List.rev (trim (start, till) :: found)
    else
      match text.[i] with
      | '(' | '[' | '{' -> scan (i + 1) (depth + 1) start found
      | ')' | ']' | '}' -> scan (i + 1) (depth - 1) start found
      | c when depth = 0 && (c = separator || (separator = ' ' && is_blank c)) ->
        scan (i + 1) depth (i + 1) (trim (start, i) :: found)
      | _ -> scan (i + 1) depth start found
  in
  List.filter (fun (a, b) -> a < b) (scan from 0 from [])

(* Deleting an item removes it up to the next one, or `whole` if it is the only one. With
   `together` a longer list is a piece too, as its items cannot all go one by one. *)
let item_pieces ?(together = true) text kind found whole =
  let all = Array.of_list found in
  let n = Array.length all in
  let each =
    List.mapi
      (fun i (a, b) ->
        let removed = if n = 1 then whole else if i + 1 < n then (a, fst all.(i + 1)) else (snd all.(i - 1), b) in
        piece_json text kind a b removed)
      found
  in
  if together && n > 1 then piece_json text kind (fst all.(0)) (snd all.(n - 1)) whole :: each else each

(* The lemmas after `using`, the hint databases after `with` and the rewrite rules of a
   sentence that is one tactic. *)
let fact_pieces text (s : sentence) =
  let stop = s.stop - 1 in
  let word = first_word (sub text s.start stop) in
  let plain = find_word text ";" s.start stop = None && find_word text "by" s.start stop = None in
  if not plain then []
  else if List.mem word [ "auto"; "eauto"; "trivial" ] then begin
    let list keyword at till =
      let found = items text (if keyword = "using" then ',' else ' ') (at + String.length keyword) till in
      let from = if at > s.start && text.[at - 1] = ' ' then at - 1 else at in
      item_pieces text (if keyword = "using" then "fact" else "hint database") found (from, till)
    in
    match (find_word text "using" s.start stop, find_word text "with" s.start stop) with
    | Some u, Some w when u < w -> list "using" u w @ list "with" w stop
    | Some u, None -> list "using" u stop
    | None, Some w -> list "with" w stop
    | _ -> []
  end
  else if word = "rewrite" && find_word text "in" s.start stop = None then begin
    let found = items text ',' (s.start + String.length word) stop in
    if List.length found < 2 then [] else item_pieces ~together:false text "fact" found (s.start, s.stop)
  end
  else []

(* Each module of a `Require Import`, which goes with its sentence if it is the only one. A
   `Require Export` reaches the files that import this one, so it is only reported. *)
let import_pieces text (s : sentence) =
  let stop = s.stop - 1 in
  match find_word text "Require" s.start stop with
  | None -> []
  | Some require -> (
    let after = require + String.length "Require" in
    let keyword word = Option.map (fun at -> (word, at)) (find_word text word after stop) in
    match List.find_map keyword [ "Import"; "Export" ] with
    | None -> []
    | Some (word, at) ->
      let kind = if word = "Import" then "import" else "public import" in
      item_pieces text kind (items text ' ' (at + String.length word) stop) (with_lines text s.start s.stop))

let diagnostic_json text (s : sentence) =
  let source = sub text s.start s.stop in
  let name = first_word source in
  let from, till = with_lines text s.start s.stop in
  `Assoc
    [ ("name", `String name); ("text", `String (first_line source));
      ("category", `String (if List.mem name exploration then "exploration" else "test")); ("range", range from till);
      ("line", `Int (line_number text s.start)); ("ms", `Int s.ms) ]

let load initial file =
  let text = In_channel.with_open_bin file In_channel.input_all in
  let sentences = ref [] in
  let time = ref (Unix.gettimeofday ()) in
  let each (start, stop) before after =
    let now = Unix.gettimeofday () in
    sentences := { start; stop; before; ms = int_of_float ((now -. !time) *. 1000.); goals = open_goals after } :: !sentences;
    time := now;
    true
  in
  let final =
    try run_text initial text each
    with e ->
      let at = match !sentences with s :: _ -> s.stop | [] -> 0 in
      failwith (Printf.sprintf "%s: after line %d: %s" file (line_number text at) (error_text e))
  in
  let sentences = Array.of_list (List.rev !sentences) in
  let count = Array.length sentences in
  let after i = if i + 1 < count then sentences.(i + 1).before else final in
  let goals_before i = if i = 0 then 0 else sentences.(i - 1).goals in
  let decls = ref [] in
  let opened = ref None in
  Array.iteri
    (fun i (s : sentence) ->
      match !opened with
      | None when depth s.before = 0 && depth (after i) > 0 ->
        let names = Vernacstate.LemmaStack.get_all_proof_names (Option.get (after i).interp.lemmas) in
        opened := Some (i, Names.Id.to_string (List.hd names))
      | Some (first, name) when depth (after i) = 0 ->
        let body = List.init (i - first - 1) (fun k -> first + 1 + k) in
        let tactics = List.filter (fun k -> is_tactic text sentences.(k)) body in
        let closing k =
          let s = sentences.(k) in
          if s.goals < goals_before k then Some { sentence = k; from = s.start; till = s.stop - 1 } else None
        in
        let pieces k = tactic_piece text sentences.(k) :: fact_pieces text sentences.(k) in
        decls :=
          { key = Printf.sprintf "%s:%d" file sentences.(first).start; name; kind = "theorem"; first; last = i;
            ok = first_word (sub text s.start s.stop) = "Qed"; steps = List.filter_map closing tactics;
            pieces = List.concat_map pieces tactics }
          :: !decls;
        opened := None
      | _ -> ())
    sentences;
  let imports =
    { key = file ^ ":imports"; name = "imports"; kind = "imports"; first = 0; last = count - 1; ok = count > 0;
      steps = []; pieces = List.concat_map (import_pieces text) (Array.to_list sentences) }
  in
  { file; text; sentences; decls = imports :: List.rev !decls }

let apply_edits text start stop edits =
  let latest_first = List.sort (fun (a, _, _) (b, _, _) -> compare b a) edits in
  let out, upto =
    List.fold_left
      (fun (out, upto) (from, till, replacement) -> (replacement ^ sub text till upto ^ out, from))
      ("", stop) latest_first
  in
  sub text start upto ^ out

(* `run` under a time limit, as its verdict, the ms it took and its message. *)
let timed timeout_ms run =
  let start = Unix.gettimeofday () in
  let verdict, message =
    match Control.timeout (float_of_int timeout_ms /. 1000.) run () with
    | Ok result -> result
    | Error _ -> ("timeout", "")
    | exception e -> ("fails", error_text e)
  in
  (verdict, int_of_float ((Unix.gettimeofday () -. start) *. 1000.), message)

(* Check the declaration once with the edits, from the state before it. The imports are the
   whole file. *)
let run_once loaded decl edits timeout_ms =
  let whole = decl.kind = "imports" in
  let first, last = (loaded.sentences.(decl.first), loaded.sentences.(decl.last)) in
  let start, stop = if whole then (0, String.length loaded.text) else (first.start, last.stop) in
  let source = apply_edits loaded.text start stop edits in
  let outside = depth first.before in
  timed timeout_ms (fun () ->
      let closed = ref false in
      let extra = ref false in
      let each _ _ after =
        if !closed then extra := true;
        if (not whole) && depth after = outside then closed := true;
        not !extra
      in
      let final = run_text first.before source each in
      if !extra then ("fails", "the edited text is more than one lemma")
      else if depth final <> outside then ("fails", "the proof is not finished")
      else ("closes", ""))

(* Run `text` in place of the step. It must leave as many goals as the step does. *)
let step_once loaded step text timeout_ms =
  let s = loaded.sentences.(step.sentence) in
  timed timeout_ms (fun () ->
      let count = ref 0 in
      let final = run_text s.before (text ^ ".") (fun _ _ _ -> incr count; true) in
      if !count <> 1 then ("fails", "not one tactic")
      else if open_goals final <> s.goals then ("fails", "it leaves other goals")
      else ("closes", ""))

(* the protocol *)

let step_json loaded step =
  `Assoc
    [ ("text", `String (sub loaded.text step.from step.till)); ("range", range step.from step.till);
      ("line", `Int (line_number loaded.text step.from)); ("candidates", `List (List.map (fun c -> `String c) closers)) ]

let decl_json loaded decl =
  let start, stop =
    if decl.kind = "imports" then (0, String.length loaded.text)
    else (loaded.sentences.(decl.first).start, loaded.sentences.(decl.last).stop)
  in
  `Assoc
    [ ("key", `String decl.key); ("name", `String decl.name); ("kind", `String decl.kind); ("range", range start stop);
      ("line", `Int (line_number loaded.text start)); ("ok", `Bool decl.ok);
      ("steps", `List (List.map (step_json loaded) decl.steps)); ("simps", `List []); ("pieces", `List decl.pieces) ]

let command_json loaded (s : sentence) =
  let source = sub loaded.text s.start s.stop in
  let word = first_word source in
  `Assoc
    [ ("kind", `String (if word = "" then "bullet" else word)); ("text", `String (first_line source));
      ("range", range s.start s.stop);
      ("ms", `Int s.ms) ]

let answer loaded question =
  let open Yojson.Safe.Util in
  let key = to_string (member "key" question) in
  let reply verdict ms message =
    `Assoc
      [ ("response", `String "answer");
        ("answer",
         `Assoc
           [ ("key", `String key); ("verdict", `String verdict); ("ms", `List (List.map (fun ms -> `Int ms) ms));
             ("message", `String message) ]) ]
  in
  let timeout = to_int (member "timeout_ms" question) in
  let rec repeat left times once =
    if left = 0 then reply "closes" (List.rev times) ""
    else
      match once () with
      | "closes", ms, _ -> repeat (left - 1) (ms :: times) once
      | verdict, ms, message -> reply verdict [ ms ] message
  in
  let runs = max 1 (to_int (member "runs" question)) in
  match List.find_opt (fun d -> d.key = to_string (member "decl" question)) loaded.decls with
  | None -> reply "error" [] "no such declaration"
  | Some decl -> (
    match to_string (member "do" question) with
    | "run" ->
      let edits =
        List.map
          (fun edit ->
            let range = member "range" edit in
            (to_int (member "start" range), to_int (member "stop" range), to_string (member "text" edit)))
          (to_list (member "edits" question))
      in
      repeat runs [] (fun () -> run_once loaded decl edits timeout)
    | "step" -> (
      match List.nth_opt decl.steps (to_int (member "step" question)) with
      | None -> reply "error" [] "no such step"
      | Some step -> repeat runs [] (fun () -> step_once loaded step (to_string (member "text" question)) timeout))
    | "suggest" -> reply "closes" [] ""
    | _ -> reply "error" [] "the Rocq server has no simplifier questions")

let respond initial state request =
  let open Yojson.Safe.Util in
  match to_string (member "request" request) with
  | "hello" ->
    `Assoc
      [ ("response", `String "hello");
        ("hello",
         `Assoc
           [ ("prover", `String "rocq"); ("version", `String ("The Rocq Prover, version " ^ Coq_config.version));
             ("closers", `List (List.map (fun c -> `String c) closers)) ]) ]
  | "load" ->
    let loaded = load (Lazy.force initial) (to_string (member "file" request)) in
    state := Some loaded;
    let sentences = Array.to_list loaded.sentences in
    let diagnostics = List.filter (is_diagnostic loaded.text) sentences in
    `Assoc
      [ ("response", `String "loaded"); ("decls", `List (List.map (decl_json loaded) loaded.decls));
        ("diagnostics", `List (List.map (diagnostic_json loaded.text) diagnostics));
        ("commands", `List (List.map (command_json loaded) sentences)) ]
  | "ask" -> (
    match !state with
    | Some loaded -> answer loaded (member "question" request)
    | None -> `Assoc [ ("response", `String "error"); ("message", `String "no file is loaded") ])
  | _ -> `Assoc [ ("response", `String "error"); ("message", `String "unknown request") ]

(* -Q and -R of the nearest _CoqProject, with their directories made absolute. *)
let rec project_args dir =
  let file = Filename.concat dir "_CoqProject" in
  if Sys.file_exists file then begin
    let words = Str.split (Str.regexp "[ \t\n]+") (In_channel.with_open_bin file In_channel.input_all) in
    let rec args = function
      | (("-Q" | "-R") as flag) :: path :: name :: rest ->
        flag :: (if Filename.is_relative path then Filename.concat dir path else path) :: name :: args rest
      | _ :: rest -> args rest
      | [] -> []
    in
    args words
  end
  else if Filename.dirname dir = dir then []
  else project_args (Filename.dirname dir)

(* Rocq prints to stdout, which carries the protocol, so the answers go to a copy of it. *)
let answers =
  let copy = Unix.dup Unix.stdout in
  Unix.dup2 (Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0) Unix.stdout;
  Unix.out_channel_of_descr copy

let write response =
  output_string answers (Yojson.Safe.to_string response ^ "\n");
  flush answers

let handle initial state line =
  write
    (try respond initial state (Yojson.Safe.from_string line)
     with e -> `Assoc [ ("response", `String "error"); ("message", `String (error_text e)) ])

(* Rocq starts at the first `load`, since its load path comes from that file's project. *)
let () =
  let state = ref None in
  let rec wait () =
    match input_line stdin with
    | exception End_of_file -> ()
    | line when Yojson.Safe.Util.(to_string (member "request" (Yojson.Safe.from_string line))) <> "load" ->
      handle (lazy (failwith "no file is loaded")) state line;
      wait ()
    | line ->
      let file = Yojson.Safe.Util.(to_string (member "file" (Yojson.Safe.from_string line))) in
      let file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
      let run _ ~opts:_ _ =
        let initial = Lazy.from_val (Vernacstate.freeze_full_state ()) in
        handle initial state line;
        try while true do handle initial state (input_line stdin) done with End_of_file -> ()
      in
      Coqtop.start_coq { Coqtop.coqtop_toplevel with run } ([ "-q"; "-topfile"; file ] @ project_args (Filename.dirname file))
  in
  wait ()
