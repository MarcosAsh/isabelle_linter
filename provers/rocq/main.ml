(* The Rocq server of xlint. It drives one `rocq repl` and goes back to the state before a
   lemma to check it again with edited text. Offsets are bytes into the file. *)

let sub text start stop = String.sub text start (stop - start)

(* sentences *)

let is_blank c = c = ' ' || c = '\n' || c = '\t' || c = '\r'

(* The end of the comment that starts at `i`. Comments nest. *)
let rec skip_comment text i depth =
  let n = String.length text in
  if i + 1 >= n then n
  else if text.[i] = '(' && text.[i + 1] = '*' then skip_comment text (i + 2) (depth + 1)
  else if text.[i] = '*' && text.[i + 1] = ')' then
    if depth = 1 then i + 2 else skip_comment text (i + 2) (depth - 1)
  else skip_comment text (i + 1) depth

let rec skip_blank text i =
  let n = String.length text in
  if i < n && is_blank text.[i] then skip_blank text (i + 1)
  else if i + 1 < n && text.[i] = '(' && text.[i + 1] = '*' then skip_blank text (skip_comment text (i + 2) 1)
  else i

let is_bullet c = c = '-' || c = '+' || c = '*'

(* The next sentence from `i`, as (start, stop). Bullets and braces are sentences only in a proof. *)
let next_sentence text i in_proof =
  let n = String.length text in
  let start = skip_blank text i in
  if start >= n then None
  else if in_proof && (text.[start] = '{' || text.[start] = '}') then Some (start, start + 1)
  else if in_proof && is_bullet text.[start] then begin
    let stop = ref start in
    while !stop < n && text.[!stop] = text.[start] do incr stop done;
    Some (start, !stop)
  end
  else begin
    let rec scan i =
      if i >= n then n
      else if text.[i] = '"' then scan ((try String.index_from text (i + 1) '"' with Not_found -> n - 1) + 1)
      else if i + 1 < n && text.[i] = '(' && text.[i + 1] = '*' then scan (skip_comment text (i + 2) 1)
      else if text.[i] = '.' && (i + 1 = n || is_blank text.[i + 1]) then i + 1
      else scan (i + 1)
    in
    Some (start, scan start)
  end

let first_word sentence =
  let stop = ref 0 in
  let n = String.length sentence in
  while !stop < n && (match sentence.[!stop] with 'A' .. 'Z' | 'a' .. 'z' | '_' -> true | _ -> false) do incr stop done;
  String.sub sentence 0 !stop

let opens_proof word =
  List.mem word [ "Lemma"; "Theorem"; "Corollary"; "Proposition"; "Fact"; "Remark"; "Example"; "Goal" ]

let closes_proof word = List.mem word [ "Qed"; "Defined"; "Admitted"; "Abort"; "Save" ]

(* the repl *)

type repl = { pid : int; input : out_channel; output : Unix.file_descr; mutable state : int; mutable depth : int }

(* `name < state |open proofs| depth < `, as `-emacs` prints it *)
let prompt = Str.regexp "<prompt>[^<]*< \\([0-9]+\\) |\\([^|]*\\)| [0-9]+ < </prompt>"

(* Read up to the next prompt, or interrupt the repl after `timeout_ms`. Returns what it wrote
   and whether it ran out of time. *)
let read_reply repl timeout_ms =
  let buffer = Buffer.create 1024 in
  let chunk = Bytes.create 65536 in
  let deadline = Unix.gettimeofday () +. (float_of_int timeout_ms /. 1000.) in
  let late = ref false in
  let rec loop () =
    let text = Buffer.contents buffer in
    match Str.search_backward prompt text (String.length text) with
    | _ when Str.match_end () = String.length text ->
      repl.state <- int_of_string (Str.matched_group 1 text);
      repl.depth <- (if Str.matched_group 2 text = "" then 0 else 1);
      text
    | _ | (exception Not_found) ->
      let left = if !late then 60. else deadline -. Unix.gettimeofday () in
      if left <= 0. then begin
        late := true;
        Unix.kill repl.pid Sys.sigint;
        loop ()
      end
      else begin
        (match Unix.select [ repl.output ] [] [] left with
         | [], _, _ -> ()
         | _ ->
           let n = Unix.read repl.output chunk 0 (Bytes.length chunk) in
           if n = 0 then failwith "the Rocq repl closed its output";
           Buffer.add_subbytes buffer chunk 0 n);
        loop ()
      end
  in
  let text = loop () in
  (text, !late)

let has_error reply =
  try ignore (Str.search_forward (Str.regexp "^Error:\\|^Anomaly") reply 0); true with Not_found -> false

(* Run one sentence. Returns the verdict, the ms and the repl's output. *)
let feed repl sentence timeout_ms =
  let line = String.map (fun c -> if c = '\n' || c = '\r' then ' ' else c) sentence in
  let start = Unix.gettimeofday () in
  output_string repl.input (line ^ "\n");
  flush repl.input;
  let reply, late = read_reply repl timeout_ms in
  let ms = int_of_float ((Unix.gettimeofday () -. start) *. 1000.) in
  ((if late then "timeout" else if has_error reply then "fails" else "closes"), ms, reply)

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

let start_repl file =
  let top = try Sys.getenv "XLINT_ROCQ_TOP" with Not_found -> "rocq repl" in
  let dir = Filename.dirname (if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file) in
  let command = Str.split (Str.regexp " +") top @ [ "-emacs"; "-q" ] @ project_args dir in
  let to_repl, input = Unix.pipe ~cloexec:true () in
  let output, from_repl = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process (List.hd command) (Array.of_list command) to_repl from_repl from_repl in
  Unix.close to_repl;
  Unix.close from_repl;
  let repl = { pid; input = Unix.out_channel_of_descr input; output; state = 0; depth = 0 } in
  ignore (read_reply repl 60000);
  repl

(* the loaded file *)

type sentence = { start : int; stop : int; mutable before : int; ms : int }

type decl = {
  key : string;
  name : string;
  first : int;  (* index of its statement in the sentences *)
  last : int;
  ok : bool;
  pieces : Yojson.Safe.t list;
}

type loaded = {
  file : string;
  text : string;
  repl : repl;
  sentences : sentence array;
  decls : decl list;
  (* Sentences before this index are in the repl as written, each at its `before` state. *)
  mutable frontier : int;
}

let line_number text pos =
  let n = ref 1 in
  String.iteri (fun i c -> if i < pos && c = '\n' then incr n) text;
  !n

let range start stop = `Assoc [ ("start", `Int start); ("stop", `Int stop) ]

(* A tactic sentence that fills its own lines goes with them. *)
let piece text (s : sentence) =
  let source = sub text s.start s.stop in
  let word = first_word source in
  let line_start = try String.rindex_from text (max 0 (s.start - 1)) '\n' + 1 with Not_found -> 0 in
  let line_stop = try String.index_from text s.stop '\n' + 1 with Not_found -> String.length text in
  let blank a b = String.for_all is_blank (sub text a b) in
  let alone = (s.start = 0 || blank line_start s.start) && blank s.stop line_stop in
  let start, stop = if alone then (line_start, line_stop) else (s.start, s.stop) in
  let kind = if List.mem word [ "assert"; "pose"; "have"; "enough"; "specialize" ] then "have" else "tactic" in
  `Assoc
    [ ("kind", `String kind); ("text", `String (List.hd (String.split_on_char '\n' source)));
      ("range", range start stop); ("line", `Int (line_number text s.start)) ]

let is_tactic text (s : sentence) =
  let c = text.[s.start] in
  let word = first_word (sub text s.start s.stop) in
  not (c = '{' || c = '}' || is_bullet c || word = "Proof" || closes_proof word)

let load file =
  let text = In_channel.with_open_bin file In_channel.input_all in
  let repl = start_repl file in
  let sentences = ref [] in
  let decls = ref [] in
  let opened = ref None in
  let failed = ref false in
  let rec go i index =
    match next_sentence text i (repl.depth > 0) with
    | None -> ()
    | Some (start, stop) ->
      let before = repl.state in
      let source = sub text start stop in
      let verdict, ms, reply = feed repl source 600000 in
      if verdict <> "closes" && repl.depth = 0 && !opened = None then
        failwith (Printf.sprintf "%s:%d: %s" file (line_number text start) (String.trim reply));
      sentences := { start; stop; before; ms } :: !sentences;
      let word = first_word source in
      if verdict <> "closes" then failed := true;
      (match !opened with
       | None when repl.depth > 0 && opens_proof word -> opened := Some index; failed := false
       | Some first when repl.depth = 0 || closes_proof word ->
         let all = Array.of_list (List.rev !sentences) in
         let statement = sub text all.(first).start all.(first).stop in
         let name =
           match Str.split (Str.regexp "[ \t\n:(]+") statement with _ :: name :: _ -> name | _ -> "" in
         let body = Array.to_list (Array.sub all (first + 1) (index - first - 1)) in
         let ok = (not !failed) && (word = "Qed" || word = "Defined") in
         decls :=
           { key = Printf.sprintf "%s:%d" file all.(first).start; name; first; last = index; ok;
             pieces = List.map (piece text) (List.filter (is_tactic text) body) }
           :: !decls;
         opened := None
       | _ -> ());
      go stop (index + 1)
  in
  go 0 0;
  let sentences = Array.of_list (List.rev !sentences) in
  { file; text; repl; sentences; decls = List.rev !decls; frontier = Array.length sentences }

(* Put the repl in the state before sentence `index`, running the file's own sentences again
   if an earlier question went back past it. *)
let goto loaded index =
  let back_to state = ignore (feed loaded.repl (Printf.sprintf "BackTo %d." state) 600000) in
  if index <= loaded.frontier then back_to loaded.sentences.(index).before
  else begin
    back_to loaded.sentences.(loaded.frontier).before;
    for i = loaded.frontier to index - 1 do
      let s = loaded.sentences.(i) in
      s.before <- loaded.repl.state;
      ignore (feed loaded.repl (sub loaded.text s.start s.stop) 600000)
    done;
    if index < Array.length loaded.sentences then loaded.sentences.(index).before <- loaded.repl.state
  end;
  loaded.frontier <- index

let apply_edits text start stop edits =
  let latest_first = List.sort (fun (a, _, _) (b, _, _) -> compare b a) edits in
  let out, upto =
    List.fold_left
      (fun (out, upto) (from, till, replacement) -> (replacement ^ sub text till upto ^ out, from))
      ("", stop) latest_first
  in
  sub text start upto ^ out

(* Check the lemma once with the edits, from the state before it. *)
let run_once loaded decl edits timeout_ms =
  goto loaded decl.first;
  let first, last = (loaded.sentences.(decl.first), loaded.sentences.(decl.last)) in
  let source = apply_edits loaded.text first.start last.stop edits in
  let deadline = Unix.gettimeofday () +. (float_of_int timeout_ms /. 1000.) in
  let start = Unix.gettimeofday () in
  let elapsed () = int_of_float ((Unix.gettimeofday () -. start) *. 1000.) in
  let rec go i ran =
    match next_sentence source i (ran && loaded.repl.depth > 0) with
    | None -> if loaded.repl.depth = 0 then ("closes", "") else ("fails", "the proof is not finished")
    | Some (from, till) ->
      let left = int_of_float ((deadline -. Unix.gettimeofday ()) *. 1000.) in
      if left <= 0 then ("timeout", "")
      else begin
        match feed loaded.repl (sub source from till) left with
        | "closes", _, _ ->
          if loaded.repl.depth = 0 && String.trim (sub source till (String.length source)) <> "" then
            ("fails", "the edited text is more than one lemma")
          else go till true
        | verdict, _, reply -> (verdict, String.trim reply)
      end
  in
  let verdict, message = go 0 false in
  (verdict, elapsed (), message)

(* the protocol *)

let decl_json loaded decl =
  let first, last = (loaded.sentences.(decl.first), loaded.sentences.(decl.last)) in
  `Assoc
    [ ("key", `String decl.key); ("name", `String decl.name); ("kind", `String "theorem");
      ("range", range first.start last.stop); ("line", `Int (line_number loaded.text first.start));
      ("ok", `Bool decl.ok); ("steps", `List []); ("simps", `List []); ("pieces", `List decl.pieces) ]

let command_json loaded (s : sentence) =
  let source = sub loaded.text s.start s.stop in
  `Assoc
    [ ("kind", `String (first_word source)); ("text", `String (List.hd (String.split_on_char '\n' source)));
      ("range", range s.start s.stop); ("ms", `Int s.ms) ]

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
  match List.find_opt (fun d -> d.key = to_string (member "decl" question)) loaded.decls with
  | None -> reply "error" [] "no such declaration"
  | Some _ when to_string (member "do" question) <> "run" -> reply "error" [] "the Rocq server can only run"
  | Some decl ->
    let edits =
      List.map
        (fun edit ->
          let range = member "range" edit in
          (to_int (member "start" range), to_int (member "stop" range), to_string (member "text" edit)))
        (to_list (member "edits" question))
    in
    let timeout = to_int (member "timeout_ms" question) in
    let runs = max 1 (to_int (member "runs" question)) in
    let rec go left times =
      if left = 0 then reply "closes" (List.rev times) ""
      else
        match run_once loaded decl edits timeout with
        | "closes", ms, _ -> go (left - 1) (ms :: times)
        | verdict, ms, message -> reply verdict [ ms ] message
    in
    go runs []

let version () =
  let top = try Sys.getenv "XLINT_ROCQ_TOP" with Not_found -> "rocq repl" in
  let channel = Unix.open_process_in (List.hd (String.split_on_char ' ' top) ^ " -v </dev/null 2>&1") in
  let line = try input_line channel with End_of_file -> "" in
  ignore (Unix.close_process_in channel);
  line

let respond state request =
  let open Yojson.Safe.Util in
  match to_string (member "request" request) with
  | "hello" ->
    `Assoc
      [ ("response", `String "hello");
        ("hello", `Assoc [ ("prover", `String "rocq"); ("version", `String (version ())); ("closers", `List []) ]) ]
  | "load" ->
    let loaded = load (to_string (member "file" request)) in
    state := Some loaded;
    `Assoc
      [ ("response", `String "loaded"); ("decls", `List (List.map (decl_json loaded) loaded.decls));
        ("diagnostics", `List []);
        ("commands", `List (Array.to_list (Array.map (command_json loaded) loaded.sentences))) ]
  | "ask" -> (
    match !state with
    | Some loaded -> answer loaded (member "question" request)
    | None -> `Assoc [ ("response", `String "error"); ("message", `String "no file is loaded") ])
  | _ -> `Assoc [ ("response", `String "error"); ("message", `String "unknown request") ]

let () =
  let state = ref None in
  try
    while true do
      let line = input_line stdin in
      let response =
        try respond state (Yojson.Safe.from_string line)
        with e -> `Assoc [ ("response", `String "error"); ("message", `String (Printexc.to_string e)) ]
      in
      print_endline (Yojson.Safe.to_string response)
    done
  with End_of_file -> ()
