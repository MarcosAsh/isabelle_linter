(*  Title:      isabelle_linter/ml/linter_try0.ML

Print function for HOL sessions that runs try0 on a step's goal, as a baseline for faster_step.
*)

structure Linter_Try0 =
struct

fun method_timeout ms = if ms <= 0 then NONE else SOME (Time.fromMilliseconds ms);

(*try0 says `apply` for a proof that leaves goals.*)
fun closes ({command, ...}: Try0.result) = String.isPrefix "by " command;

(*try0 sorts what it finds by time, measured while it runs a slice of its schedule in parallel.*)
fun found (results: Try0.result list) =
  space_implode "; " (map (fn {name, time, ...} => name ^ " " ^ string_of_int (Time.toMilliseconds time)) results);

fun describe [] = ("fails", [])
  | describe (results as {command = first, ...} :: _) =
      let val listed = [("first", first), ("found", found results)] in
        (case find_first closes results of
          SOME {command, time, ...} =>
            ("closes", ("method", unprefix "by " command) :: Linter_Query.ms "method_ms" (Time.toMilliseconds time) :: listed)
        | NONE => ("fails", listed))
      end;

(*linter_try0 MS: try0 with MS ms for each method, 0 for its default; method is the fastest proof
  that closes, method_ms its time, first try0's own suggestion and found all it found.*)
val _ =
  Linter_Query.register "linter_try0" (fn limit => fn [ms] => fn st =>
    let
      val try0 = Try0.try0 (method_timeout (the (Int.fromString ms))) Try0.empty_facts;
      val (res, t) = Linter_Query.timed limit (fn () => try0 (Toplevel.proof_of st));
    in
      (case res of
        Exn.Res results => describe results ||> append (Linter_Query.times t)
      | _ => (Linter_Query.verdict res, Linter_Query.times t))
    end);

end;
