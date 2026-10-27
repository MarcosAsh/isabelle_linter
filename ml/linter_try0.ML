(*  Title:      isabelle_linter/ml/linter_try0.ML

Print function for HOL sessions. Args: INSTANCE, TIMEOUT_MS, then

  linter_try0 MS   run try0 on the goal, as the try0 command does: its schedule, each method
                   with MS ms (0: try0's own default, try0_default_timeout); method is the
                   fastest proof that closes the goal and method_ms its time as try0 measured
                   it, first is try0's own suggestion, found everything it found

try0 runs a slice of its schedule in parallel and sorts what it finds by time, so method_ms is
taken under load. ms is the whole run.
*)

structure Linter_Try0 =
struct

fun method_timeout ms = if ms <= 0 then NONE else SOME (Time.fromMilliseconds ms);

(*try0 says `apply` for a proof that leaves goals*)
fun closes ({command, ...}: Try0.result) = String.isPrefix "by " command;

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
