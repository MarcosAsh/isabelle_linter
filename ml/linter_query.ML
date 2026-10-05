(*  Title:      isabelle_linter/ml/linter_query.ML

Print functions that src/core/pide.scala attaches as overlays. Args: INSTANCE, TIMEOUT_MS, then

  linter_try  METHODS   run `by METHODS` on the goal
  linter_time N A B     run `by A` and `by B` N times each; ms, ms2 are the medians
  linter_run  TEXT      run an edited copy of the lemma from the state before it
  linter_goal           describe the goal, for learning which methods close it

Times are wall-clock ms. cpu and gc count the whole process, so they only mean something
when a question runs alone.
*)

structure Linter_Query =
struct

fun timed limit f =
  let
    val start = Timing.start ();
    val res = Exn.result (Timeout.apply limit f) ();
  in (res, Timing.result start) end;

(*a timeout must never count as a failure*)
fun verdict (Exn.Res _) = "closes"
  | verdict (Exn.Exn exn) =
      if Exn.is_interrupt_proper exn then Exn.reraise exn
      else
        (case exn of
          Timeout.TIMEOUT _ => "timeout"
        | _ => if String.isSubstring "Timeout" (Runtime.exn_message exn) then "timeout" else "fails");

fun parse_methods thy text =
  let
    val toks = Token.explode (Thy_Header.get_keywords thy) Position.none text |> filter Token.is_proper;
  in
    (case Scan.read Token.stopper (Method.parse -- Scan.option Method.parse) toks of
      SOME methods => methods
    | NONE => error ("Cannot parse proof methods " ^ quote text))
  end;

(*a toplevel goal is at the bottom of the proof stack*)
fun run_by st text () =
  let
    val pre = Toplevel.proof_of st;
    val methods = parse_methods (Proof.theory_of pre) text;
  in
    if can (Proof.assert_bottom true) pre
    then ignore (Proof.global_terminal_proof methods pre)
    else ignore (Proof.local_terminal_proof methods pre)
  end;

(*no position: markup would go into the theory; forked proofs must finish too*)
fun run_text st0 text () =
  let
    val thy = Toplevel.theory_of st0;
    val st = fold (Toplevel.command_exception false) (Outer_Syntax.parse_text thy (K thy) Position.none text) st0;
  in
    if Toplevel.is_proof st orelse Toplevel.is_skipped_proof st then error "Unfinished proof"
    else Thm.consolidate_theory (Toplevel.theory_of st)
  end;

fun median xs = nth (sort int_ord xs) (length xs div 2);


(* goal features *)

fun depth (t $ u) = Int.max (depth t, depth u) + 1
  | depth (Abs (_, _, t)) = depth t + 1
  | depth _ = 0;

fun concl t =
  (case Logic.strip_assums_concl t of
    Const ("HOL.Trueprop", _) $ u => u
  | u => u);

fun head t =
  (case Term.head_of (concl t) of
    Const (c, _) => c
  | Free _ => "free"
  | Var _ => "var"
  | _ => "other");

(*in every goal, so they say nothing*)
val noise = ["Pure.all", "Pure.imp", "HOL.Trueprop", "prop"];

fun consts t = subtract (op =) noise (Term.add_const_names t []);
fun tycons t =
  subtract (op =) noise (Term.fold_types (Term.fold_subtypes (fn Type (c, _) => insert (op =) c | _ => I)) t []);

fun local_facts ctxt =
  Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
    (Proof_Context.facts_of ctxt);

(*the first subgoal; the goal as text so features can be recomputed later*)
fun goal_features state =
  let
    val {context = ctxt, facts, goal} = Proof.goal state;
    val t = hd (Thm.prems_of goal);
    fun count name xs = (name, string_of_int (length xs));
    fun names name xs = (name, space_implode " " (sort_strings xs));
  in
    [count "subgoals" (Thm.prems_of goal),
     ("size", string_of_int (Term.size_of_term t)),
     ("depth", string_of_int (depth t)),
     ("head", head t),
     names "consts" (consts t),
     names "types" (tycons t),
     count "params" (Logic.strip_params t),
     count "prems" (Logic.strip_assums_hyp t),
     count "chained" facts,
     count "local_facts" (local_facts ctxt),
     ("goal", Pretty.pure_string_of (Syntax.pretty_term ctxt t))]
  end;


fun output instance verdict props =
  Output.result ((Markup.instanceN, instance) :: ("verdict", verdict) :: props) [verdict];

fun ms name n = (name, string_of_int n);

fun times ({elapsed, cpu, gc}: Timing.timing) =
  map (fn (name, t) => ms name (Time.toMilliseconds t)) [("ms", elapsed), ("cpu", cpu), ("gc", gc)];

fun register name check =
  Command.print_function name
    (fn {args = instance :: timeout_ms :: args, ...} =>
      SOME {delay = NONE, pri = Task_Queue.urgent_pri, persistent = false, strict = false,
        print_fn = fn _ => fn st =>
          let
            val limit = Time.fromMilliseconds (the (Int.fromString timeout_ms));
            val (verdict, props) = check limit args st handle ERROR msg => ("fails", [("message", msg)]);
          in output instance verdict props end}
    | _ => NONE);

val _ =
  register "linter_try" (fn limit => fn [text] => fn st =>
    let val (res, t) = timed limit (run_by st text) in (verdict res, times t) end);

val _ =
  register "linter_time" (fn limit => fn [n, a, b] => fn st =>
    let
      fun run text = timed limit (run_by st text) |> apfst verdict;
      val runs = map (fn _ => (run a, run b)) (1 upto the (Int.fromString n));
      val ok = forall (fn ((va, _), (vb, _)) => va = "closes" andalso vb = "closes") runs;

      fun med name f = ms name (median (map (Time.toMilliseconds o f) runs));
    in
      (if ok then "closes" else "fails",
        [med "ms" (#elapsed o #2 o #1), med "ms2" (#elapsed o #2 o #2),
         med "cpu" (#cpu o #2 o #1), med "cpu2" (#cpu o #2 o #2)])
    end);

val _ =
  register "linter_run" (fn limit => fn [text] => fn st =>
    let val (res, t) = timed limit (run_text st text) in (verdict res, times t) end);

val _ =
  register "linter_goal" (fn _ => fn [] => fn st => ("goal", goal_features (Toplevel.proof_of st)));

end;
