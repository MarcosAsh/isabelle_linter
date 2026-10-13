(*  Title:      isabelle_linter/ml/linter_query.ML

Print functions that src/core/pide.scala attaches as overlays. Args: INSTANCE, TIMEOUT_MS, then

  linter_try  METHODS   run `by METHODS` on the goal
  linter_time N A B     run `by A` and `by B` N times each; ms, ms2 are the medians, as are
                        cpu, cpu2 and gc, gc2
  linter_run  TEXT      run an edited copy of the lemma from the state before it
  linter_runs N A B     run lemma texts A and B N times each, in turn; ms, ms2 are the medians,
                        as are cpu, cpu2
  linter_times N M...   run each `by M` N times; ms0, ms1 ... are the medians of those that close,
                        cpu0, gc0 ... the medians of their cpu and gc, runs0 ... every run's ms
  linter_goal           describe the goal, for learning which methods close it
  linter_profile M      run `by M` once under Poly/ML's time profiler for this thread; the
                        profile arrives as a tracing message on the command
  linter_subgoals M C...  run `apply M`, then try each C on each subgoal alone; sub1, ms1 ... are
                        the fastest C (as an index) and its time, for the subgoals some C closes
  linter_used_rules M   run `by M`; rules are the simp rules, and the facts named in M, that its
                        proof used, as names that parse in the goal's context; facts are all
                        named theorems it used that M does not name, minus logic and
                        internals; subgoals counts the goals before it

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


(* subgoals *)

fun apply_text text state =
  Proof.apply (#1 (parse_methods (Proof.theory_of state) text)) state |> Seq.the_result "";

fun nsubgoals state = Thm.nprems_of (#goal (Proof.goal state));

(*restricted to the first subgoal, which it must close*)
fun close_first text state () =
  let val n = nsubgoals state in
    if nsubgoals (apply_text ("(" ^ text ^ ")[1]") state) = n - 1 then ()
    else error "Subgoal not closed"
  end;

(*each later try only gets the best time so far; under 1 ms Timeout.apply has no limit at all*)
fun fastest limit closers state =
  fold (fn (i, text) => fn best =>
    let
      val budget =
        (case best of SOME (_, t) => Time.min (limit, t) | NONE => limit)
        |> curry Time.max (Time.fromMilliseconds 1);
      val (res, t) = timed budget (close_first text state);
    in
      if verdict res = "closes" andalso (case best of SOME (_, b) => #elapsed t < b | NONE => true)
      then SOME (i, #elapsed t) else best
    end) (map_index I closers) NONE;


(* used rules *)

(*like `by M1 M2`, but keeping the finished goal*)
fun finish_by (m1, m2) state =
  Proof.proof (SOME m1) state |> Seq.the_result ""
  |> (case m2 of SOME m => Proof.apply_end m #> Seq.the_result "" | NONE => I)
  |> Proof.apply_end (Method.finish_text (NONE, true), Position.no_range) |> Seq.the_result ""
  |> Proof.goal |> #goal;

(*the shortest name that still means this fact here*)
fun extern_fact ctxt name =
  let
    val space = Facts.space_of (Proof_Context.facts_of_fact ctxt name);
    val xname = Name_Space.extern ctxt space name;
  in if Name_Space.intern space xname = name then SOME xname else NONE end;

(*logic, type classes, metis and meson's own reconstruction, and definitional internals
  (monotonicity of inductive definitions, termination) that no proof method needs as a fact*)
fun plumbing name =
  let val base = Long_Name.base_name name in
    exists (fn thy => String.isPrefix (thy ^ ".") name) ["Pure", "HOL", "Meson", "Metis", "Inductive"] orelse
    member (op =) ["super", "termination", "cases", "exhaust", "monoI"] base orelse
    exists (fn p => String.isPrefix p base) ["arity_", "classrel_", "le_bool", "le_fun"] orelse
    String.isSuffix "_mono" base orelse
    exists (fn s => String.isSubstring s name) ["accp", "fundef_", "_cong"]
  end;

(*named theorems the proof depends on, stopping at each; forked proofs are joined first*)
fun used_rules st text () =
  let
    val state = Toplevel.proof_of st;
    val ctxt = Proof.context_of state;
    val thy = Proof_Context.theory_of ctxt;
    val goal = finish_by (parse_methods thy text) state;
    val _ = Thm.no_prems goal orelse error "Unfinished proof";

    val deps = Thm_Deps.thm_deps thy [Thm.close_derivation Position.none goal];
    val simps = map (#1 o #1) (Raw_Simplifier.dest_simps (simpset_of ctxt));
    val words = Token.explode (Thy_Header.get_keywords thy) Position.none text |> map Token.content_of;
    fun named name xname = exists (member (op =) words) [name, xname];
    fun pick keep (name, i) =
      (case extern_fact ctxt name of
        SOME xname => if keep name xname then SOME (xname ^ Thm_Name.print_suffix (name, i)) else NONE
      | NONE => NONE);
    val rule = pick (fn name => fn xname => member (op =) simps name orelse named name xname);
    val fact = pick (fn name => fn xname => not (named name xname orelse plumbing name));
    val names = map #2 deps;
  in (map_filter rule names, distinct (op =) (map_filter fact names)) end;


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

fun count name xs = (name, string_of_int (length xs));
fun names name xs = (name, space_implode " " (sort_strings xs));

fun subgoal_features ctxt facts goal t =
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
   ("goal", Pretty.pure_string_of (Syntax.pretty_term ctxt t))];

(*the first subgoal; the goal as text so features can be recomputed later*)
fun goal_features state =
  let val {context = ctxt, facts, goal} = Proof.goal state in
    (case Thm.prems_of goal of
      [] => [count "subgoals" []]
    | t :: _ => subgoal_features ctxt facts goal t)
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
            val (verdict, props) =
              (case Exn.result (check limit args) st of
                Exn.Res res => res
              | Exn.Exn exn =>
                  if Exn.is_interrupt exn then Exn.reraise exn
                  else ("fails", [("message", Runtime.exn_message exn)]));
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
         med "cpu" (#cpu o #2 o #1), med "cpu2" (#cpu o #2 o #2),
         med "gc" (#gc o #2 o #1), med "gc2" (#gc o #2 o #2)])
    end);

val _ =
  register "linter_runs" (fn limit => fn [n, a, b] => fn st =>
    let
      fun run text = timed limit (run_text st text) |> apfst verdict;
      val runs = map (fn _ => (run a, run b)) (1 upto the (Int.fromString n));
      val ok = forall (fn ((va, _), (vb, _)) => va = "closes" andalso vb = "closes") runs;

      fun med name f = ms name (median (map (Time.toMilliseconds o f) runs));
    in
      (if ok then "closes" else "fails",
        [med "ms" (#elapsed o #2 o #1), med "ms2" (#elapsed o #2 o #2),
         med "cpu" (#cpu o #2 o #1), med "cpu2" (#cpu o #2 o #2)])
    end);

(*the methods run one after another, never in parallel*)
val _ =
  register "linter_times" (fn limit => fn n :: methods => fn st =>
    let
      fun run text = timed limit (run_by st text);
      fun medians (i, text) =
        let
          val runs = map (fn _ => run text) (1 upto the (Int.fromString n));
          fun med name f = ms (name ^ string_of_int i) (median (map (Time.toMilliseconds o f o #2) runs));
          val each = ("runs" ^ string_of_int i,
            space_implode "," (map (string_of_int o Time.toMilliseconds o #elapsed o #2) runs));
        in
          if forall (fn (res, _) => verdict res = "closes") runs
          then [med "ms" #elapsed, med "cpu" #cpu, med "gc" #gc, each] else []
        end;
    in ("closes", maps medians (map_index I methods)) end);

val _ =
  register "linter_run" (fn limit => fn [text] => fn st =>
    let val (res, t) = timed limit (run_text st text) in (verdict res, times t) end);

(*the profile is a tracing message on the command, so ask it alone*)
val _ =
  register "linter_profile" (fn limit => fn [text] => fn st =>
    let val (res, t) = timed limit (fn () => ML_Profiling.profile "time_thread" (run_by st text) ())
    in (verdict res, times t) end);

val _ =
  register "linter_goal" (fn _ => fn [] => fn st => ("goal", goal_features (Toplevel.proof_of st)));

val _ =
  register "linter_subgoals" (fn limit => fn first :: closers => fn st =>
    let
      val after = apply_text first (Toplevel.proof_of st);
      val n = nsubgoals after;

      fun subgoal i =
        (case fastest limit closers (Proof.prefer i after) of
          SOME (j, t) => [("sub" ^ string_of_int i, string_of_int j), ms ("ms" ^ string_of_int i) (Time.toMilliseconds t)]
        | NONE => []);
    in ("closes", ms "n" n :: maps subgoal (1 upto n)) end);

val _ =
  register "linter_used_rules" (fn limit => fn [text] => fn st =>
    ("closes",
      let val (rules, facts) = Timeout.apply limit (used_rules st text) () in
        [("rules", space_implode " " rules), ("facts", space_implode " " facts),
         ms "subgoals" (nsubgoals (Toplevel.proof_of st))]
      end));

end;
