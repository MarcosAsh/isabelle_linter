(*  Title:      isabelle_linter/ml/linter_query.ML

Print functions that src/core/pide.scala attaches as overlays. Args: INSTANCE, TIMEOUT_MS, then

  linter_try  METHODS   run `by METHODS` on the goal
  linter_time N A B     run `by A` and `by B` N times each; ms, ms2 are the medians, as are
                        cpu, cpu2 and gc, gc2
  linter_run  TEXT      run an edited copy of the lemma from the state before it
  linter_runs N A B     run lemma texts A and B N times each, in turn, B first every other
                        time; ms, ms2 are the medians, as are cpu, cpu2
  linter_times N M...   run each `by M` N times; ms0, ms1 ... are the medians of those that close,
                        cpu0, gc0 ... the medians of their cpu and gc, runs0 ... every run's ms
  linter_goal           describe the goal, for learning which methods close it
  linter_profile M      run `by M` once under Poly/ML's time profiler for this thread; the
                        profile arrives as a tracing message on the command
  linter_subgoals M C...  run `apply M`, then try each C on each subgoal alone; sub1, ms1 ... are
                        the fastest C (as an index) and its time, for the subgoals some C closes
  linter_used_rules M   run `by M`; rules are the simp rules, and the facts named in M, that its
                        proof used, as names that parse in the goal's context; subgoals counts
                        the goals before it
  linter_imports REF... on a theory's last command: uses are the other theories whose theorems
                        its facts' proofs use, that declared the constants, types, classes and
                        type instances its facts and constants mention, or the entities REF
                        ("kind name", from the text's markup); context is "theory facts simps
                        consts types classes" for each theory in its context, joined by ";"
  linter_names A B...   run texts A, B1 ... from the state; per Bi: oki, msi, missingi, differi, reorderedi
  linter_used_members M F...  run `by M`; used0, used1 ... are the names of the theorems of
                        each fact F that its proof used, all0, all1 ... the names of all of
                        them; "-" for none, "*" when a theorem has no global name
  linter_try_del M F... run `by M` with the theorems of the facts F deleted from the simpset

Times are wall-clock ms. cpu and gc count the whole process, so they only mean something
when a question runs alone. A question cancelled while it runs answers "interrupted", with
its time so far.
*)

structure Linter_Query =
struct

(*physical: a plain timeout is postponed by GC time, so under heap pressure it can run for far
  longer than its limit*)
fun timed limit f =
  let
    val start = Timing.start ();
    val res = Exn.result (Timeout.apply_physical limit f) ();
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
fun run_on pre text () =
  let val methods = parse_methods (Proof.theory_of pre) text in
    if can (Proof.assert_bottom true) pre
    then ignore (Proof.global_terminal_proof methods pre)
    else ignore (Proof.local_terminal_proof methods pre)
  end;

fun run_by st = run_on (Toplevel.proof_of st);

(*no position: markup would go into the theory; forked proofs must finish too*)
fun run_state st0 text () =
  let
    val thy = Toplevel.theory_of st0;
    val st = fold (Toplevel.command_exception false) (Outer_Syntax.parse_text thy (K thy) Position.none text) st0;
  in
    if Toplevel.is_proof st orelse Toplevel.is_skipped_proof st then error "Unfinished proof"
    else (Thm.consolidate_theory (Toplevel.theory_of st); st)
  end;

fun run_text st0 text () = ignore (run_state st0 text ());

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

(*each later try only gets the best time so far; under 1 ms a timeout has no limit at all*)
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
    fun rule (name, i) =
      (case extern_fact ctxt name of
        SOME xname =>
          if member (op =) simps name orelse exists (member (op =) words) [name, xname]
          then SOME (xname ^ Thm_Name.print_suffix (name, i)) else NONE
      | NONE => NONE);
  in map_filter (rule o #2) deps end;


(* names a definition adds *)

fun spaces st =
  let
    val ctxt = Toplevel.context_of st;
    val thy = Proof_Context.theory_of ctxt;
  in
    [Facts.space_of (Global_Theory.facts_of thy), Facts.space_of (Proof_Context.facts_of ctxt),
     Consts.space_of (Sign.consts_of thy)]
  end;

fun new_names space0 space = filter_out (Symtab.defined (Symtab.make_set (Name_Space.get_names space0)))
  (Name_Space.get_names space);

(*as a's context writes them*)
fun missing st_a st_b =
  let val ctxt = Toplevel.context_of st_a in
    maps (fn (a, b) => map (Name_Space.extern ctxt a) (new_names b a)) (spaces st_a ~~ spaces st_b)
    |> distinct (op =)
  end;

fun fact_tables st =
  let val ctxt = Toplevel.context_of st
  in [Global_Theory.facts_of (Proof_Context.theory_of ctxt), Proof_Context.facts_of ctxt] end;

fun props st facts name =
  Facts.lookup (Context.Proof (Toplevel.context_of st)) facts name |> Option.map (map Thm.prop_of o #thms);

(*"differ": other theorem; "reordered": same facts in another order*)
fun changed st0 st_a st_b =
  let
    val ctxt = Toplevel.context_of st_a;
    fun compare (fa, fb) name =
      (case (props st_a fa name, props st_b fb name) of
        (SOME ts, SOME us) =>
          if eq_list (op aconv) (ts, us) then NONE
          else SOME ((if eq_set (op aconv) (ts, us) then "reordered" else "differ"),
            Facts.extern ctxt fa name)
      | _ => NONE);
    fun table ((f0, fa), fb) =
      map_filter (compare (fa, fb)) (new_names (Facts.space_of f0) (Facts.space_of fa));
    val found = maps table (fact_tables st0 ~~ fact_tables st_a ~~ fact_tables st_b);
    fun names kind = distinct (op =) (map #2 (filter (fn (k, _) => k = kind) found));
  in (names "differ", names "reordered") end;


(* theorems of a fact, for simp_scope *)

fun eval_fact ctxt text =
  let
    val keywords = Thy_Header.get_keywords (Proof_Context.theory_of ctxt);
    val toks = Token.explode keywords Position.none text |> filter Token.is_proper;
  in
    (case Scan.read Token.stopper Parse.thms1 toks of
      SOME srcs => Attrib.eval_thms ctxt srcs
    | NONE => error ("Cannot parse fact " ^ quote text))
  end;

fun denotes ctxt thm (name, i) =
  (case extern_fact ctxt name of
    SOME xname =>
      let
        val ths = Proof_Context.get_fact ctxt (Facts.named xname) handle ERROR _ => [];
        val k = if i = 0 then 1 else i;
      in
        if (i > 0 orelse length ths = 1) andalso k <= length ths andalso Thm.eq_thm_prop (nth ths (k - 1), thm)
        then SOME (xname ^ Thm_Name.print_suffix (name, i)) else NONE
      end
  | NONE => NONE);

(*`lemmas defs = a_def b_def` renames its theorems: defs(2), a_def*)
fun names_below thy thm =
  let
    fun down 0 _ = []
      | down n th =
          (case try (Thm_Deps.thm_deps thy) [th] of
            SOME [(_, name)] =>
              (case try (Global_Theory.get_thm_name thy) (name, Position.none) of
                SOME th' => if Thm.eq_thm_prop (th, th') then name :: down (n - 1) th' else []
              | NONE => [])
          | _ => []);
  in down 5 thm end;

(*global identity and most specific name; a note only gives a hint like local.simps(1)*)
fun global_name ctxt thm =
  let val thy = Proof_Context.theory_of ctxt in
    (case Global_Theory.lookup_thm thy thm of
      SOME (id, (name, _)) =>
        (case get_first (denotes ctxt thm) (rev (names_below thy thm) @ [name, Thm.get_name_hint thm]) of
          SOME xname => SOME (id, xname)
        | NONE => NONE)
    | NONE => NONE)
  end;

fun print_names [] = "-"
  | print_names names = space_implode " " (distinct (op =) names);

fun used_of ctxt deps text =
  let
    val members = map (global_name ctxt) (eval_fact ctxt text);
    val named = map_filter I members;
    val used = filter (fn (id, _) => member (op =) deps id) named;
  in
    if exists is_none members then ("*", "*")
    else (print_names (map #2 used), print_names (map #2 named))
  end;

fun used_members st text facts () =
  let
    val state = Toplevel.proof_of st;
    val ctxt = Proof.context_of state;
    val thy = Proof_Context.theory_of ctxt;
    val goal = finish_by (parse_methods thy text) state;
    val _ = Thm.no_prems goal orelse error "Unfinished proof";
    val deps = map #1 (Thm_Deps.thm_deps thy [Thm.close_derivation Position.none goal]);
  in map (used_of ctxt deps) facts end;

fun without_simps facts st =
  Toplevel.proof_of st |> Proof.map_context (fn ctxt =>
    ctxt
    |> Context_Position.set_visible false
    |> Simplifier.del_simps (maps (eval_fact ctxt) facts)
    |> Context_Position.restore_visible ctxt);


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


(* imports *)

(*the theory that declared name, if the space knows it*)
fun entry_theory space name = try (Name_Space.theory_name {long = true} space) name;

fun facts_space thy = Facts.space_of (Global_Theory.facts_of thy);

(*the name spaces of the entity kinds that markup refers to; other kinds are ignored*)
fun kind_space thy kind =
  AList.lookup (op =)
    [(Markup.constantN, Sign.const_space), (Markup.type_nameN, Sign.type_space),
     (Markup.classN, Sign.class_space), (Markup.factN, facts_space),
     (Markup.localeN, Locale.locale_space), (Markup.bundleN, Bundle.bundle_space o Context.Theory),
     (Markup.methodN, Method.method_space o Context.Theory),
     (Markup.attributeN, Attrib.attribute_space o Context.Theory)] kind
  |> Option.map (fn space => space thy);

fun own thy space name = entry_theory space name = SOME (Context.theory_long_name thy);

fun own_thms thy =
  Facts.fold_static (fn (a, ths) => own thy (facts_space thy) a ? append ths)
    (Global_Theory.facts_of thy) [];

(*constants with their types, and abbreviations with what they stand for*)
fun own_const_terms thy =
  #constants (Consts.dest (Sign.consts_of thy))
  |> maps (fn (c, (T, rhs)) => if own thy (Sign.const_space thy) c then Const (c, T) :: the_list rhs else []);

(*the theories of the theorems that derivations use, looking through those of thy itself*)
fun proof_theories thy thms =
  let
    val name = Context.theory_long_name thy;
    fun walk (i, node) (seen, used) =
      if Inttab.defined seen i then (seen, used)
      else
        let val a = #theory_name (Proofterm.thm_id (i, node)) in
          if a = name then fold walk (Proofterm.thm_node_thms node) (Inttab.update (i, ()) seen, used)
          else (Inttab.update (i, ()) seen, Symtab.update (a, ()) used)
        end;
    fun deps thm = the_default [] (try Thm.thm_deps thm);
  in fold (fold walk o deps) thms (Inttab.empty, Symtab.empty) |> #2 |> Symtab.keys end;

fun add_key a = Symtab.update (a, ());

fun term_names ts =
  (fold (Term.fold_aterms (fn Const (c, _) => add_key c | _ => I)) ts Symtab.empty |> Symtab.keys,
   fold (Term.fold_types (Term.fold_subtypes (fn Type (a, _) => add_key a | _ => I))) ts Symtab.empty
   |> Symtab.keys,
   fold (Term.fold_types (Term.fold_atyps_sorts (fn (_, S) => fold add_key S))) ts Symtab.empty
   |> Symtab.keys);

(*a type instance counts for each class that a mentioned constant or type variable asks for, except
  the default sort, which every type has (in HOL)*)
fun arity_theories thy tycons classes =
  let val all = subtract (op =) (Sign.defaultS thy) (Sign.complete_sort thy classes) in
    maps (fn a => maps (fn c => Thm.theory_names_of_arity {long = true} thy (a, c)) all) tycons
  end;

(*the theories that declared the constants, types and classes of ts, and the instances they need*)
fun term_theories thy ts =
  let
    val (consts, types, sorts) = term_names ts;
    val schemes = map_filter (try (Consts.the_constraint (Sign.consts_of thy))) consts;
    val classes = distinct (op =) (sorts @ #3 (term_names (map (fn T => Free ("x", T)) schemes)));
    fun theories space = map_filter (entry_theory space);
  in
    theories (Sign.const_space thy) consts @ theories (Sign.type_space thy) types @
    theories (Sign.class_space thy) classes @ arity_theories thy types classes
  end;

fun dest_ref r =
  (case space_explode " " r of
    [kind, name] => SOME (kind, name)
  | _ => NONE);

fun ref_theories thy refs =
  refs |> map_filter (fn (kind, name) =>
    Option.mapPartial (fn space => entry_theory space name) (kind_space thy kind));

(*the constants and types the text refers to, as terms, for their instances; a class parameter's
  class is in its constraint, not its type*)
fun ref_terms thy refs =
  refs |> map_filter (fn (kind, name) =>
    if kind = Markup.constantN then
      Option.map (fn T => Const (name, T)) (try (Consts.the_constraint (Sign.consts_of thy)) name)
    else if kind = Markup.type_nameN then SOME (Free ("x", Type (name, [])))
    else NONE);

fun uses thy texts =
  let
    val thms = own_thms thy;
    val refs = map_filter dest_ref texts;
    val terms = map Thm.prop_of thms @ own_const_terms thy @ ref_terms thy refs;
  in
    proof_theories thy thms @ term_theories thy terms @ ref_theories thy refs
    |> distinct (op =) |> remove (op =) (Context.theory_long_name thy)
  end;

(*per theory, how many names of each space are its own; simp rules by the names of their facts*)
fun context_counts thy =
  let
    fun tally i space names =
      fold (fn a =>
        (case entry_theory space a of
          SOME t => Symtab.map_default (t, [0, 0, 0, 0, 0]) (nth_map i (fn n => n + 1))
        | NONE => I)) names;
    fun all space = Name_Space.get_names space;
    val simps = map (#1 o #1) (Raw_Simplifier.dest_simps (simpset_of (Proof_Context.init_global thy)));
    val counts =
      Symtab.empty
      |> tally 0 (facts_space thy) (all (facts_space thy))
      |> tally 1 (facts_space thy) simps
      |> tally 2 (Sign.const_space thy) (all (Sign.const_space thy))
      |> tally 3 (Sign.type_space thy) (all (Sign.type_space thy))
      |> tally 4 (Sign.class_space thy) (all (Sign.class_space thy));
  in
    Symtab.dest counts
    |> map (fn (t, ns) => space_implode " " (t :: map string_of_int ns))
    |> space_implode ";"
  end;


fun output instance verdict props =
  Output.result ((Markup.instanceN, instance) :: ("verdict", verdict) :: props) [verdict];

fun ms name n = (name, string_of_int n);

fun times ({elapsed, cpu, gc}: Timing.timing) =
  map (fn (name, t) => ms name (Time.toMilliseconds t)) [("ms", elapsed), ("cpu", cpu), ("gc", gc)];

(*cancelled from outside (overlay removed, or every task cancelled when the heap runs out): say so
  before passing the interrupt on, so that the question is not just unanswered*)
fun interrupted instance start exn =
  (Thread_Attributes.uninterruptible_body (fn _ =>
    output instance "interrupted" (times (Timing.result start)));
   Exn.reraise exn);

fun register name check =
  Command.print_function name
    (fn {args = instance :: timeout_ms :: args, ...} =>
      SOME {delay = NONE, pri = 0, persistent = false, strict = false,
        print_fn = fn _ => fn st =>
          let
            val limit = Time.fromMilliseconds (the (Int.fromString timeout_ms));
            val start = Timing.start ();
            val (verdict, props) =
              (*Exn.result would pass interrupts on before we see them*)
              (case Exn.capture (check limit args) st of
                Exn.Res res => res
              | Exn.Exn exn =>
                  if Exn.is_interrupt exn then interrupted instance start exn
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

      (*the second of a pair runs faster, so alternate*)
      fun pair i = if i mod 2 = 1 then (run a, run b) else swap (run b, run a);
      val runs = map pair (1 upto the (Int.fromString n));
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

(*per B: verdict, ms, names A lacks, facts that differ*)
fun compare_run limit st st_a (i, text) =
  let
    val (res, t) = timed limit (run_state st text);
    val k = string_of_int i;
    val time = ms ("ms" ^ k) (Time.toMilliseconds (#elapsed t));
  in
    (case res of
      Exn.Res st_b =>
        let val (differ, reordered) = changed st st_a st_b in
          [("ok" ^ k, "closes"), time, ("missing" ^ k, space_implode " " (missing st_a st_b)),
           ("differ" ^ k, space_implode " " differ), ("reordered" ^ k, space_implode " " reordered)]
        end
    | Exn.Exn exn => [("ok" ^ k, verdict res), time, ("message" ^ k, Runtime.exn_message exn)])
  end;

val _ =
  register "linter_names" (fn limit => fn a :: bs => fn st =>
    let val (res, t) = timed limit (run_state st a) in
      (case res of
        Exn.Res st_a => ("closes", times t @ maps (compare_run limit st st_a) (map_index (apfst (curry op + 1)) bs))
      | Exn.Exn _ => (verdict res, times t))
    end);

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
      [("rules", space_implode " " (Timeout.apply_physical limit (used_rules st text) ())),
       ms "subgoals" (nsubgoals (Toplevel.proof_of st))]));

val _ =
  register "linter_imports" (fn limit => fn refs => fn st =>
    let
      val thy = Toplevel.theory_of st;
      val (used, context) = Timeout.apply_physical limit (fn () => (uses thy refs, context_counts thy)) ();
    in ("closes", [("uses", space_implode " " used), ("context", context)]) end);

val _ =
  register "linter_used_members" (fn limit => fn text :: facts => fn st =>
    let
      val (res, t) = timed limit (used_members st text facts);
      fun used us =
        maps (fn (i, (u, a)) => [("used" ^ string_of_int i, u), ("all" ^ string_of_int i, a)]) (map_index I us);
    in (verdict res, times t @ (case res of Exn.Res us => used us | Exn.Exn _ => [])) end);

val _ =
  register "linter_try_del" (fn limit => fn text :: facts => fn st =>
    let val (res, t) = timed limit (run_on (without_simps facts st) text)
    in (verdict res, times t) end);

end;
