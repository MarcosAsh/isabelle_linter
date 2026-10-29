(*  Title:      isabelle_linter/ml/linter_simproc.ML

Print function for HOL sessions: the cost of the simproc datatype_no_proper_subterm on a step.

  linter_simproc_variants N RUN_MS M  run `by M` once untimed, then N rounds of three variants
      in rotating order: 0 as is, 1 without the simproc, 2 with Cached_No_Proper_Subterm in its
      place; then once with the simproc wrapped in a counter. verdictI, msI, cpuI, gcI, runsI as
      in linter_times_without; calls, hits (calls that rewrote), inside_ms (wall time inside the
      simproc) and step_ms (that run's wall time)

RUN_MS limits each run.
*)

structure Cached_No_Proper_Subterm =
struct

val forbidden_types =
  [\<^type_name>\<open>bool\<close>, \<^type_name>\<open>nat\<close>, \<^type_name>\<open>prod\<close>,
   \<^type_name>\<open>sum\<close>, \<^type_name>\<open>list\<close>, \<^type_name>\<open>option\<close>];

val size_neq_imp_neq_thm = @{thm HOL.Eq_FalseI[OF size_neq_size_imp_neq]};

fun contains_datatypes T_names =
  let
    fun go (Type (s, Ts)) = (member op = T_names s andalso forall is_TVar Ts) orelse exists go Ts
      | go _ = false;
  in go end;

fun mk_ctor T_names t =
  (dest_Const_name t, map (contains_datatypes T_names) (fst (strip_type (fastype_of t))));

fun ctors_of (sugar : BNF_FP_Def_Sugar.fp_sugar) T_names =
  map (Thm.concl_of #> Logic.dest_equals #> fst #> mk_ctor T_names) (#ctr_defs (#fp_ctr_sugar sugar));

(*size equations and the constructors of the type and its mutual types*)
fun lookup ctxt T_name =
  (case (BNF_FP_Def_Sugar.fp_sugar_of ctxt T_name, BNF_LFP_Size.size_of ctxt T_name) of
    (SOME sugar, SOME (_, (_, size_eqs, _))) =>
      let
        val mutuals = map dest_Type_name (#Ts (#fp_res sugar));
        val sugars = map (BNF_FP_Def_Sugar.fp_sugar_of ctxt) mutuals;
      in
        if exists is_none sugars then NONE
        else SOME (size_eqs, maps (fn s => ctors_of (the s) mutuals) sugars)
      end
  | _ => NONE);

fun cached cache ctxt T_name =
  (case Symtab.lookup (Synchronized.value cache) T_name of
    SOME info => info
  | NONE =>
      let val info = lookup ctxt T_name
      in Synchronized.change cache (Symtab.update (T_name, info)); info end);

fun is_comb (_ $ _) = true
  | is_comb _ = false;

fun is_subterm ctors s t =
  let
    fun go t = s aconv t orelse (is_comb t andalso go' (strip_comb t))
    and go' (Const (c, _), ts) =
          (case AList.lookup op = ctors c of
            NONE => false
          | SOME poss => exists (fn (b, t) => b andalso go t) (poss ~~ ts))
      | go' _ = false;
  in go t end;

fun proc cache ctxt ct =
  let
    val (clhs, crhs) = Thm.dest_binop ct;
    val (lhs, rhs) = apply2 Thm.term_of (clhs, crhs);
    val cT = Thm.ctyp_of_cterm clhs;
    val (T_name, _) = dest_Type (Thm.typ_of cT);
  in
    if member op = forbidden_types T_name orelse lhs aconv rhs then NONE
    else
      (case cached cache ctxt T_name of
        NONE => NONE
      | SOME (size_eqs, ctors) =>
          if not (is_subterm ctors lhs rhs) andalso not (is_subterm ctors rhs lhs) then NONE
          else
            size_neq_imp_neq_thm
            |> Drule.instantiate'_normalize [SOME cT] [SOME clhs, SOME crhs]
            |> rewrite_goals_rule ctxt (map (fn thm => thm RS @{thm eq_reflection}) size_eqs)
            |> Tactic.rule_by_tactic ctxt (HEADGOAL (Lin_Arith.simple_tac ctxt))
            |> SOME)
  end
  handle CTERM _ => NONE | TERM _ => NONE | TYPE _ => NONE | THM _ => NONE;

(*the pattern's variables must be schematic: a proof context may fix 'a, x or y*)
fun global ctxt = Proof_Context.init_global (Proof_Context.theory_of ctxt);

(*a fresh instance has an empty cache: make one per proof attempt*)
fun simproc ctxt =
  let val cache = Synchronized.var "no_proper_subterm" Symtab.empty in
    Simplifier.make_simproc (global ctxt)
      {name = "datatype_no_proper_subterm_cached", kind = Simplifier.Simproc,
       lhss = [\<^term>\<open>(x :: 'a :: size) = y\<close>], proc = fn _ => proc cache, identifier = []}
  end;

end;

structure Linter_Simproc =
struct

val simproc_name = "datatype_no_proper_subterm";

fun counting_simproc ctxt counter =
  Simplifier.make_simproc (Cached_No_Proper_Subterm.global ctxt)
    {name = "datatype_no_proper_subterm_counted", kind = Simplifier.Simproc,
     lhss = [\<^term>\<open>(x :: 'a :: size) = y\<close>],
     proc = fn _ => fn ctxt => fn ct =>
      let
        val start = Time.now ();
        val res = Datatype_Simprocs.no_proper_subterm_proc ctxt ct;
        val t = Time.now () - start;
        val hit = if is_some res then 1 else 0;
      in Synchronized.change counter (fn (n, k, d) => (n + 1, k + hit, d + t)); res end,
     identifier = []};

fun states pre =
  let
    val ctxt = Proof.context_of pre;
    val proc = #2 (Simplifier.check_simproc ctxt (simproc_name, Position.none));
    val without = Proof.map_context (Raw_Simplifier.del_proc proc) pre;
    fun replaced simproc = Proof.map_context (fn ctxt => Raw_Simplifier.add_proc (simproc ctxt) ctxt) without;
  in (without, replaced) end;

fun rotate 1 (a, b, c) = [(0, a), (1, b), (2, c)]
  | rotate 2 (a, b, c) = [(1, b), (2, c), (0, a)]
  | rotate _ (a, b, c) = [(2, c), (0, a), (1, b)];

fun variants limit n text st =
  let
    val pre = Toplevel.proof_of st;
    val (without, replaced) = states pre;
    fun run state = Linter_Query.timed limit (Linter_Query.run_on state text);
    val _ = run pre;
    (*a fresh cache per run, as a fresh simproc instance per proof would have*)
    fun round i =
      rotate (i mod 3 + 1)
        (fn () => run pre, fn () => run without, fn () => run (replaced Cached_No_Proper_Subterm.simproc))
      |> map (fn (j, f) => (j, f ()));
    val rounds = maps round (1 upto n);
    fun runs j = map #2 (filter (fn (k, _) => k = j) rounds);

    val counter = Synchronized.var "counter" (0, 0, Time.zeroTime);
    val (res, t) = run (replaced (fn ctxt => counting_simproc ctxt counter));
    val (calls, hits, inside) = Synchronized.value counter;
  in
    maps (fn j => Linter_Query.round_fields j (runs j)) [0, 1, 2] @
    [("calls", string_of_int calls), ("hits", string_of_int hits),
     Linter_Query.ms "inside_ms" (Time.toMilliseconds inside),
     Linter_Query.ms "step_ms" (Time.toMilliseconds (#elapsed t)),
     ("counted_verdict", Linter_Query.verdict res)]
  end;

val _ =
  Linter_Query.register "linter_simproc_variants" (fn _ => fn [n, run_ms, text] => fn st =>
    ("closes",
      variants (Time.fromMilliseconds (the (Int.fromString run_ms))) (the (Int.fromString n)) text st));

end;
