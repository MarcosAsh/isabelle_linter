(*  Title:      isabelle_linter/ml/linter_query.ML

Print functions that src/core/pide.scala attaches as overlays. Args: INSTANCE, TIMEOUT_MS, then

  linter_try  METHODS   run `by METHODS` on the goal
  linter_time N A B     run `by A` and `by B` N times each; ms, ms2 are the medians
  linter_run  TEXT      run an edited copy of the lemma from the state before it
*)

structure Linter_Query =
struct

(*a timeout must never count as a failure*)
fun timed limit f =
  let
    val start = Time.now ();
    val res = Exn.result (Timeout.apply limit f) ();
    val ms = Time.toMilliseconds (Time.now () - start);
  in
    (case res of
      Exn.Res () => ("closes", ms)
    | Exn.Exn exn =>
        if Exn.is_interrupt_proper exn then Exn.reraise exn
        else
          (case exn of
            Timeout.TIMEOUT _ => ("timeout", ms)
          | _ => (if String.isSubstring "Timeout" (Runtime.exn_message exn) then "timeout" else "fails", ms)))
  end;

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


fun output instance verdict props =
  Output.result ((Markup.instanceN, instance) :: ("verdict", verdict) :: props) [verdict];

fun ms name n = (name, string_of_int n);

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
    let val (verdict, t) = timed limit (run_by st text) in (verdict, [ms "ms" t]) end);

val _ =
  register "linter_time" (fn limit => fn [n, a, b] => fn st =>
    let
      val runs = map (fn _ => (timed limit (run_by st a), timed limit (run_by st b)))
        (1 upto the (Int.fromString n));
      val ok = forall (fn ((va, _), (vb, _)) => va = "closes" andalso vb = "closes") runs;
    in
      (if ok then "closes" else "fails", [ms "ms" (median (map (#2 o #1) runs)), ms "ms2" (median (map (#2 o #2) runs))])
    end);

val _ =
  register "linter_run" (fn limit => fn [text] => fn st =>
    let val (verdict, t) = timed limit (run_text st text) in (verdict, [ms "ms" t]) end);

end;
