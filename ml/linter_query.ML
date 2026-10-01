(*  Title:      isabelle_linter/ml/linter_query.ML

The prover side of src/core/pide.scala: one print function that Scala attaches as a document
overlay to the command before a `by` step. It runs on that command's result state, i.e. the goal
the step has to solve; nothing else in the theory is re-checked.

  overlay "linter_try" with args [INSTANCE, TIMEOUT_MS, METHODS]

runs `by METHODS` with a time limit and reports one result message with properties
instance = INSTANCE, verdict = closes|fails|timeout and ms = elapsed milliseconds. The body starts
with the verdict, because the protocol drops empty messages.
*)

structure Linter_Query =
struct

fun parse_by thy text =
  let
    val keywords = Thy_Header.get_keywords thy;
    val toks = Token.explode keywords Position.none text |> filter Token.is_proper;
  in
    (case Scan.read Token.stopper (Method.parse -- Scan.option Method.parse) toks of
      SOME methods => methods
    | NONE => error ("Cannot parse proof methods " ^ quote text))
  end;

(*a toplevel goal is at the bottom of the proof stack*)
fun run_by st text =
  let
    val pre = Toplevel.proof_of st;
    val methods = parse_by (Proof.theory_of pre) text;
  in
    if can (Proof.assert_bottom true) pre
    then ignore (Proof.global_terminal_proof methods pre)
    else ignore (Proof.local_terminal_proof methods pre)
  end;

(*a timeout must never count as a failure of the method*)
fun try_by st limit text =
  let
    val start = Time.now ();
    val res = Exn.result (Timeout.apply limit (run_by st)) text;
    val ms = Time.toMilliseconds (Time.now () - start);
  in
    (case res of
      Exn.Res () => ("closes", ms, "")
    | Exn.Exn exn =>
        if Exn.is_interrupt_proper exn then Exn.reraise exn
        else
          let
            val msg = Runtime.exn_message exn;
            val verdict =
              (case exn of
                Timeout.TIMEOUT _ => "timeout"
              | _ => if String.isSubstring "Timeout" msg then "timeout" else "fails");
          in (verdict, ms, Protocol_Message.clean_output msg) end)
  end;

val _ =
  Command.print_function "linter_try"
    (fn {args = [instance, timeout_ms, text], ...} =>
      SOME {delay = NONE, pri = Task_Queue.urgent_pri, persistent = false, strict = false,
        print_fn = fn _ => fn st =>
          let
            val (verdict, ms, detail) =
              if Toplevel.is_proof st
              then try_by st (Time.fromMilliseconds (the (Int.fromString timeout_ms))) text
              else ("fails", 0, "no proof state");
          in
            Output.result
              [(Markup.instanceN, instance), ("verdict", verdict), ("ms", string_of_int ms)]
              [cat_lines (verdict :: (if detail = "" then [] else [detail]))]
          end}
    | _ => NONE);

end;
