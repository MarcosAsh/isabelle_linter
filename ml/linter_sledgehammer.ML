(*  Title:      isabelle_linter/ml/linter_sledgehammer.ML

Print function for HOL sessions that runs Sledgehammer on a step's goal, for linter_collect.
*)

structure Linter_Sledgehammer =
struct

(*Half the time goes to the provers, the rest to preplay.*)
fun params thy limit provers =
  Sledgehammer_Commands.default_params thy
    ([("timeout", Value.print_real (Time.toReal limit / 2.0)), ("isar_proofs", "false"),
      ("falsify", "false")] @
      (if provers = "" then [] else [("provers", provers)]));

fun not_chained (_, (sc, _)) = sc <> ATP_Problem_Generate.Chained;

fun text meth names = Sledgehammer_Proof_Methods.string_of_proof_method names meth;

fun played (meth, (Sledgehammer_Proof_Methods.Played _, facts)) =
      SOME (text meth (facts |> filter not_chained |> map (Pretty.pure_string_of o fst)))
  | played _ = NONE;

(*Tactic provers like simp have nothing to preplay: their method is the proof.*)
fun method (Sledgehammer.SH_Some ({preferred_methss = (meth, []), used_facts, ...}, [])) =
      SOME (text meth (used_facts |> filter not_chained |> map fst))
  | method (Sledgehammer.SH_Some (_, preplays)) = get_first played preplays
  | method _ = NONE;

fun sledgehammer limit provers state () =
  let
    val (_, (outcome, _)) =
      Sledgehammer.run_sledgehammer (params (Proof.theory_of state) limit provers)
        Sledgehammer_Prover.Normal (SOME (K ())) 1 Sledgehammer_Fact.no_fact_override state;
  in method outcome end;

(*linter_sledgehammer PROVERS: Sledgehammer with the space-separated PROVERS, or its defaults if
  empty; method is the proof it found.*)
val _ =
  Linter_Query.register "linter_sledgehammer" (fn limit => fn [provers] => fn st =>
    let val (res, t) = Linter_Query.timed limit (sledgehammer limit provers (Toplevel.proof_of st)) in
      (case res of
        Exn.Res (SOME m) => ("closes", ("method", m) :: Linter_Query.times t)
      | Exn.Res NONE => ("fails", Linter_Query.times t)
      | _ => (Linter_Query.verdict res, Linter_Query.times t))
    end);

end;
