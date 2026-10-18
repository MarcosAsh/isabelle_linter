(*  Title:      isabelle_linter/ml/linter_rule_stats.ML

Print function for an Isabelle built with etc/simpstats.patch. Args: INSTANCE, TIMEOUT_MS, then

  linter_rule_stats TEXT   run the lemma TEXT from the state before it, with the rule statistics
                           on. Each answer is lines of tab-separated fields:
                           rules: the [simp] rules of the context before it that the net offered:
                             name, candidates, matches, rewrites, microseconds in failed tries of
                             a conditional rule, 1 if it is conditional
                           procs: the simprocs called: name, calls, rewrites, microseconds inside
                           classical: the rules the classical reasoner tried ("classical") or the
                             net offered to blast ("blast"): kind, name, tries, unified tries,
                             1 if the lemma's proof uses the rule
                           proved: 1 if the lemma finished, so that its proof is known

TEXT must name the lemma, since an unnamed result is not kept. The counts come back even when
the lemma fails or runs out of time.
*)

structure Linter_Rule_Stats =
struct

fun declare key = "declare [[rule_statistics = " ^ quote key ^ "]]\n";

fun line fields = space_implode "\t" fields;

fun flag b = if b then "1" else "0";

fun us t = string_of_int (Time.toMicroseconds t);


(* the run *)

fun new_facts st0 st =
  let
    fun global_facts s = Global_Theory.facts_of (Toplevel.theory_of s);
    fun local_facts s = Proof_Context.facts_of (Toplevel.context_of s);
    fun added f = Facts.dest_static false [f st0] (f st);
  in maps #2 (added global_facts @ added local_facts) end;

(*the named theorems the lemma's proof uses*)
fun run st0 text () =
  let
    val st = Linter_Query.run_state st0 text ();
    val deps = Thm_Deps.thm_deps (Toplevel.theory_of st) (new_facts st0 st);
  in Thm_Name.Set.make (map #2 deps) end;


(* answer *)

fun kind k (((k', _), _): Rule_Statistics.key * Rule_Statistics.counts) = k = k';

(*a rule without a name hint, like the equations of fun, is "??.unknown"*)
fun named (((_, (name, _)), _): Rule_Statistics.key * Rule_Statistics.counts) =
  not (String.isPrefix "??." name);

(*each [simp] rule, and whether it is conditional; a fact can give several rules*)
fun simp_rules st =
  let
    val simps = Raw_Simplifier.dest_simps (simpset_of (Toplevel.context_of st));
    fun conditional thm c = c orelse Thm.nprems_of thm > 0;
    fun add (name, thm) = Thm_Name.Table.map_default (name, false) (conditional thm);
  in fold add simps Thm_Name.Table.empty end;

fun rule_line simps ((_, name), {tried, matched, succeeded, time}) =
  Thm_Name.Table.lookup simps name |> Option.map (fn conditional =>
    line (Thm_Name.print name :: map string_of_int [tried, matched, succeeded] @
      [us time, flag conditional]));

fun proc_line ((_, (name, _)), {tried, succeeded, time, ...}: Rule_Statistics.counts) =
  line [name, string_of_int tried, string_of_int succeeded, us time];

fun classical_line used ((kind, name), {tried, matched, ...}: Rule_Statistics.counts) =
  line [kind, Thm_Name.print name, string_of_int tried, string_of_int matched,
    flag (Thm_Name.Set.member used name)];

fun statistics st key used =
  let
    val entries = filter named (Rule_Statistics.get key);
    val _ = Rule_Statistics.reset key;
    val classical = filter (fn e => kind "classical" e orelse kind "blast" e) entries;
  in
    [("rules", cat_lines (map_filter (rule_line (simp_rules st)) (filter (kind "simp") entries))),
     ("procs", cat_lines (map proc_line (filter (kind "simproc") entries))),
     ("classical", cat_lines (map (classical_line used) classical))]
  end;

val _ =
  Linter_Query.register "linter_rule_stats" (fn limit => fn [text] => fn st =>
    let
      val key = "linter_rule_stats_" ^ serial_string ();
      val (res, t) = Linter_Query.timed limit (run st (declare key ^ text));
      val used = (case res of Exn.Res u => u | Exn.Exn _ => Thm_Name.Set.empty);
      val proved = ("proved", flag (Exn.is_res res));
    in (Linter_Query.verdict res, proved :: Linter_Query.times t @ statistics st key used) end);

end;
