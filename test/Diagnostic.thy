theory Diagnostic
  imports Main
begin

text \<open>Each command says in a comment what diagnostic_commands should find. -F deletes only the
  exploration commands, and the session must still build afterwards.\<close>

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(* exploration: delete it; -F deletes the line *)
find_theorems "fib (Suc _)"

(* noise: delete it; -F leaves it *)
thm fib.simps

(* test: move it to a test session; -F leaves it *)
value "fib 20"

(* test, compiling SML: move it to a test session; -F leaves it *)
export_code fib checking SML

(* exploration: delete it; -F deletes the quickcheck line and keeps the proof *)
lemma fib_pos: "n > 0 \<Longrightarrow> fib n > 0"
  quickcheck
  by (induction n rule: fib.induct) auto

(* exploration: delete it; -F deletes the whole lemma, as it only explores *)
lemma "fib n \<ge> n"
  nitpick
  oops

(* test, as it expects a counterexample: move it to a test session; -F leaves it *)
lemma "fib n > n"
  quickcheck [expect = counterexample]
  oops

end
