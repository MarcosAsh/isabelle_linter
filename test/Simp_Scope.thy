theory Simp_Scope
  imports Main
begin

text \<open>Each lemma says in a comment what simp_scope should find. Unfolding big makes simp
  compute a big numeral, which takes about a second; small is cheap.\<close>

definition big :: "nat \<Rightarrow> nat" where "big n = n * ((2::nat)^300 * 3^200)"
definition small :: "nat \<Rightarrow> nat" where "small n = n + 1"

lemmas sizes = big_def small_def

(* `note defs`: a unfolds big without needing to; b uses `simp add: small_def` *)
lemma ss1: "(P (big x) \<longrightarrow> P (big x)) \<and> small 0 = 1"
proof -
  note defs[simp] = big_def small_def
  have a: "P (big x) \<longrightarrow> P (big x)" by simp
  have b: "small 0 = 1" by simp
  show ?thesis using a b by blast
qed

(* `note [simp] = ...` loses `[simp] =`; show gets small_def, qed nothing *)
lemma ss2: "small 0 = 1 \<and> (P (big x) \<longrightarrow> P (big x))"
proof -
  note [simp] = big_def small_def
  show ?thesis
  proof (rule conjI)
    show "small 0 = 1" by simp
  qed simp
qed

(* nothing: both steps need big_def, so moving it to them gains nothing *)
lemma ss3: "big 0 = 0 \<and> big 1 = (2::nat)^300 * 3^200"
proof -
  note big_def[simp]
  have "big 0 = 0" by simp
  moreover have "big 1 = (2::nat)^300 * 3^200" by simp
  ultimately show ?thesis by blast
qed

(* nothing: `simplified` reads the note's rule, and `rule` cannot be given it *)
lemma ss4:
  assumes "Q (big x) (small x)"
  shows "Q (big x) (Suc x) \<and> big 1 = (2::nat)^300 * 3^200"
proof -
  note small_def[simp]
  have "Q (big x) (Suc x)" by (rule assms[simplified])
  moreover have "big 1 = (2::nat)^300 * 3^200" by (simp add: big_def)
  ultimately show ?thesis by blast
qed

(* `by (simp add: small_def)`: big_def of sizes is not needed *)
lemma ss5: "small (big x) = big x + 1"
  by (simp add: sizes)

(* nothing: the proof needs both theorems of sizes *)
lemma ss6: "small (big 0) = 1"
  by (simp add: sizes)

text \<open>Only with -o simp_scope_theory=true: the [simp] of tiny_def is needed by 1 of the 3 lemmas
  after it (ss7).\<close>

definition tiny :: "nat \<Rightarrow> nat" where "tiny n = n"

declare tiny_def[simp]

lemma ss7: "tiny x = x" by simp

lemma ss8: "x + 0 = (x::nat)" by simp

lemma ss9: "rev [x] = [x]" by simp

end
