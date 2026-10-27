theory Simp_Only
  imports Main
begin

text \<open>Each lemma says in a comment what faster_step should find. The full simpset takes about
  a second on the big numerals, the rules the proof used a few ms.\<close>

definition sq :: "nat \<Rightarrow> nat" where "sq n = n * n"

(* `by (simp only: simp_thms(6) add.right_neutral ... power_numeral)` *)
lemma s1: "g (x + (0::nat)) ((2::nat)^200 * 3^150) = g x ((2::nat)^200 * 3^150)"
  by simp

(* `by (simp only: ... power_numeral sq_def)`: a fact of the method is kept *)
lemma s2: "h (sq (x + 0)) ((2::nat)^200 * 3^150) = h (x * x) ((2::nat)^200 * 3^150)"
  by (auto simp: sq_def)

(* `by (simp only: simp_thms(6) add.commute ... power_numeral)`: add.commute is no simp rule,
  but the method names it *)
lemma s3: "g (x + y + (0::nat)) ((2::nat)^200 * 3^150) = g (y + x) ((2::nat)^200 * 3^150)"
  by (simp add: add.commute)

(* `by (induct xs) (simp_all only: ... length_map)`: the induction stays *)
lemma s4: "length (map f xs) * ((2::nat)^200 * 3^150) = length xs * ((2::nat)^200 * 3^150)"
  by (induct xs) auto

(* nothing: simp proves `x + y = y + x` with a simproc, which `simp only:` lacks *)
lemma s5: "(x + y + (0::nat) = y + x) = ((2::nat)^200 * 3^150 > 0)"
  by simp

datatype \<Gamma> = G1 | G2 nat

(* `by (simp only: ... \<Gamma>.inject ...)`: rule names stay in symbol form, not Unicode *)
lemma s6: "g (G2 (x + 0) = G2 y) ((2::nat)^200 * 3^150) = g (x = y) ((2::nat)^200 * 3^150)"
  by simp

end
