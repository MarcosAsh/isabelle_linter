theory Interp
  imports Main
begin

text \<open>A proof inside an interpretation is not a lemma: unused must not touch it.\<close>

locale le_check =
  fixes f :: "nat \<Rightarrow> nat"
  assumes mono: "x \<le> y \<Longrightarrow> f x \<le> f y"

context
begin

(* nothing: without `that` the `show` fails *)
interpretation id_check: le_check "\<lambda>n. n"
proof
  show "(\<lambda>n. n) x \<le> (\<lambda>n. n) y" if "x \<le> y" for x y :: nat
    using that by simp
qed

end

end
