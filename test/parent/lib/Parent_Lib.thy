theory Parent_Lib
  imports Main
begin

text \<open>A library session. Linter_Parent_Client imports it through its \<open>sessions\<close> clause, so
  every build of the client checks this theory again.\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

lemma sum_upto_closed: "2 * sum_upto n = n * Suc n"
  by (induction n) auto

lemma sum_upto_mono: "m \<le> n \<Longrightarrow> sum_upto m \<le> sum_upto n"
  by (induction n) (auto simp: le_Suc_eq)

end
