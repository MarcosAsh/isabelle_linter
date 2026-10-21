theory Def_Lints_Use
  imports Def_Lints
begin

lemma "n \<le> sum_upto n"
  by (induction n rule: sum_upto.induct) simp_all

end
