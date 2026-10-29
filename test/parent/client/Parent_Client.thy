theory Parent_Client
  imports Linter_Parent_Lib.Parent_Lib
begin

text \<open>linter_parent should suggest Linter_Parent_Lib as the parent of this session.\<close>

lemma "sum_upto 4 = 10"
  by (simp add: eval_nat_numeral)

end
