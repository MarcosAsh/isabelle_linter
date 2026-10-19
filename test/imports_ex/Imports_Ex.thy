theory Imports_Ex
  imports Linter_Imports.Imports_Test
begin

lemma "twice [] = []"
  by (simp add: twice_def)

end
