theory Imports_Test
  imports Imports_Defs Imports_Inst Imports_Other Imports_Syntax Imports_Unused Imports_Later
    Imports_Extra
begin

text \<open>What the unused_imports lint should say about each import of this theory:

  Imports_Defs    imported anyway, via Imports_Inst and Imports_Other: removed
  Imports_Inst    kept: the type instance nat :: pointed, which the prover's view shows
  Imports_Other   kept: quad
  Imports_Syntax  kept: only its notation +++ is used, which only the build shows
  Imports_Unused  not needed: removed, and the ROOT's theories get Imports_Unused, which
                  only this import kept in the session
  Imports_Later   kept: Imports_User needs half
  Imports_Extra   kept: Imports_Ex (session Linter_Imports_Ex) needs twice, which only
                  the build of that session shows\<close>

lemma quad_1: "quad 1 = 4"
  by (simp add: quad_def double_def)

lemma "(point :: nat) = point"
  by simp

lemma "xs +++ [] = xs"
  by simp

end
