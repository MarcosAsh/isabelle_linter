theory Imports_Defs
  imports Main
begin

definition double :: "nat \<Rightarrow> nat" where "double n = n + n"

class pointed =
  fixes point :: 'a

end
