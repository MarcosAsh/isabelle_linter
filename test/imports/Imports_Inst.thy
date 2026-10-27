theory Imports_Inst
  imports Imports_Defs
begin

instantiation nat :: pointed
begin

definition "point = (0 :: nat)"

instance ..

end

end
