theory Def_Lints_Code
  imports Main
begin

text \<open>What datatype_plugins should find, in a theory that evaluates its datatype.\<close>

(* datatype_plugins: `(plugins del: extraction lifting "quickcheck" size transfer)`; code stays *)
datatype digit = Zero | One | Two

value "[Zero, One, Two]"

end
