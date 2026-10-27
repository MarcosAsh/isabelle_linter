theory Def_Lints
  imports Main
begin

text \<open>Each definition says in a comment what datatype_plugins or fun_to_primrec should find. Both
  look at the text after the definition, here and in Def_Lints_Use, which imports this theory.
  Run with -o fun_slow=0.3 for the slow fun.\<close>

(* datatype_plugins: `(plugins del: code extraction lifting "quickcheck" size transfer)` *)
datatype colour = Red | Green | Blue

lemma "Red \<noteq> Green"
  by simp

(* datatype_plugins: `(plugins del: code extraction lifting "quickcheck" transfer)`; size stays *)
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

(* fun_to_primrec: nothing, as a lemma below uses mirror.induct *)
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Leaf = Leaf"
| "mirror (Node l x r) = Node (mirror r) x (mirror l)"

lemma "mirror (mirror t) = t"
  by (induction t rule: mirror.induct) simp_all

(* fun_to_primrec: `primrec`, one equation per constructor and recursion on the list *)
fun len :: "'a list \<Rightarrow> nat" where
  "len [] = 0"
| "len (x # xs) = Suc (len xs)"

lemma "len (xs @ ys) = len xs + len ys"
  by (induction xs) simp_all

(* fun_to_primrec: nothing, as Def_Lints_Use uses sum_upto.induct *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

(* fun_to_primrec: nothing, the patterns are nested *)
fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

(* fun_to_primrec: nothing, the patterns overlap *)
fun is_zero :: "nat \<Rightarrow> bool" where
  "is_zero 0 = True"
| "is_zero n = False"

(* datatype_plugins: `(plugins del: code extraction lifting "quickcheck" transfer)`; size stays *)
datatype suit = Hearts | Diamonds | Clubs | Spades

(* fun_to_primrec: slow fun, mostly its pattern proof; stays, patterns on several arguments *)
fun beats :: "suit \<Rightarrow> suit \<Rightarrow> suit \<Rightarrow> bool" where
  "beats Hearts Hearts _ = False"
| "beats Hearts Diamonds Hearts = True"
| "beats Hearts Diamonds Diamonds = False"
| "beats Hearts Diamonds Clubs = True"
| "beats Hearts Diamonds Spades = False"
| "beats Diamonds Clubs Hearts = True"
| "beats Diamonds Clubs Diamonds = False"
| "beats Diamonds Clubs Clubs = True"
| "beats Diamonds Clubs Spades = False"
| "beats Clubs Spades Hearts = True"
| "beats Clubs Spades Diamonds = False"
| "beats Clubs Spades Clubs = True"
| "beats Clubs Spades Spades = False"
| "beats Spades Hearts Hearts = True"
| "beats Spades Hearts Diamonds = False"
| "beats Spades Hearts Clubs = True"
| "beats Spades Hearts Spades = False"
| "beats _ _ _ = False"

end
