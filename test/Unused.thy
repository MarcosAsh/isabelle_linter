theory Unused
  imports Main
begin

text \<open>Each lemma says in a comment what the unused lint should find.\<close>

(* the `using` and the simp fact *)
lemma u1: "rev (rev xs) = xs"
  using append_Nil by (simp add: rev_append)

(* `"y = y"`, reported but not removed; and `using assms` (without `x > 0`, x has no type) *)
lemma u2:
  assumes "x > (0::nat)" and "y = y"
  shows "x + 0 = x"
  using assms by simp

(* both haves and `using h1` *)
lemma u3: "length (xs @ ys) = length ys + length xs"
proof -
  have h1: "length (xs @ ys) = length xs + length ys" by simp
  have h2: "rev [] = ([] :: nat list)" by simp
  show ?thesis using h1 by simp
qed

(* the first apply *)
lemma u4: "P \<longrightarrow> P \<or> Q"
  apply (rule impI)
  apply simp
  done

(* the second metis fact *)
lemma u5: "rev (rev (xs @ ys)) = xs @ ys"
  by (metis rev_rev_ident append_Nil2)

(* nothing *)
lemma u6: "(x::nat) * 2 = x + x"
  by simp

(* nothing: the unnamed corollary needs secret_val, as simp does not unfold secret *)
definition secret :: nat where "secret = 3"

lemma secret_val: "secret = 3"
  by (simp add: secret_def)

corollary "secret + 1 = 4"
  using secret_val by simp

(* the assumption is needed *)
lemma u7:
  assumes "A"
  shows "A \<or> B"
  using assms by simp

(* nothing, though rev_append is not needed: a schematic goal's proof chooses its statement *)
schematic_goal u8: "length [a, b] = ?n"
  by (simp add: rev_append)

end
