theory Simp_Hygiene
  imports Main
begin

text \<open>Each declaration says in a comment what simp_hygiene should find with
  -o simp_hygiene_min=100. It needs the patched Isabelle. It also reports what HOL itself tries
  here for nothing: the [simp] rules INF_bool_eq, SUP_bool_eq, split_eta_SetCompr,
  split_eta_SetCompr2 and unit_abs_eta_conv, whose left-hand sides the net treats as variables,
  so that they are offered for every term (about 12000 times) and never match; the simprocs
  Record.update and Record.select_update (called on every term), Record.eq and HOL.neq (on every
  equation); and the classical rule Set.psubsetI, tried on the goals `good (f a)` below and never
  unified. Unused and faster_step find nothing.\<close>

definition pair :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "pair x y = x"

consts special :: "'a \<Rightarrow> bool"

fun pairs :: "'a list \<Rightarrow> 'a list" where
  "pairs (x # y # xs) = pair x y # pairs (y # xs)"
| "pairs xs = xs"

(* offered often, never matched: no lemma below pairs a term with itself *)
lemma pair_same [simp]: "pair x x = x"
  by (simp add: pair_def)

(* condition tried often, never held, so it never rewrote *)
lemma pair_eq [simp]: "y = x \<Longrightarrow> pair x y = y"
  by (simp add: pair_def del: pair_same)

(* condition tried often, held only in the last lemma *)
lemma pair_special [simp]: "special x \<Longrightarrow> pair x y = x"
  by (simp add: pair_def)

(* called often, never rewrote *)
simproc_setup pair_idle ("pair x y") = \<open>K (K (K NONE))\<close>

(* nothing: offered only by one lemma, under the threshold *)
lemma pairs_pair [simp]: "pairs [pair x y] = [pair x y]"
  by simp

(* nothing: pairs.simps rewrites *)
lemma "length (pairs [a, b, c, d, e, f, g, h, i, j, k, l, m, n, p, q, r, s, t, u]) = 20"
  by simp

lemma "pairs [a, b, c, d, e, f, g, h, i, j, k, l, m, n, p, q, r, s, t, u] \<noteq> []"
  by simp

lemma "hd (pairs [a, b, c, d, e, f, g, h, i, j, k, l, m, n, p, q, r, s, t, u]) = pair a b"
  by simp

lemma "last (pairs [a, b, c, d, e, f, g, h, i, j, k, l, m, n, p, q, r, s, t, u]) = u"
  by simp

lemma "rev (pairs [a, b, c, d, e, f, g, h, i, j]) = rev (pairs [a, b, c, d, e, f, g, h, i, j])"
  by simp

lemma "pairs [pair a b] = [pair a b]"
  by simp

lemma "special a \<Longrightarrow> pairs [a, b, c] = [a, pair b c, c]"
  by simp


definition good :: "'a list \<Rightarrow> bool" where "good xs \<longleftrightarrow> xs \<noteq> []"

(* nothing: in every proof below *)
lemma good_Cons [intro!]: "good (x # xs)"
  by (simp add: good_def)

(* tried often, in no proof: its premise never holds below *)
lemma good_length [intro]: "length xs > 1 \<Longrightarrow> good xs"
  by (auto simp: good_def)

lemma "good xs \<or> good (a # xs)"
  by blast

lemma "\<forall>x. good (f x) \<Longrightarrow> good (f a)"
  by blast

lemma "\<forall>x y. good (g x y) \<Longrightarrow> good (g a b) \<and> good (g b a)"
  by blast

lemma "\<forall>x. good (f x) \<Longrightarrow> good (f a) \<and> good (f b)"
  by fast

lemma "\<forall>x y. good (g x y) \<Longrightarrow> good (g a b) \<or> good c"
  by force

lemma "\<forall>x. good (f x) \<Longrightarrow> \<forall>x. good (h x) \<Longrightarrow> good (f a) \<and> good (h b)"
  by auto

lemma "\<forall>x. good (f x) \<Longrightarrow> \<forall>x. good (h x) \<Longrightarrow> good (h a) \<and> good (f b)"
  by fastforce

lemma "\<forall>x. good (f x) \<Longrightarrow>
    good (f a) \<and> good (f b) \<and> good (f c) \<and> good (f d) \<and> good (f e) \<and> good (f g) \<and>
    good (f i) \<and> good (f j) \<and> good (f k) \<and> good (f l) \<and> good (f m) \<and> good (f n) \<and>
    good (f p) \<and> good (f q) \<and> good (f r) \<and> good (f s) \<and> good (f t) \<and> good (f u) \<and>
    good (f v) \<and> good (f w) \<and> good (f y) \<and> good (f z)"
  by blast

lemma "\<forall>x. good (f x) \<Longrightarrow>
    good (f a) \<and> good (f b) \<and> good (f c) \<and> good (f d) \<and> good (f e) \<and> good (f g) \<and>
    good (f i) \<and> good (f j) \<and> good (f k) \<and> good (f l) \<and> good (f m) \<and> good (f n) \<and>
    good (f p) \<and> good (f q) \<and> good (f r) \<and> good (f s) \<and> good (f t) \<and> good (f u) \<and>
    good (f v) \<and> good (f w) \<and> good (f y) \<and> good (f z)"
  by fast

lemma "\<forall>x. good (f x) \<Longrightarrow>
    good (f a) \<and> good (f b) \<and> good (f c) \<and> good (f d) \<and> good (f e) \<and> good (f g) \<and>
    good (f i) \<and> good (f j) \<and> good (f k) \<and> good (f l) \<and> good (f m) \<and> good (f n) \<and>
    good (f p) \<and> good (f q) \<and> good (f r) \<and> good (f s) \<and> good (f t) \<and> good (f u) \<and>
    good (f v) \<and> good (f w) \<and> good (f y) \<and> good (f z)"
  by best

lemma "\<forall>x. good (h x) \<Longrightarrow>
    good (h a) \<and> good (h b) \<and> good (h c) \<and> good (h d) \<and> good (h e) \<and> good (h g) \<and>
    good (h i) \<and> good (h j) \<and> good (h k) \<and> good (h l) \<and> good (h m) \<and> good (h n) \<and>
    good (h p) \<and> good (h q) \<and> good (h r) \<and> good (h s) \<and> good (h t) \<and> good (h u) \<and>
    good (h v) \<and> good (h w) \<and> good (h y) \<and> good (h z)"
  by blast

lemma "\<forall>x. good (h x) \<Longrightarrow>
    good (h a) \<and> good (h b) \<and> good (h c) \<and> good (h d) \<and> good (h e) \<and> good (h g) \<and>
    good (h i) \<and> good (h j) \<and> good (h k) \<and> good (h l) \<and> good (h m) \<and> good (h n) \<and>
    good (h p) \<and> good (h q) \<and> good (h r) \<and> good (h s) \<and> good (h t) \<and> good (h u) \<and>
    good (h v) \<and> good (h w) \<and> good (h y) \<and> good (h z)"
  by fast

end
