theory Used_Facts
  imports Main
begin

lemma f1: "A \<subseteq> B \<Longrightarrow> B \<inter> C \<subseteq> D \<Longrightarrow> A \<inter> C \<subseteq> D"
  by force

lemma f2: "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> \<exists>y \<in> set xs. P y"
  by auto

lemma f3: "sorted (xs @ [x]) \<Longrightarrow> sorted xs"
  by (auto simp: sorted_append)

lemma f4: "distinct xs \<Longrightarrow> distinct (filter P xs)"
  by auto

lemma f5: "set (rev xs @ ys) = set ys \<union> set xs"
  by auto

lemma f6: "finite A \<Longrightarrow> finite B \<Longrightarrow> card (A \<union> B) \<le> card A + card B"
  by (auto intro: card_Un_le)

end
