theory Example
  imports Main
begin

lemma l1: "(x::nat) + y + z = z + y + x"
  by (smt (verit) add.commute add.assoc)

lemma l2: "(a::int) * (b + c) - a * c = a * b"
  by (smt (verit) distrib_left)

lemma l3: "rev (xs @ ys @ zs) = rev zs @ rev ys @ rev xs"
  by (metis append_assoc rev_append)

lemma l4: "(x::nat) < 10 \<Longrightarrow> x * 2 < 20"
  by presburger

lemma l5: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P a \<Longrightarrow> Q a"
  by force

lemma l6: "length (map f (filter P xs)) \<le> length xs"
  by (auto simp: length_filter_le)

lemma l7: "(a::int)^2 + 2*a*b + b^2 = (a + b)^2"
  by (smt (verit) power2_sum)

lemma l8: "finite A \<Longrightarrow> card (A \<union> B) \<le> card A + card B"
  by (metis card_Un_le)

lemma l9: "(\<Sum>i<n. (2::nat) * i + 1) = n^2"
  by (induct n) (auto simp: power2_eq_square)

end
