theorem needed (a b : Nat) (h : a = b) : b = a := by
  have h1 : a + 0 = a := by simp
  have h2 : b = a := h.symm
  exact h2

theorem lists (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  have unused : xs.length = xs.length := rfl
  simp [List.length_append, Nat.add_comm, List.length_nil]

theorem one_lemma (n : Nat) : n + 0 = n := by
  simp [Nat.mul_comm]

theorem keeps (n : Nat) (h : 0 < n) : n ≠ 0 := by
  have h' : n ≠ 0 := Nat.pos_iff_ne_zero.mp h
  exact h'

#check Nat.add_comm

#eval (List.range 2000).foldl (· + ·) 0

theorem slow_step (a b c d : Nat) (h : a + 2 * b = 3 * c + 1) (h' : c = d + b) : a + 2 * b = 3 * (d + b) + 1 := by
  simp_all
