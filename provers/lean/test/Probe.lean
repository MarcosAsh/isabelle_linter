def AlwaysTrue (n : Nat) : Prop := n = n
def NeverTrue (n : Nat) : Bool := n < 0
def Even' (n : Nat) : Prop := n % 2 = 0

theorem vac (n : Nat) (h1 : n < 2) (h2 : n > 5) : n = 7 := by omega
theorem vac' : ∀ n : Nat, n < 2 → n > 5 → n = 7 := by omega
theorem fine (n : Nat) (h : n < 2) : n < 3 := by omega
theorem neg (n : Nat) : ¬ (n + 1 = 0) := by omega
theorem refute (n : Nat) (h : n + 1 = 0) : False := by omega
