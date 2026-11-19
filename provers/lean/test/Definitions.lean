inductive Colour where
  | red | green
  deriving Repr, DecidableEq, Inhabited

structure Point where
  x : Nat
  y : Nat
  deriving Repr

private structure Hidden where
  n : Nat
  deriving BEq

theorem same (c : Colour) : c = c ∨ c = Colour.red := by
  by_cases h : c = Colour.red
  · exact Or.inr h
  · exact Or.inl rfl

def count (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => count k + 1
termination_by n

def halve (n : Nat) : Nat :=
  if h : n < 2 then 0 else halve (n / 2) + 1
termination_by n
decreasing_by omega

def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs
termination_by xs => xs.length
