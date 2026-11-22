Require Import Arith Lia.

Lemma needed (a b : nat) (h : a = b) : b = a.
Proof.
  assert (h1 : a + 0 = a) by lia.
  symmetry.
  exact h.
Qed.

Lemma bullets (n : nat) : n + 0 = n /\ 0 + n = n.
Proof.
  split.
  - simpl. (* a. comment *)
    lia.
  - pose proof (Nat.add_comm n 0) as unused.
    reflexivity.
Qed.

Lemma keeps (n : nat) (h : 0 < n) : n <> 0.
Proof.
  assert (h' : n <> 0) by lia.
  exact h'.
Qed.
