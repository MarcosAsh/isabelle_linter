Require Import Arith Lia.
Require Import List Bool.

Check Nat.add_comm.

Lemma slow (n : nat) : n = n.
Proof.
  do 3000000 idtac; reflexivity.
Qed.

Lemma facts (a b : nat) (h : b = a) : b + 0 = a.
Proof.
  rewrite Nat.add_0_r, h.
  auto using Nat.add_comm, Nat.le_refl with arith.
Qed.

Lemma scoped (n : nat) : n + 0 = n.
Proof.
  Open Scope bool_scope.
  apply Nat.add_0_r.
  Close Scope bool_scope.
Qed.

Compute 2 + 2.
