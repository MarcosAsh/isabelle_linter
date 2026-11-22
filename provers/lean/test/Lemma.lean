import Lean
open Lean

/-- Mathlib's `lemma`, which a server has to treat as a theorem. -/
syntax (name := lemma) declModifiers group("lemma " declId ppIndent(declSig) declVal) : command

@[macro «lemma»] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

lemma as_lemma (n : Nat) : n + 0 = n := by
  have unused : n = n := rfl
  simp

theorem empties (n : Nat) : n + 0 = n := by
  simp [Nat.mul_comm, Nat.mul_assoc]
