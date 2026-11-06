import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.ConnectiveCombination
import Attach
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Lemma 7.6.1 (helper): literal_cinstance_eq
-- ===================================================================

/-- Helper: A c-instance of a literal (atomic or negated atomic) must
equal the literal itself, since literals have no sub-structure to
instantiate. -/
theorem literal_cinstance_eq {L : Language}
    (A : FormulaN L)
    (hLit : A.isAtomic ∨ (∃ B, A = .neg B ∧ B.isAtomic))
    (K : FormulaN L)
    (hK : isCInstanceOf K A) : K = A := by
-- BEGIN PROOF
  obtain ⟨ci, hsrc, hform, _hwf⟩ := hK
  cases ci with
  | atom C hC =>
    have hs : C = A := hsrc
    have hf : C = K := by unfold CInstance.toFormula at hform; exact hform
    rw [← hf, hs]
  | negAtom C hC =>
    have hs : FormulaN.neg C = A := hsrc
    have hf : FormulaN.neg C = K := by
      unfold CInstance.toFormula at hform; exact hform
    rw [← hf, hs]
  | connective star C' D' _ _ =>
    -- ci.source = .conj C' D' (star = true) or .disj C' D' (star = false).
    -- hsrc equates this to A, but A is a literal — constructor mismatch.
    rcases hLit with hAtom | ⟨B, hNeg, _⟩
    · cases star with
      | true =>
        have hs : FormulaN.conj C' D' = A := by
          have := hsrc; unfold CInstance.source at this; exact this
        rw [← hs] at hAtom
        simp [FormulaN.isAtomic] at hAtom
      | false =>
        have hs : FormulaN.disj C' D' = A := by
          have := hsrc; unfold CInstance.source at this; exact this
        rw [← hs] at hAtom
        simp [FormulaN.isAtomic] at hAtom
    · subst hNeg
      cases star with
      | true =>
        have hs : FormulaN.conj C' D' = FormulaN.neg B := by
          have := hsrc; unfold CInstance.source at this; exact this
        exact absurd hs (by intro h; cases h)
      | false =>
        have hs : FormulaN.disj C' D' = FormulaN.neg B := by
          have := hsrc; unfold CInstance.source at this; exact this
        exact absurd hs (by intro h; cases h)
  | forallInst x C' _ _ _ _ _ _ =>
    -- ci.source = .all x C', but A is a literal — constructor mismatch.
    rcases hLit with hAtom | ⟨B, hNeg, _⟩
    · have hs : FormulaN.all x C' = A := by
        have := hsrc; unfold CInstance.source at this; exact this
      rw [← hs] at hAtom
      simp [FormulaN.isAtomic] at hAtom
    · subst hNeg
      have hs : FormulaN.all x C' = FormulaN.neg B := by
        have := hsrc; unfold CInstance.source at this; exact this
      exact absurd hs (by intro h; cases h)

-- ===================================================================
-- Lemma 7.6.1: g2nnfCInstanceCombination
-- ===================================================================

/-- Lemma 7.6.1, connective case: combine the two component witnesses
using induction hypotheses in the same G1 calculus as the conclusion.
The language branches are separate, with the equality branch in G1nnf=. -/
theorem cInstance_combination_connective {L : Language}
    [DecidableEq (FormulaN L)]
    (B C : FormulaN L) (isConj : Bool)
    (A : FormulaN L)
    (hA : A = if isConj then FormulaN.conj B C else FormulaN.disj B C)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K A) (hL : isCInstanceOf Ls A) :
    (∀ hNoEq : L.withoutEquality,
      (∀ K' Ls', isCInstanceOf K' B → isCInstanceOf Ls' B →
        ∃ D, isCInstanceOf D B ∧
          Nonempty (G1nnfProofTree hNoEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      (∀ K' Ls', isCInstanceOf K' C → isCInstanceOf Ls' C →
        ∃ D, isCInstanceOf D C ∧
          Nonempty (G1nnfProofTree hNoEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      ∃ D, isCInstanceOf D A ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      (∀ K' Ls', isCInstanceOf K' B → isCInstanceOf Ls' B →
        ∃ D, isCInstanceOf D B ∧
          Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      (∀ K' Ls', isCInstanceOf K' C → isCInstanceOf Ls' C →
        ∃ D, isCInstanceOf D C ∧
          Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      ∃ D, isCInstanceOf D A ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) := by
  -- REPAIR(T7-79): proof pending (G1nnf/G1nnf= connective combination).
  sorry

/-- Lemma 7.6.1, universal case: concatenate the ordered nonempty
instantiation families. The right-nested resulting c-instance implies the
grouped conjunction in G1nnf or G1nnf= for the respective language branch. -/
theorem cInstance_combination_universal {L : Language}
    [DecidableEq (FormulaN L)]
    (x : Nat) (C : FormulaN L) (K Ls : FormulaN L)
    (hK : isCInstanceOf K (FormulaN.all x C))
    (hL : isCInstanceOf Ls (FormulaN.all x C)) :
    (∀ hNoEq : L.withoutEquality,
      ∃ D, isCInstanceOf D (FormulaN.all x C) ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      ∃ D, isCInstanceOf D (FormulaN.all x C) ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) := by
  -- REPAIR(T7-79): proof pending (G1nnf/G1nnf= universal combination).
  sorry

/-- Lemma 7.6.1, existence assertion: for any two c-instances K and Ls
of an NNF Skolem-normal sentence B, a c-instance D proves D -> (K and Ls)
in G1nnf when the language has no equality, and in G1nnf= when it does.
The same repaired c-instance relation is used in both branches. The
computable combination realization is deferred under OD-A17. -/
@[blueprint "chap7__lemma_7_6_1" (main := true)]
theorem cInstance_combination {L : Language}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L) (hNNF : FormulaN.isNNF B)
    (hSkolem : isSkolemNormalForm B)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K B) (hL : isCInstanceOf Ls B) :
    (∀ hNoEq : L.withoutEquality,
      ∃ D, isCInstanceOf D B ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      ∃ D, isCInstanceOf D B ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) 

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): midsequentCInstancesProvable
-- ===================================================================

end LCS.Herbrand.SHGTheorem.Herbrand
end
