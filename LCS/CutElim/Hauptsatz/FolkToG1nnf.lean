import LCS.CutElim.Hauptsatz.CutElimination
import Attach
import LCS.CutElim.Hauptsatz.FolkToG1nnf.ProofsStamp

/-! # FolkToG1nnf
    Completeness of G1nnf with indexed finite-set proof witnesses.
-/

namespace LCS.CutElim.Hauptsatz.FolkToG1nnf

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.LK
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness

-- ===================================================================
-- Full completeness: indexed proof-tree witnesses
-- ===================================================================

/-- Lemma 6.4.2: Every valid G1nnf-sequent over a language without equality
satisfying the sequent-level free/bound-variable convention has a G1nnf
proof. The witness is indexed by any finite-set representatives of the
antecedent and succedent. The term-countability instance records the
book's invocation of Theorem 5.5.1. -/
@[blueprint "chap6__lemma_6_4_2" (main := true)]
theorem g1nnf_completeness_full {L : Language} [Countable (Term L)]
    (hNoEq : L.withoutEquality)
    (s : G1nnfSequent L hNoEq)
    (hValid : s.isValid)
    (hNoFreeBound :
      ∀ x : Nat,
        (∃ A, (A ∈ s.ante ∨ A ∈ s.succ) ∧
          x ∈ LCS.FirstOrder.SyntaxN.Variables.formulaFVN A) →
        (∀ B, (B ∈ s.ante ∨ B ∈ s.succ) →
          x ∉ LCS.FirstOrder.SyntaxN.Variables.formulaBVN B))
    (Γ Δ : LCS.Finset (FormulaN L))
    (hΓ : ∀ F, F ∈ Γ ↔ s.ante F)
    (hΔ : ∀ F, F ∈ Δ ↔ s.succ F) :
    Nonempty (G1nnfProofTree hNoEq Γ Δ) 

end LCS.CutElim.Hauptsatz.FolkToG1nnf
