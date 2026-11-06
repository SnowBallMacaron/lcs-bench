import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Constructions
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Measures
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Eigenvariables
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Lemma 6.4.5 (Weakening lemma): an arbitrary NNF formula can be
added on either side. Both output proofs preserve depth and cut rank, and
have no eigenvariable free in the added formula. -/
@[blueprint "chap6__lemma_6_4_5" (main := true)]
theorem g1nnf_weakening_lemma {L : Language}
    (hNoEq : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hNoEq Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF) :
    (∃ Tₗ : G1nnfProofTree hNoEq (LCS.Finset.insert A Γ) Δ,
      Tₗ.depth = T.depth ∧ Tₗ.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ Tₗ.eigenvariables v) ∧
    (∃ Tᵣ : G1nnfProofTree hNoEq Γ (LCS.Finset.insert A Δ),
      Tᵣ.depth = T.depth ∧ Tᵣ.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ Tᵣ.eigenvariables v) 

end LCS.CutElim.Hauptsatz
end
