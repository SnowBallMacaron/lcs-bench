import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.TreeSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionPreparation
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionLemma.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Internal substitution lemma under the direct rule-admissibility contract. -/
theorem g1nnf_substitution_of_treeSubstOk {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) :
    ∃ T' : G1nnfProofTree hL (substFormulaFinset Γ t y) (substFormulaFinset Δ t y),
      T'.depth = T.depth
      ∧ T'.cutRank = T.cutRank
      ∧ (¬ T'.eigenvariables y)
      ∧ (∀ v, termFV t v → ¬ T'.eigenvariables v)
      ∧ T'.conclusion = (substFormulaFinset Γ t y, substFormulaFinset Δ t y) := by
-- BEGIN PROOF
  have hDisjoint := T.treeSubstOk_eigenvariables_disjoint y t hOk
  refine ⟨T.substTerm t y hOk, T.substTerm_depth y t hOk,
    T.substTerm_cutRank y t hOk, ?_, ?_, rfl⟩
  · rw [T.substTerm_eigenvariables_eq y t hOk y]
    exact hDisjoint.1
  · intro v hv
    rw [T.substTerm_eigenvariables_eq y t hOk v]
    exact hDisjoint.2 v hv /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Lemma 6.4.4 (Substitution lemma): if `y` is not bound in T and
`t` is free for `y` in its root sequent, there is a proof of the substituted
sequent with the same depth and cut rank. Neither `y` nor any variable of
`t` is an eigenvariable of the resulting proof. -/
@[blueprint "chap6__lemma_6_4_4" (main := true)]
theorem g1nnf_substitution_lemma {L : Language}
    {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hNotBound : T.notBoundIn y) (hFree : freeForAtRoot T t y) :
    ∃ T' : G1nnfProofTree hL (substFormulaFinset Γ t y) (substFormulaFinset Δ t y),
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      (¬ T'.eigenvariables y) ∧
      (∀ v, termFV t v → ¬ T'.eigenvariables v) ∧
      T'.conclusion = (substFormulaFinset Γ t y, substFormulaFinset Δ t y)

end LCS.CutElim.Hauptsatz
end
