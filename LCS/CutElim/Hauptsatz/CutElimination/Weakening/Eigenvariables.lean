import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.TreeTransport
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Constructions

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Lemma 6.4.5: Weakening
-- ===================================================================
/-- Eigenvariables can be renamed away from the free variables of a formula
while preserving the end sequent, depth, and cut rank. -/
theorem G1nnfProofTree.freshenForWeakening_exists {L : Language}
    {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) :
    ∃ S : G1nnfProofTree hL Γ Δ,
      S.depth = T.depth ∧ S.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ S.eigenvariables v := by
  -- REPAIR(T6-29a): proof pending
  sorry

/-- Direct left weakening preserves the eigenvariable labels of its input. -/
theorem G1nnfProofTree.weakenTreeLeft_eigenvariables_eq {L : Language}
    {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, formulaFVN A v → ¬ T.eigenvariables v) (v : Nat) :
    (T.weakenTreeLeft A hNNF hFV).eigenvariables v = T.eigenvariables v := by
  -- REPAIR(T6-29a): proof pending
  sorry

/-- Direct right weakening preserves the eigenvariable labels of its input. -/
theorem G1nnfProofTree.weakenTreeRight_eigenvariables_eq {L : Language}
    {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, formulaFVN A v → ¬ T.eigenvariables v) (v : Nat) :
    (T.weakenTreeRight A hNNF hFV).eigenvariables v = T.eigenvariables v := by
  -- REPAIR(T6-29a): proof pending
  sorry

end LCS.CutElim.Hauptsatz
end
