import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Reduction.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Lemma 6.4.7: Reduction lemma
-- ===================================================================
/-- Lemma 6.4.7 (Reduction lemma for G1nnf, adopted reading under
erratum E-CUTFB): given proofs T₁ of `Γ → insert A Δ` and T₂ of
`insert A Λ → Θ` with `c(T₁), c(T₂) ≤ |A|`, assume the §6.1 convention
on the output sequent `Γ ∪ Λ → Δ ∪ Θ`: no variable occurs both free
and bound anywhere in that sequent. The conclusion is a proof T of this
sequent with `depth(T) ≤ depth(T₁) + depth(T₂)` and `c(T) ≤ |A|`. -/
@[attach_debt, blueprint "chap6__lemma_6_4_7" (main := true)]
theorem g1nnf_reduction_lemma {L : Language} {hL : L.withoutEquality}
    {Γ Δ Λ Θ : LCS.Finset (FormulaN L)}
    (A : FormulaN L)
    (T₁ : G1nnfProofTree hL Γ (LCS.Finset.insert A Δ))
    (T₂ : G1nnfProofTree hL (LCS.Finset.insert A Λ) Θ)
    (hRank1 : T₁.cutRank ≤ A.degree) (hRank2 : T₂.cutRank ≤ A.degree)
    (hOut : finsetCrossNoFreeBound (LCS.Finset.union Γ Λ) (LCS.Finset.union Δ Θ)) :
    ∃ T : G1nnfProofTree hL (LCS.Finset.union Γ Λ) (LCS.Finset.union Δ Θ),
      T.depth ≤ T₁.depth + T₂.depth ∧
      T.cutRank ≤ A.degree 

end LCS.CutElim.Hauptsatz
end
