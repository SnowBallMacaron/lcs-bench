import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Inversion.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Lemma 6.4.6: Inversion lemma
-- ===================================================================
/-- Lemma 6.4.6 (Inversion lemma): Conjunction-right inversion (case
i-a). If `Γ → insert (A ∧ B) Δ` is G1nnf-provable, then both
`Γ → insert A Δ` and `Γ → insert B Δ` are provable with depth/cutRank
bounds. The companion cases are `g1nnf_inversion_disj_left` (i-b),
`g1nnf_inversion_all_right` (ii-a), and `g1nnf_inversion_ex_left`
(ii-b). -/
@[attach_debt, blueprint "chap6__lemma_6_4_6" (main := true)]
theorem g1nnf_inversion_conj_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (A B : FormulaN L)
    (T : G1nnfProofTree hL Γ (LCS.Finset.insert (.conj A B) Δ)) :
    ∃ (T₁ : G1nnfProofTree hL Γ (LCS.Finset.insert A Δ))
      (T₂ : G1nnfProofTree hL Γ (LCS.Finset.insert B Δ)),
      T₁.depth ≤ T.depth ∧
      T₂.depth ≤ T.depth ∧
      T₁.cutRank ≤ T.cutRank ∧
      T₂.cutRank ≤ T.cutRank 

/-- Lemma 6.4.6 (Inversion lemma, companion case i-b): Disjunction-left
inversion. The main statement carries the `@[lcsmain]` tag on
`g1nnf_inversion_conj_right`. -/
@[attach_debt, blueprint "chap6__lemma_6_4_6" (main := true)]
theorem g1nnf_inversion_disj_left {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (A B : FormulaN L)
    (T : G1nnfProofTree hL (LCS.Finset.insert (.disj A B) Γ) Δ) :
    ∃ (T₁ : G1nnfProofTree hL (LCS.Finset.insert A Γ) Δ)
      (T₂ : G1nnfProofTree hL (LCS.Finset.insert B Γ) Δ),
      T₁.depth ≤ T.depth ∧
      T₂.depth ≤ T.depth ∧
      T₁.cutRank ≤ T.cutRank ∧
      T₂.cutRank ≤ T.cutRank 

/-- Lemma 6.4.6 (Inversion lemma, companion case ii-a): Universal-right
inversion. The main statement carries the `@[lcsmain]` tag on
`g1nnf_inversion_conj_right`. -/
@[attach_debt, blueprint "chap6__lemma_6_4_6" (main := true)]
theorem g1nnf_inversion_all_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (x : Nat) (B : FormulaN L)
    (T : G1nnfProofTree hL Γ (LCS.Finset.insert (.all x B) Δ))
    (y : Nat)
    (hNotBound : T.forgetProofTree.notBoundIn y)
    (hNotEigen : ¬ T.eigenvariables y) :
    ∃ T₁ : G1nnfProofTree hL Γ (LCS.Finset.insert (formulaSubstN B (.var y) x) Δ),
      T₁.depth ≤ T.depth ∧
      T₁.cutRank ≤ T.cutRank 

/-- Lemma 6.4.6 (Inversion lemma, companion case ii-b): Existential-left
inversion. The main statement carries the `@[lcsmain]` tag on
`g1nnf_inversion_conj_right`. -/
@[attach_debt, blueprint "chap6__lemma_6_4_6" (main := true)]
theorem g1nnf_inversion_ex_left {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (x : Nat) (B : FormulaN L)
    (T : G1nnfProofTree hL (LCS.Finset.insert (.ex x B) Γ) Δ)
    (y : Nat)
    (hNotBound : T.forgetProofTree.notBoundIn y)
    (hNotEigen : ¬ T.eigenvariables y) :
    ∃ T₁ : G1nnfProofTree hL (LCS.Finset.insert (formulaSubstN B (.var y) x) Γ) Δ,
      T₁.depth ≤ T.depth ∧
      T₁.cutRank ≤ T.cutRank 

end LCS.CutElim.Hauptsatz
end
