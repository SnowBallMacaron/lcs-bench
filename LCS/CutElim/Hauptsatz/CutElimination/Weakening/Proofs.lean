import LCS.CutElim.Hauptsatz.CutElimination.Weakening

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

helper /-- Lemma 6.4.5 (left weakening): every NNF formula may be added
with unchanged depth and cut rank, and its free variables are disjoint from
the eigenvariables of the resulting proof. -/
theorem g1nnf_weakening_left {L : Language}
    (hNoEq : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hNoEq Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF) :
    ∃ T' : G1nnfProofTree hNoEq (LCS.Finset.insert A Γ) Δ,
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ T'.eigenvariables v := by
  obtain ⟨S, hd, hc, he⟩ := T.freshenForWeakening_exists A
  refine ⟨S.weakenTreeLeft A hNNF he,
    (S.weakenTreeLeft_depth A hNNF he).trans hd,
    (S.weakenTreeLeft_cutRank A hNNF he).trans hc, ?_⟩
  intro v hv
  rw [S.weakenTreeLeft_eigenvariables_eq A hNNF he v]
  exact he v hv

helper /-- Lemma 6.4.5 (right weakening): every NNF formula may be added
with unchanged depth and cut rank, and its free variables are disjoint from
the eigenvariables of the resulting proof. -/
theorem g1nnf_weakening_right {L : Language}
    (hNoEq : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hNoEq Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF) :
    ∃ T' : G1nnfProofTree hNoEq Γ (LCS.Finset.insert A Δ),
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ T'.eigenvariables v := by
  obtain ⟨S, hd, hc, he⟩ := T.freshenForWeakening_exists A
  refine ⟨S.weakenTreeRight A hNNF he,
    (S.weakenTreeRight_depth A hNNF he).trans hd,
    (S.weakenTreeRight_cutRank A hNNF he).trans hc, ?_⟩
  intro v hv
  rw [S.weakenTreeRight_eigenvariables_eq A hNNF he v]
  exact he v hv

proof_of g1nnf_weakening_lemma := by
  exact ⟨g1nnf_weakening_left hNoEq T A hNNF,
    g1nnf_weakening_right hNoEq T A hNNF⟩

end LCS.CutElim.Hauptsatz
end
