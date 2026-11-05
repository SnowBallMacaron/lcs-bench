import LCS.CutElim.Hauptsatz.CutElimination.Freshening

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

proof_of g1nnf_substitution_lemma := by
  let R := G1nnfProofTree.prepareSubstitution T t y hNotBound hFree
  obtain ⟨T', hd, hc, he⟩ :=
    g1nnf_substitution_of_treeSubstOk R.tree y t R.treeSubstOk
  exact ⟨T', hd.trans R.depth_eq, hc.trans R.cutRank_eq, he⟩

helper theorem degree_conj_left {L : Language} (A B : FormulaN L) :
    A.degree < (FormulaN.conj A B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega

helper theorem degree_conj_right {L : Language} (A B : FormulaN L) :
    B.degree < (FormulaN.conj A B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega

helper theorem degree_disj_left {L : Language} (A B : FormulaN L) :
    A.degree < (FormulaN.disj A B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega

helper theorem degree_disj_right {L : Language} (A B : FormulaN L) :
    B.degree < (FormulaN.disj A B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega

helper theorem degree_all_body {L : Language} (x : Nat) (B : FormulaN L) :
    B.degree < (FormulaN.all x B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega

helper theorem degree_ex_body {L : Language} (x : Nat) (B : FormulaN L) :
    B.degree < (FormulaN.ex x B).degree := by
-- BEGIN PROOF
  simp only [FormulaN.degree]; omega





helper theorem nat_le_two_pow : ∀ (n : Nat), n ≤ 2 ^ n := by
  intro n
  exact nat_le_pow_of_two_le 2 n (by omega)









end LCS.CutElim.Hauptsatz

end
