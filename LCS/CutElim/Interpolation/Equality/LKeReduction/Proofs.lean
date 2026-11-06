import LCS.CutElim.Interpolation.Equality.LKeReduction

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

helper /-- Lemma 6.5.3 (companion): Backward direction: if
(closedEqualityAxioms S ++ Gamma) -> Delta is LKe-provable,
then S is LKe-provable. Each formula in S_e is universally valid,
so use lkeProvable_remove_valid_prefix to strip them. -/
theorem lke_with_se_to_lke {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : lkeProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent }) :
    lkeProvable S :=
-- BEGIN PROOF
by
  have hresult := lkeProvable_remove_valid_prefix
    (closedEqualityAxioms hL S) S.antecedent S.succedent
    (closedEqualityAxioms_universally_valid hL S) hProv
  have heq : Sequent.mk S.antecedent S.succedent = S := by cases S; rfl
  rw [heq] at hresult
  exact hresult

helper /-- Lemma 6.5.3 (companion): Backward direction from folkProvable:
if (closedEqualityAxioms S ++ Gamma) -> Delta is LK-provable,
then S is LKe-provable. Wraps the FOLK proof in LKe.lk and
strips the S_e prefix. -/
theorem lk_with_se_to_lke {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent }) :
    lkeProvable S :=
-- BEGIN PROOF
by
  -- folkProvable is now Nonempty (FOLKProofTree s) with indexed proof trees
  obtain ⟨t⟩ := hProv
  have hlke : lkeProvable (Sequent.mk (closedEqualityAxioms hL S ++ S.antecedent) S.succedent) :=
    ⟨LKeProofTree.lk t⟩
  exact lke_with_se_to_lke hL S hlke

proof_of lke_provable_iff_lke_with_se := ⟨lke_to_folk_with_se hL S, lk_with_se_to_lke hL S⟩
  -- BEGIN PROOF

end LCS.CutElim.Interpolation.Equality
end
