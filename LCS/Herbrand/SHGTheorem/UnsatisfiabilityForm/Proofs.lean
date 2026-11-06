import LCS.Herbrand.SHGTheorem.UnsatisfiabilityForm

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

proof_of shgMotivPreparation := by
  refine ⟨rfl, by trivial, ?_, ?_⟩
  · simp [shgMotivNNFNeg, shgMotivLang,
      LCS.FirstOrder.Semantics.Subformulae.isRectified,
      LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      formulaFVN, formulaBVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      shgMotivVec1, shgMotivVec2, Fin.exists_fin_succ,
      Fin.forall_fin_succ] <;> (intros; omega)
  · change formulaFVN shgMotivNNFNeg = ∅
    funext x
    apply propext
    simp [shgMotivNNFNeg, shgMotivLang, formulaFVN, termFV,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      shgMotivVec1, shgMotivVec2, Fin.exists_fin_succ,
      Fin.forall_fin_succ] <;> omega

proof_of shgMotivMidsequent_substitution := set_option backward.isDefEq.respectTransparency false in
  by
    simp [shgMotivMidsequent, shgMotivTransformedMidsequent,
      ShgMotivProof.p, ShgMotivProof.r, ShgMotivProof.a,
      ShgMotivTransformedProof.fa, ShgMotivTransformedProof.a, shgMotivLang,
      formulaSubstN, ShgMotivProof.substVec1, ShgMotivProof.substVec2, termSubst]

end LCS.Herbrand.SHGTheorem
end
