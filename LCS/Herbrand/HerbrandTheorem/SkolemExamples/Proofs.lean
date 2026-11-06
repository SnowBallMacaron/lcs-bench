import LCS.Herbrand.HerbrandTheorem.SkolemExamples

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

proof_of functionalFormExample_eq_allocated := by
  -- REPAIR(T7-131): proof pending
  sorry

proof_of groundSequentExample_eq_substitution := by
  simp only [functionalFormExample_7_5_2, groundSequentExample_7_5_2,
    skolemExampleGroundSubstitution, prenexPrefix, prenexMatrix,
    Substitution.applyFormula, vec2, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, LCS.FirstOrder.SyntaxN.FormulaN.neg.injEq,
    LCS.FirstOrder.SyntaxN.FormulaN.conj.injEq]
  refine ⟨True.intro, True.intro, ?_, ?_, ?_, ?_⟩
  all_goals
    apply congrArg (LCS.FirstOrder.SyntaxN.FormulaN.predN _)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl

end LCS.Herbrand.HerbrandTheorem
