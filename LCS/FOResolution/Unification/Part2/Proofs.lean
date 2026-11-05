import LCS.FOResolution.Unification.Part2

section

namespace LCS.FOResolution.Unification

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.SyntaxN.Variables

helper /-- The explicit Robinson decrease relation is well founded. -/
theorem robinsonMeasureDecreases_wf {L : Language} :
    WellFounded (@RobinsonMeasureDecreases L) := by
-- BEGIN PROOF
  unfold RobinsonMeasureDecreases
  exact InvImage.wf robinsonMeasure
    (Prod.lex Nat.lt_wfRel
      (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf





helper /-- A unifiable finite equation system cannot terminate in either failure
    state. -/
theorem robinsonSolve_ne_failure_of_unifiable {L : Language}
    (equations : List (Term L × Term L))
    (sigma : Nat → Term L)
    (hUnif : IsPairwiseUnifier sigma equations)
    (reason : RobinsonFailure) :
    robinsonSolve equations ≠ RobinsonSolveResult.failure reason := by
-- BEGIN PROOF
  intro hFailure
  exact (robinsonSolve_failure_not_unifiable
    equations reason hFailure) ⟨sigma, hUnif⟩





proof_of unifEx_common_images_i := by
  constructor
  · rfl
  · change Term.func (L := unificationExampleLanguage) UnifExFunc.f _ = Term.func (L := unificationExampleLanguage) UnifExFunc.f _
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ =>
      change Term.func (L := unificationExampleLanguage) UnifExFunc.g _ = Term.func (L := unificationExampleLanguage) UnifExFunc.g _
      congr 1
      funext j
      match j with | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ =>
      change Term.func (L := unificationExampleLanguage) UnifExFunc.g _ = Term.func (L := unificationExampleLanguage) UnifExFunc.g _
      congr 1
      funext j
      match j with | ⟨0, _⟩ => rfl


proof_of unifEx_mci_i_eq := by
  change Term.func (L := unificationExampleLanguage) UnifExFunc.f _ = Term.func (L := unificationExampleLanguage) UnifExFunc.f _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ =>
    change Term.func (L := unificationExampleLanguage) UnifExFunc.g _ = Term.func (L := unificationExampleLanguage) UnifExFunc.g _
    congr 1
    funext j
    match j with | ⟨0, _⟩ => rfl


end LCS.FOResolution.Unification

end
