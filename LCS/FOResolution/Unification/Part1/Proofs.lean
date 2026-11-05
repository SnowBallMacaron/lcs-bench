import LCS.FOResolution.Unification.Part1

section

namespace LCS.FOResolution.Unification

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.SyntaxN.Variables



proof_of mostCommonInstance_eq := by
  exact h.1.2 _ _ (List.head_mem h.1.1) ht




















proof_of termSubstAll_compose := SubstitutionCore.termSubstAll_compose t sigma.map theta.map


proof_of substCompose_assoc := by
  apply FiniteSubstitution.ext
  · exact List.append_assoc _ _ _
  · intro x
    exact termSubstAll_compose (sigma x) theta rho


proof_of substCompose_identity_left := by
  apply FiniteSubstitution.ext
  · rfl
  · intro x
    rfl


proof_of substCompose_identity_right := by
  apply FiniteSubstitution.ext
  · exact List.append_nil _
  · intro x
    exact termSubstAll_identity (sigma x)


proof_of substSupport_compose_subset := by
  intro x hx
  rcases SubstitutionCore.substSupport_compose_subset theta.map sigma.map x hx with h | h
  · exact Or.inr h
  · exact Or.inl h












helper /-- Boolean occurs-check form of `termSubstAll_elementary_of_not_fv`. -/
theorem termSubstAll_elementary_of_occurs_false {L : Language}
    (x : Nat) (u t : Term L) (hOccurs : termOccurs x t = false) :
    termSubstAll t (elementarySubst x u) = t := by
-- BEGIN PROOF
  apply termSubstAll_elementary_of_not_fv
  intro hx
  have := (termOccurs_eq_true_iff x t).mpr hx
  rw [hOccurs] at this
  contradiction









































end LCS.FOResolution.Unification

end
