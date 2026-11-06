import LCS.FOResolution.Unification.Examples

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

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

proof_of unifEx_isMGU_i := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro t u ht hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · rfl
    · exact unifEx_common_images_i.1.trans unifEx_common_images_i.2.symm
    · exact unifEx_common_images_i.2.trans unifEx_common_images_i.1.symm
    · rfl
  · intro x hx
    have hm : x ∈ unifEx_finite_mgu_i.support :=
      Classical.byContradiction (fun h => hx (unifEx_finite_mgu_i.outsideSupport x h))
    change x ∈ [0, 2] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨unifEx_t1_i, by simp, ⟨(0 : Fin 2), rfl⟩⟩
    · exact ⟨unifEx_t2_i, by simp, ⟨(1 : Fin 2), (0 : Fin 1), rfl⟩⟩
  · intro tau hTau
    have he := hTau.2 unifEx_t1_i unifEx_t2_i (by simp) (by simp)
    have hargs := eq_of_heq (Term.func.inj he).2
    have h0 := congrFun hargs (0 : Fin 2)
    have h1 := congrFun hargs (1 : Fin 2)
    have h12 := congrFun (eq_of_heq (Term.func.inj h1).2) (0 : Fin 1)
    change tau 1 = tau 2 at h12
    refine ⟨tau, ?_⟩
    intro x
    match x with
    | 0 => exact h0
    | 1 => rfl
    | 2 => exact h12.symm
    | n + 3 => rfl

proof_of unifEx_mostCommonInstance_i := by
  exact (mostCommonInstance_eq unifEx_finite_mgu_i
    [unifEx_t1_i, unifEx_t2_i] unifEx_isMGU_i unifEx_t2_i (by simp)).trans
      unifEx_common_images_i.2

proof_of unifEx_symbol_clash_ii := by
  have he := h.2 unifEx_t1_ii unifEx_t2_ii (by simp) (by simp)
  have hargs := eq_of_heq (Term.func.inj he).2
  have hg := congrFun hargs (1 : Fin 2)
  exact (Term.func.inj hg).1

proof_of unifEx_not_unifiable_ii := by
  rintro ⟨sigma, h⟩
  have clash := unifEx_symbol_clash_ii sigma h
  cases clash

proof_of unifEx_equations_iii := by
  have he := h.2 unifEx_t1_iii unifEx_t2_iii (by simp) (by simp)
  have hargs := eq_of_heq (Term.func.inj he).2
  have h0 := congrFun hargs (0 : Fin 3)
  have h1 := congrFun hargs (1 : Fin 3)
  have h2 := congrFun hargs (2 : Fin 3)
  have hinner := congrFun (eq_of_heq (Term.func.inj h1).2) (0 : Fin 1)
  exact ⟨h0, h2, h1, hinner, h2.symm.trans hinner⟩

proof_of unifEx_not_unifiable_iii := by
  rintro ⟨sigma, h⟩
  have hz := (unifEx_equations_iii sigma h).2.2.2.2
  exact (var_occurs_not_unifiable (L := unificationExampleLanguage3) 2
    (Term.func UnifExFunc3.g (unifVec1 (Term.var 2)))
    (by intro he; cases he) (by rfl)) ⟨sigma.map, hz⟩

end LCS.FOResolution.Unification
end
