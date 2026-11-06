import LCS.FOResolution.Method.Soundness.ResolventValidity

section
namespace LCS.FOResolution.Method.Soundness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method

proof_of resolvent_validity := by
  intro M hA hB
  have hQFA := (clauseQF (hNoEq := by all_goals exact hNoEq)) A
  have hQFB := (clauseQF (hNoEq := by all_goals exact hNoEq)) B
  obtain ⟨A', B', rho, rho', sigma,
    hSubA, hSubB, _hA'ne, _hB'ne, _hSameSign, _hOppSign,
    _hSamePred, _hSep, _hPairwise, hCeq⟩ := hRes
  intro s
  have sA_eq : (fun x => termEval M s (termSubstAll (rho x) sigma)) =
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho x)) :=
    funext fun x => termSubstAll_eval M s sigma (rho x)
  have sB_eq : (fun x => termEval M s (termSubstAll (rho' x) sigma)) =
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho' x)) :=
    funext fun x => termSubstAll_eval M s sigma (rho' x)
  let sA : Assignment M := fun x => termEval M s (termSubstAll (rho x) sigma)
  let sB : Assignment M := fun x => termEval M s (termSubstAll (rho' x) sigma)
  obtain ⟨litA, hlitA_mem, hlitA_eval⟩ := hA sA
  obtain ⟨litB, hlitB_mem, hlitB_eval⟩ := hB sB
  have listDiff_mem : ∀ {α : Type} [DecidableEq α] {a : α} {full sub : List α},
      a ∈ full → a ∉ sub → a ∈ listDiff full sub := by
    intro α _ a full sub hmem hnotin
    simp only [listDiff, List.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [Bool.not_eq_true']; rw [Bool.eq_false_iff]
    intro hc; rw [List.contains_iff_exists_mem_beq] at hc
    obtain ⟨b, hb, heq⟩ := hc; exact hnotin (eq_of_beq heq ▸ hb)
  by_cases hlitA_in : litA ∈ A'
  · by_cases hlitB_in : litB ∈ B'
    · -- contradiction case: opposite sign + unifier
      exact absurd ((opposite_sign_contradiction_pairwise (hNoEq := by all_goals exact hNoEq)) M s A' B' rho rho' sigma
        litA litB hlitA_in hlitB_in _hSameSign _hOppSign _hSamePred _hPairwise
        (sA_eq ▸ hlitA_eval) (sB_eq ▸ hlitB_eval)) id
    · have hmem_diff := listDiff_mem hlitB_mem hlitB_in
      have hmem_sigma : (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho' litB) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
                           (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
        simp only [substLits, List.map_append]
        exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem hmem_diff))
      refine ⟨_, (hCeq _).mpr hmem_sigma, ?_⟩
      apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho' litB)
        ((isQF_substLit_formula (hNoEq := by all_goals exact hNoEq)) rho' litB (hQFB litB hlitB_mem))).mpr
      apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M (fun x => termEval M s (sigma x)) rho' litB
        (hQFB litB hlitB_mem)).mpr
      rw [← sB_eq]; exact hlitB_eval
  · have hmem_diff := listDiff_mem hlitA_mem hlitA_in
    have hmem_sigma : (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho litA) ∈
        (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
                         (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
      simp only [substLits, List.map_append]
      exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem hmem_diff))
    refine ⟨_, (hCeq _).mpr hmem_sigma, ?_⟩
    apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho litA)
      ((isQF_substLit_formula (hNoEq := by all_goals exact hNoEq)) rho litA (hQFA litA hlitA_mem))).mpr
    apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M (fun x => termEval M s (sigma x)) rho litA
      (hQFA litA hlitA_mem)).mpr
    rw [← sA_eq]; exact hlitA_eval

end LCS.FOResolution.Method.Soundness
end
