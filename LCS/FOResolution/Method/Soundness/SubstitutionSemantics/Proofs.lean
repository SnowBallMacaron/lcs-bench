import LCS.FOResolution.Method.Soundness.SubstitutionSemantics

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





















helper /-- substFormula preserves the quantifier-free property. -/
theorem isQF_substFormula {L : Language} (sigma : Nat → Term L)
    (A : FormulaN L) (h : isQuantifierFree A) :
    isQuantifierFree (substLit.substFormula sigma A) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih => exact ih h
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | all _ _ => exact absurd h id
  | ex _ _ => exact absurd h id



helper /-- substLits preserves ClauseQF. -/
theorem ClauseQF_substLits {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (C : FOClause L hNoEq) (hQF : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C) :
    (ClauseQF (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C) := by
-- BEGIN PROOF
  intro lit hmem
  simp [substLits, List.mem_map] at hmem
  obtain ⟨lit', hmem', rfl⟩ := hmem
  exact (clauseQF (hNoEq := by all_goals exact hNoEq)) _ _ (List.mem_map_of_mem hmem')

helper /-- listDiff preserves ClauseQF. -/
theorem ClauseQF_listDiff {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (C sub : FOClause L hNoEq) (hQF : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C) :
    (ClauseQF (hNoEq := by all_goals exact hNoEq)) (listDiff C sub) := by
-- BEGIN PROOF
  intro lit hmem
  simp [listDiff, List.mem_filter] at hmem
  exact hQF lit hmem.1

helper /-- Append preserves ClauseQF. -/
theorem ClauseQF_append {L : Language} (hNoEq : L.withoutEquality) (C1 C2 : FOClause L hNoEq)
    (h1 : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C1) (h2 : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C2) :
    (ClauseQF (hNoEq := by all_goals exact hNoEq)) (C1 ++ C2) := by
-- BEGIN PROOF
  intro lit hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl h => exact h1 lit h
  | inr h => exact h2 lit h

helper /-- Resolution preserves ClauseQF because literals have an atomic carrier. -/
theorem ClauseQF_resolvent {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (A B C : FOClause L hNoEq) (hRes : (IsResolvent (hNoEq := by all_goals exact hNoEq)) C A B) : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C := by
-- BEGIN PROOF
  exact (clauseQF (hNoEq := by all_goals exact hNoEq)) C





































end LCS.FOResolution.Method.Soundness

end
