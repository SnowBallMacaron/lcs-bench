import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of positiveClosure_equivalence := by
  -- REPAIR(T10-22): proof pending — combine the sort-supported closure's fiber equivalences.
  sorry

proof_of semanticEqualityRelationNode_mk := by
  -- BEGIN PROOF
    obtain ⟨uv, hum⟩ := u
    obtain ⟨vv, hvm⟩ := v
    simp only at hu hv ⊢
    subst hu; subst hv
    exact ⟨s, rfl, rfl, hrel⟩

proof_of semanticEqualityRelationNode_elim := by
  -- BEGIN PROOF
    obtain ⟨uv, hum⟩ := u
    obtain ⟨vv, hvm⟩ := v
    simp only at hu hv
    subst hu; subst hv
    obtain ⟨s', h1, h2, hr⟩ := hrel
    -- `s' = ⟨s,tu⟩.1 = s`; both transports collapse to identity.
    cases h1; cases h2
    exact hr

proof_of semanticEqualityRelation_isCongruence := by
  -- REPAIR(T10-22): proof pending — establish sort support, fiber equivalence and backward closure over occurring labels.
  sorry

proof_of positiveEquationRelation_subset_semantic := by
  -- BEGIN PROOF
    obtain ⟨hL, s, t, u, hcontain, hp, hq⟩ := h
    refine semanticEqualityRelationNode_mk C p q s t u hp hq ⟨hL, ?_⟩
    -- `eq_ hL s t u` is a member of `E_set`, so any satisfying model makes
    -- it true.
    intro M v hsat
    exact hsat (MSFormula.eq_ hL s t u) ⟨⟨hL, s, t, u, rfl⟩, hcontain⟩

proof_of collision_entails_equation := by
  -- BEGIN PROOF
    -- `R*` is the least congruence containing `E`, and the semantic-equality
    -- node relation is a congruence containing `E`, so `R* ⊆ R`.
    have hsub := msCongruenceClosure_smallest (graphOfConjunction C)
      (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) (semanticEqualityRelationNode C)
      (semanticEqualityRelation_isCongruence C)
      (positiveEquationRelation_subset_semantic C)
      p q hcol
    -- Extract the sort-level relation between `r`, `v`.
    have hrel := semanticEqualityRelationNode_elim C p q s r v hp hq hsub
    -- `hrel : ∃ hL', msEntails E_set (eq_ hL' s r v)`; the proof flag is
    -- irrelevant (proof of `L.hasEquality = true`).
    obtain ⟨hL', hent⟩ := hrel
    -- align the equality flag.
    have : hL' = hL := rfl
    rw [this] at hent
    exact hent

proof_of msConjunctContains_eval := by
  -- BEGIN PROOF
    intro C
    induction C with
    | conj A B ihA ihB =>
      intro X hcon hCeval
      rw [msFormulaEval_conj, hAnd_eq_T_iff] at hCeval
      rcases hcon with hself | hsub
      · rw [← hself]; rw [msFormulaEval_conj, hAnd_eq_T_iff]; exact hCeval
      · rcases hsub with hA | hB
        · exact ihA X hA hCeval.1
        · exact ihB X hB hCeval.2
    | falsum => intro X hcon hCeval; rw [show X = MSFormula.falsum from hcon.symm]; exact hCeval
    | pred P ts => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | eq_ hL s t u => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | disj A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | impl A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | equiv_ A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | neg A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | all s i A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | ex s i A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval

proof_of collision_unsat_direction := by
  -- BEGIN PROOF
    obtain ⟨hL, s, r, vt, p, q, hneg, hp, hq, hcol⟩ := h
    -- Suppose `C` is satisfiable; derive a contradiction.
    rintro ⟨M, v, hCeval⟩
    -- The collision entails `r =̇ vt` under any model of E_set.
    have hent := collision_entails_equation C hL s r vt p q hp hq hcol
    -- `M, v` satisfies E_set (the positive equations contained in C).
    have hEset : ∀ B, equationSetOfConjunction C B →
        msFormulaEval M B v = BoolVal.T := by
      intro B ⟨_, hBcontain⟩
      exact msConjunctContains_eval M v C B hBcontain hCeval
    -- So `r =̇ vt` is true under `M, v`.
    have hpos : msFormulaEval M (MSFormula.eq_ hL s r vt) v = BoolVal.T :=
      hent M v hEset
    -- But the negated equation is also true (it is a conjunct of C).
    have hnegeval : msFormulaEval M (MSFormula.neg (MSFormula.eq_ hL s r vt)) v
        = BoolVal.T :=
      msConjunctContains_eval M v C _ hneg hCeval
    -- Contradiction: `r =̇ vt` is true, so `r_M[v] = vt_M[v]`, making the
    -- negated equation evaluate to `F`, not `T`.
    have heq : msTermEval M v r = msTermEval M v vt :=
      (msFormulaEval_eq_T_iff M hL s r vt v).mp hpos
    dsimp only [msFormulaEval, negM, eqM] at hnegeval
    rw [if_pos heq] at hnegeval
    exact absurd hnegeval (by decide)

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
