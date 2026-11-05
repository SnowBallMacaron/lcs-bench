import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.Propositional.Semantics

proof_of collisionUnsatPredCore := by
  -- BEGIN PROOF
    -- The collision makes `C'` unsatisfiable (Decision soundness direction).
    have hunsatC' : Decision.msUnsatisfiable (msEncodeConjunction L C) :=
      Decision.collision_unsat_direction (msEncodeConjunction L C)
        ⟨rfl, s, r, v, p, q, hcontains, hp, hq, hcol⟩
    -- The encoding preserves satisfiability, so `C` is unsatisfiable too.
    intro hsatC
    exact hunsatC' (encodePreservesSat L C hsatC)


proof_of collisionCaseNonBool := collisionUnsatPredCore L C s r v p q hcontains hp hq hcol
  -- BEGIN PROOF


proof_of collisionCaseAtomTop := collisionUnsatPredCore L C (MSBoolSort L)
  -- BEGIN PROOF
    -- The negated conjunct `neg (msEncodeAtom L P args)` IS
    -- `neg (eq_ rfl (MSBoolSort L) (msPredAsFuncTerm L P args) (msTopConst L))`,
    -- so this is a bool-sort collision folding into the soundness core.
      (msPredAsFuncTerm L P args) (msTopConst L) p q hcontains hp hq hcol


proof_of semanticEqualityRelationPred_refl := by
  intro M v _
  exact msEqReflValid rfl s t M v


proof_of semanticEqualityRelationPred_symm := by
  intro M v hsat
  apply (msFormulaEval_eq_T_iff _ _ _ _ _ _).mpr
  exact ((msFormulaEval_eq_T_iff M rfl s t u v).mp (h M v hsat)).symm


proof_of semanticEqualityRelationPred_trans := by
  intro M v hsat
  apply (msFormulaEval_eq_T_iff _ _ _ _ _ _).mpr
  have e1 := (msFormulaEval_eq_T_iff M rfl s t u v).mp (h1 M v hsat)
  have e2 := (msFormulaEval_eq_T_iff M rfl s u w v).mp (h2 M v hsat)
  exact e1.trans e2


proof_of semanticEqualityRelationPred_funcCong := by
  intro M v hsat
  apply (msFormulaEval_eq_T_iff _ _ _ _ _ _).mpr
  have hargs : ∀ i, msTermEval M v (ys i) = msTermEval M v (zs i) := by
    intro i
    exact (msFormulaEval_eq_T_iff M rfl _ _ _ v).mp (hcong i M v hsat)
  simp only [msTermEval, funM]
  congr 1
  funext i
  exact hargs i


proof_of predicateInterpC_case1 := by
  -- BEGIN PROOF
      simp only [predicateInterpC]
      rw [if_pos hclosed]


proof_of predicateInterpC_eq := rfl


proof_of msTermEval_cast_congr := by
  cases h; exact heq


proof_of predAtomOf_cong := by
  -- REPAIR(T10-17): proof pending — Split nullary constants and positive predicate applications in congruence.
  sorry


proof_of predicateInterpC_case2 := by
  -- BEGIN PROOF
    rw [predicateInterpC_eq, predicateInterpC_eq]
    have hatom := predAtomOf_cong L C' P ys zs hsurrogate
    by_cases h : semanticEqualityRelationPred L C' (MSBoolSort L)
        (predAtomOf L P ys) (msTopConst L)
    · rw [if_pos h, if_pos (semanticEqualityRelationPred_trans L C' _ _ _ _
        (semanticEqualityRelationPred_symm L C' _ _ _ hatom) h)]
    · rw [if_neg h]
      rw [if_neg]
      intro hz
      exact h (semanticEqualityRelationPred_trans L C' _ _ _ _ hatom hz)


proof_of predicateInterpC_case3 := by
  -- BEGIN PROOF
      simp only [predicateInterpC]
      rw [if_neg hnone]


proof_of closure_isAlgebraCongruence_pred := predicateInterpC_case2 L C' P ys zs hcong
  -- BEGIN PROOF


proof_of msConjunctContains_self := by
  cases Y <;> first | rfl | exact Or.inl rfl


proof_of msConjunctContains_nonConj := by
  cases Y with
  | conj A B => exact absurd rfl (hY A B)
  | _ => exact h


proof_of posEq_isLiteral := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact Or.inl (by simp [MSFormula.isAtomic])


proof_of negEq_isLiteral := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact Or.inr ⟨_, rfl, by simp [MSFormula.isAtomic]⟩


proof_of eqOrNegEq_isLiteral := h.elim posEq_isLiteral negEq_isLiteral


proof_of isLiteral_imp_conjOfLiterals := by
  cases X with
  | conj A B =>
    rcases h with hat | ⟨B', heq, _⟩
    · exact absurd hat (by simp [MSFormula.isAtomic])
    · exact absurd heq (by simp)
  | _ => exact h


proof_of encode_self_contains := msConjunctContains_self _


proof_of encode_literal_isEq := by
  -- A literal is atomic or the negation of an atomic.
  rcases hlit with hat | ⟨B, rfl, hBat⟩
  · -- `A` atomic: falsum (excluded), pred, or eq_.
    cases A with
    | falsum => exact absurd rfl hbot
    | pred P ts =>
      intro X hX
      -- `encode (pred P ts) = msEncodeAtom = eq_ rfl bool (predTerm) ⊤`.
      left
      have hYX : msEncodeConjunction L (MSFormula.pred P ts) = X :=
        msConjunctContains_nonConj (by intro A B h; nomatch h) hX
      exact ⟨rfl, _, _, _, hYX.symm⟩
    | eq_ hL s t u =>
      intro X hX
      left
      have hYX : msEncodeConjunction L (MSFormula.eq_ hL s t u) = X :=
        msConjunctContains_nonConj (by intro A B h; nomatch h) hX
      exact ⟨rfl, _, _, _, hYX.symm⟩
    | _ => exact absurd hat (by simp [MSFormula.isAtomic])
  · -- `A = neg B`, `B` atomic: falsum (excluded), pred, or eq_.
    cases B with
    | falsum => exact absurd rfl hnbot
    | pred P ts =>
      intro X hX
      right
      -- `encode (neg (pred P ts)) = neg (msEncodeAtom …) = neg (eq_ …)`.
      have hYX : msEncodeConjunction L (MSFormula.neg (MSFormula.pred P ts)) = X :=
        msConjunctContains_nonConj (by intro A B h; nomatch h) hX
      exact ⟨rfl, _, _, _, hYX.symm⟩
    | eq_ hL s t u =>
      intro X hX
      right
      have hYX : msEncodeConjunction L (MSFormula.neg (MSFormula.eq_ hL s t u)) = X :=
        msConjunctContains_nonConj (by intro A B h; nomatch h) hX
      exact ⟨rfl, _, _, _, hYX.symm⟩
    | _ => exact absurd hBat (by simp [MSFormula.isAtomic])


proof_of encode_conj_eq := rfl


proof_of encode_neg_eq := by
  cases A <;> rfl


proof_of encode_isConjOfLiterals := by
  intro C
  induction C with
  | conj A B _ ihB =>
    intro hcl hbot
    have hcl' : MSFormula.isLiteral A ∧ Decision.msIsConjunctionOfLiterals B := by
      rcases hcl with hself | h
      · rcases hself with hat | ⟨B', heq, _⟩
        · exact absurd hat (by simp [MSFormula.isAtomic])
        · exact absurd heq (by simp)
      · exact h
    obtain ⟨hAlit, hBcl⟩ := hcl'
    have hAcon : Decision.msConjunctContains (MSFormula.conj A B) A :=
      Or.inr (Or.inl (msConjunctContains_self A))
    have hAbot : A ≠ MSFormula.falsum ∧ A ≠ MSFormula.neg MSFormula.falsum :=
      hbot A hAcon hAlit
    have hBbot : ∀ X, Decision.msConjunctContains B X → MSFormula.isLiteral X →
        (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum) := by
      intro X hX hXlit
      exact hbot X (Or.inr (Or.inr hX)) hXlit
    have hBlit := ihB hBcl hBbot
    rw [encode_conj_eq]
    refine Or.inr ⟨?_, hBlit⟩
    -- `encode A` is a (neg) equation, hence a literal.
    have hAeq := encode_literal_isEq L A hAlit hAbot.1 hAbot.2
      (msEncodeConjunction L A) (encode_self_contains L A)
    exact eqOrNegEq_isLiteral hAeq
  | falsum =>
    intro _ hbot
    exact absurd (hbot MSFormula.falsum rfl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])).1 (by simp)
  | pred P ts =>
    intro _ _
    exact isLiteral_imp_conjOfLiterals (eqOrNegEq_isLiteral (encode_literal_isEq L
      (MSFormula.pred P ts) (Or.inl (by simp [MSFormula.isAtomic])) (by simp) (by simp)
      (msEncodeConjunction L (MSFormula.pred P ts)) (msConjunctContains_self _)))
  | eq_ hL s t u =>
    intro _ _
    exact isLiteral_imp_conjOfLiterals (eqOrNegEq_isLiteral (encode_literal_isEq L
      (MSFormula.eq_ hL s t u) (Or.inl (by simp [MSFormula.isAtomic])) (by simp) (by simp)
      (msEncodeConjunction L (MSFormula.eq_ hL s t u)) (msConjunctContains_self _)))
  | neg A _ =>
    intro hcl hbot
    have hlit : MSFormula.isLiteral (MSFormula.neg A) := hcl
    have hAbot : (MSFormula.neg A) ≠ MSFormula.falsum ∧
        (MSFormula.neg A) ≠ MSFormula.neg MSFormula.falsum :=
      hbot (MSFormula.neg A) rfl hlit
    have hAeq := encode_literal_isEq L (MSFormula.neg A) hlit hAbot.1 hAbot.2
      (msEncodeConjunction L (MSFormula.neg A)) (encode_self_contains L (MSFormula.neg A))
    exact isLiteral_imp_conjOfLiterals (eqOrNegEq_isLiteral hAeq)
  | disj A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | impl A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | equiv_ A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | all s i A _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | ex s i A _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])


proof_of encode_conjuncts_isEq := by
  intro C
  induction C with
  | conj A B _ ihB =>
    intro hcl hbot X hX hXlit
    have hcl' : MSFormula.isLiteral A ∧ Decision.msIsConjunctionOfLiterals B := by
      rcases hcl with hself | h
      · rcases hself with hat | ⟨B', heq, _⟩
        · exact absurd hat (by simp [MSFormula.isAtomic])
        · exact absurd heq (by simp)
      · exact h
    obtain ⟨hAlit, hBcl⟩ := hcl'
    have hAcon : Decision.msConjunctContains (MSFormula.conj A B) A :=
      Or.inr (Or.inl (msConjunctContains_self A))
    have hAbot : A ≠ MSFormula.falsum ∧ A ≠ MSFormula.neg MSFormula.falsum :=
      hbot A hAcon hAlit
    have hBbot : ∀ Y, Decision.msConjunctContains B Y → MSFormula.isLiteral Y →
        (Y ≠ MSFormula.falsum ∧ Y ≠ MSFormula.neg MSFormula.falsum) := by
      intro Y hY hYlit
      exact hbot Y (Or.inr (Or.inr hY)) hYlit
    rw [encode_conj_eq, Decision.msConjunctContains] at hX
    rcases hX with hself | hleft | hright
    · -- `X` is the whole `conj (encode A) (encode B)`, NOT a literal —
      -- contradicts `hXlit`.
      rw [← hself] at hXlit
      exact absurd hXlit (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
    · exact encode_literal_isEq L A hAlit hAbot.1 hAbot.2 X hleft
    · exact ihB hBcl hBbot X hright hXlit
  | falsum =>
    intro _ hbot
    exact absurd (hbot MSFormula.falsum rfl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])).1 (by simp)
  | pred P ts =>
    intro _ _ X hX _
    exact encode_literal_isEq L (MSFormula.pred P ts) (Or.inl (by simp [MSFormula.isAtomic]))
      (by simp) (by simp) X hX
  | eq_ hL s t u =>
    intro _ _ X hX _
    exact encode_literal_isEq L (MSFormula.eq_ hL s t u) (Or.inl (by simp [MSFormula.isAtomic]))
      (by simp) (by simp) X hX
  | neg A _ =>
    intro hcl hbot X hX _
    have hlit : MSFormula.isLiteral (MSFormula.neg A) := hcl
    have hAbot : (MSFormula.neg A) ≠ MSFormula.falsum ∧
        (MSFormula.neg A) ≠ MSFormula.neg MSFormula.falsum :=
      hbot (MSFormula.neg A) rfl hlit
    exact encode_literal_isEq L (MSFormula.neg A) hlit hAbot.1 hAbot.2 X hX
  | disj A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | impl A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | equiv_ A B _ _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | all s i A _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | ex s i A _ =>
    intro hcl
    exact absurd hcl (by simp [Decision.msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])


proof_of noCollision_sat_direction_guarded := by
  -- REPAIR(T10-17): proof pending — Transport the guarded quotient-model proof through occurring sorts and sorted closure.
  sorry


end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

end
