import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of msIsConjunctionOfEquations_iff_blocks := by
  -- REPAIR(T10-13): proof pending — partition literal occurrences into the two sign blocks.
  sorry

proof_of msIsConjunctionOfEquations_of_noPredicates := by
  -- REPAIR(T10-13): proof pending — classify ordinary atoms in a predicate-free language.
  sorry

proof_of msIsGeneratedTermAlgebra_univ := {
  nonempty := fun s => ⟨MSTerm.var s 0, trivial⟩
  closedFunc := fun _ _ _ => trivial
  closedConst := fun _ _ => trivial
  closedSubterm := fun _ _ _ _ => trivial }

proof_of msFormulaEval_disj := rfl


proof_of msFormulaEval_neg := rfl


proof_of msFormulaEval_equiv := rfl


proof_of isLiteral_of_isAtomic := Or.inl h


proof_of msIsConjunctionOfLiterals_of_isLiteral := by
  cases A with
  | conj C D =>
    -- a conjunction is never a literal (not atomic, not a negation).
    rcases h with hat | ⟨B', heq, _⟩
    · exact absurd hat (by simp [MSFormula.isAtomic])
    · exact absurd heq (by simp)
  | _ => exact h


proof_of msIsDNF_of_msIsConjunctionOfLiterals := by
  cases A with
  | disj C D =>
    -- a disjunction is never a conjunction of literals: its only literal
    -- form would be atomic or a negation, both impossible.
    exact absurd h (by
      simp [msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
  | _ => exact h


proof_of msIsDNF_dnfOr := by
  intro B
  induction B with
  | disj C R _ ihR =>
    intro D hB hD
    -- `B = C ∨ R` is a DNF: either `C ∨ R` is a conj-of-literals, or
    -- `C` is a conj-of-literals and `R` is a DNF.
    show msIsDNF (MSFormula.disj C (dnfOr R D))
    rcases hB with hcl | ⟨hCcl, hRdnf⟩
    · -- `C ∨ R` is itself a conj-of-literals: impossible (a disjunction is
      -- never a literal).
      exact absurd hcl (by
        simp [msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
    · -- recurse on `R`.
      exact Or.inr ⟨hCcl, ihR D hRdnf hD⟩
  | falsum => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | pred P ts => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | eq_ hL s t u => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | conj A B _ _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | impl A B _ _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | equiv_ A B _ _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | neg A _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | all s i A _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩
  | ex s i A _ => intro D hB hD; exact Or.inr ⟨hB, hD⟩


proof_of msIsConjunctionOfLiterals_conjConj := by
  intro C
  induction C with
  | conj l R _ ihR =>
    intro D hC hD
    show msIsConjunctionOfLiterals (MSFormula.conj l (conjConj R D))
    rcases hC with hcl | ⟨hllit, hRcl⟩
    · -- `l ∧ R` literal: impossible (a conjunction is never a literal).
      exact absurd hcl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
    · exact Or.inr ⟨hllit, ihR D hRcl hD⟩
  | falsum =>
    intro D hC hD
    exact Or.inr ⟨isLiteral_of_isAtomic (by simp [MSFormula.isAtomic]), hD⟩
  | pred P ts =>
    intro D hC hD
    exact Or.inr ⟨isLiteral_of_isAtomic (by simp [MSFormula.isAtomic]), hD⟩
  | eq_ hL s t u =>
    intro D hC hD
    exact Or.inr ⟨isLiteral_of_isAtomic (by simp [MSFormula.isAtomic]), hD⟩
  | disj A B _ _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩
  | impl A B _ _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩
  | equiv_ A B _ _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩
  | neg A _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩
  | all s i A _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩
  | ex s i A _ => intro D hC hD; exact Or.inr ⟨hC, hD⟩


proof_of msIsDNF_distLeft := by
  intro D
  induction D with
  | disj E R ihE ihR =>
    intro hD
    show msIsDNF (dnfOr (conjConj C E) (distLeft C R))
    rcases hD with hcl | ⟨hEcl, hRdnf⟩
    · -- `E ∨ R` is a conj-of-literals: impossible (it is a disjunction).
      exact absurd hcl (by
        simp [msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
    · -- `E` conj-of-literals, `R` DNF.
      refine msIsDNF_dnfOr _ _ ?_ (ihR hRdnf)
      exact msIsDNF_of_msIsConjunctionOfLiterals
        (msIsConjunctionOfLiterals_conjConj C E hC hEcl)
  | falsum =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | pred P ts =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | eq_ hL s t u =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | conj A B _ _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC hD)
  | impl A B _ _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | equiv_ A B _ _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | neg A _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | all s i A _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))
  | ex s i A _ =>
    intro hD
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_conjConj C _ hC
        (msIsConjunctionOfLiterals_of_isLiteral hD))


proof_of msIsDNF_dnfAnd := by
  intro B
  induction B with
  | disj C R _ ihR =>
    intro D hB hD
    show msIsDNF (dnfOr (distLeft C D) (dnfAnd R D))
    rcases hB with hcl | ⟨hCcl, hRdnf⟩
    · exact absurd hcl (by
        simp [msIsConjunctionOfLiterals, MSFormula.isLiteral, MSFormula.isAtomic])
    · exact msIsDNF_dnfOr _ _ (msIsDNF_distLeft C hCcl D hD) (ihR D hRdnf hD)
  | falsum =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | pred P ts =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | eq_ hL s t u =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | conj A B _ _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ hB D hD
  | impl A B _ _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | equiv_ A B _ _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | neg A _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | all s i A _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD
  | ex s i A _ =>
    intro D hB hD
    exact msIsDNF_distLeft _ (msIsConjunctionOfLiterals_of_isLiteral hB) D hD


proof_of msIsConjunctionOfLiterals_negLit := by
  cases l with
  | neg a =>
    -- `l = ¬a` literal forces `a` atomic; `negLit (¬a) = a` is a literal.
    show msIsConjunctionOfLiterals a
    rcases hl with hat | ⟨a', heq, hat'⟩
    · exact absurd hat (by simp [MSFormula.isAtomic])
    · -- `¬a = ¬a'` so `a = a'` atomic.
      have : a = a' := by injection heq
      exact msIsConjunctionOfLiterals_of_isLiteral
        (isLiteral_of_isAtomic (this ▸ hat'))
  | falsum =>
    exact msIsConjunctionOfLiterals_of_isLiteral
      (Or.inr ⟨_, rfl, by simp [MSFormula.isAtomic]⟩)
  | pred P ts =>
    exact msIsConjunctionOfLiterals_of_isLiteral
      (Or.inr ⟨_, rfl, by simp [MSFormula.isAtomic]⟩)
  | eq_ hL s t u =>
    exact msIsConjunctionOfLiterals_of_isLiteral
      (Or.inr ⟨_, rfl, by simp [MSFormula.isAtomic]⟩)
  | conj A B =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
  | disj A B =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
  | impl A B =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
  | equiv_ A B =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
  | all s i A =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
  | ex s i A =>
    exact absurd hl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])


proof_of msIsDNF_negConj := by
  intro C
  induction C with
  | conj l R _ ihR =>
    intro hC
    show msIsDNF (dnfOr (negLit l) (negConj R))
    rcases hC with hcl | ⟨hllit, hRcl⟩
    · rcases hcl with hat | ⟨_, heq, _⟩
      · exact absurd hat (by simp [MSFormula.isAtomic])
      · exact absurd heq (by simp)
    · exact msIsDNF_dnfOr _ _
        (msIsDNF_of_msIsConjunctionOfLiterals
          (msIsConjunctionOfLiterals_negLit l hllit)) (ihR hRcl)
  | falsum =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ (Or.inl (by simp [MSFormula.isAtomic])))
  | pred P ts =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ (Or.inl (by simp [MSFormula.isAtomic])))
  | eq_ hL s t u =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ (Or.inl (by simp [MSFormula.isAtomic])))
  | disj A B _ _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)
  | impl A B _ _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)
  | equiv_ A B _ _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)
  | neg A _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)
  | all s i A _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)
  | ex s i A _ =>
    intro hC
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_negLit _ hC)


proof_of msIsDNF_dnfNeg := by
  intro B
  induction B with
  | disj C R _ ihR =>
    intro hB
    show msIsDNF (dnfAnd (negConj C) (dnfNeg R))
    rcases hB with hcl | ⟨hCcl, hRdnf⟩
    · rcases hcl with hat | ⟨_, heq, _⟩
      · exact absurd hat (by simp [MSFormula.isAtomic])
      · exact absurd heq (by simp)
    · exact msIsDNF_dnfAnd _ _ (msIsDNF_negConj C hCcl) (ihR hRdnf)
  | falsum =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | pred P ts =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | eq_ hL s t u =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | conj A B _ _ =>
    intro hB
    exact msIsDNF_negConj _ hB
  | impl A B _ _ =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | equiv_ A B _ _ =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | neg A _ =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | all s i A _ =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)
  | ex s i A _ =>
    intro hB
    exact msIsDNF_negConj _ (msIsConjunctionOfLiterals_of_isLiteral hB)


proof_of msIsDNF_toDNF := by
  intro A
  induction A with
  | falsum =>
    intro _
    show msIsDNF (MSFormula.falsum)
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_of_isLiteral (Or.inl (by simp [MSFormula.isAtomic])))
  | pred P ts =>
    intro _
    show msIsDNF (MSFormula.pred P ts)
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_of_isLiteral (Or.inl (by simp [MSFormula.isAtomic])))
  | eq_ hL s t u =>
    intro _
    show msIsDNF (MSFormula.eq_ hL s t u)
    exact msIsDNF_of_msIsConjunctionOfLiterals
      (msIsConjunctionOfLiterals_of_isLiteral (Or.inl (by simp [MSFormula.isAtomic])))
  | neg A ihA =>
    intro hopen
    show msIsDNF (dnfNeg (toDNF A))
    exact msIsDNF_dnfNeg _ (ihA hopen)
  | conj A B ihA ihB =>
    intro hopen
    show msIsDNF (dnfAnd (toDNF A) (toDNF B))
    exact msIsDNF_dnfAnd _ _ (ihA hopen.1) (ihB hopen.2)
  | disj A B ihA ihB =>
    intro hopen
    show msIsDNF (dnfOr (toDNF A) (toDNF B))
    exact msIsDNF_dnfOr _ _ (ihA hopen.1) (ihB hopen.2)
  | impl A B ihA ihB =>
    intro hopen
    show msIsDNF (dnfOr (dnfNeg (toDNF A)) (toDNF B))
    exact msIsDNF_dnfOr _ _ (msIsDNF_dnfNeg _ (ihA hopen.1)) (ihB hopen.2)
  | equiv_ A B ihA ihB =>
    intro hopen
    show msIsDNF
      (dnfOr (dnfAnd (toDNF A) (toDNF B))
        (dnfAnd (dnfNeg (toDNF A)) (dnfNeg (toDNF B))))
    exact msIsDNF_dnfOr _ _
      (msIsDNF_dnfAnd _ _ (ihA hopen.1) (ihB hopen.2))
      (msIsDNF_dnfAnd _ _ (msIsDNF_dnfNeg _ (ihA hopen.1))
        (msIsDNF_dnfNeg _ (ihB hopen.2)))
  | all s i A _ => intro hopen; exact absurd hopen (by simp [MSFormula.isOpen])
  | ex s i A _ => intro hopen; exact absurd hopen (by simp [MSFormula.isOpen])


proof_of eval_dnfOr := by
  intro B
  induction B with
  | disj C R _ ihR =>
    intro D
    show msFormulaEval M (MSFormula.disj C (dnfOr R D)) v = _
    rw [msFormulaEval_disj, ihR D, msFormulaEval_disj]
    cases msFormulaEval M C v <;> cases msFormulaEval M R v <;>
      cases msFormulaEval M D v <;> rfl
  | falsum => intro D; rfl
  | pred P ts => intro D; rfl
  | eq_ hL s t u => intro D; rfl
  | conj A B _ _ => intro D; rfl
  | impl A B _ _ => intro D; rfl
  | equiv_ A B _ _ => intro D; rfl
  | neg A _ => intro D; rfl
  | all s i A _ => intro D; rfl
  | ex s i A _ => intro D; rfl


proof_of eval_conjConj := by
  intro C
  induction C with
  | conj l R _ ihR =>
    intro D
    show msFormulaEval M (MSFormula.conj l (conjConj R D)) v = _
    rw [msFormulaEval_conj, ihR D, msFormulaEval_conj]
    cases msFormulaEval M l v <;> cases msFormulaEval M R v <;>
      cases msFormulaEval M D v <;> rfl
  | falsum => intro D; rfl
  | pred P ts => intro D; rfl
  | eq_ hL s t u => intro D; rfl
  | disj A B _ _ => intro D; rfl
  | impl A B _ _ => intro D; rfl
  | equiv_ A B _ _ => intro D; rfl
  | neg A _ => intro D; rfl
  | all s i A _ => intro D; rfl
  | ex s i A _ => intro D; rfl


proof_of eval_distLeft := by
  intro D
  induction D with
  | disj E R ihE ihR =>
    show msFormulaEval M (dnfOr (conjConj C E) (distLeft C R)) v = _
    rw [eval_dnfOr, eval_conjConj, ihR, msFormulaEval_disj]
    cases msFormulaEval M C v <;> cases msFormulaEval M E v <;>
      cases msFormulaEval M R v <;> rfl
  | falsum => exact eval_conjConj M v C _
  | pred P ts => exact eval_conjConj M v C _
  | eq_ hL s t u => exact eval_conjConj M v C _
  | conj A B _ _ => exact eval_conjConj M v C _
  | impl A B _ _ => exact eval_conjConj M v C _
  | equiv_ A B _ _ => exact eval_conjConj M v C _
  | neg A _ => exact eval_conjConj M v C _
  | all s i A _ => exact eval_conjConj M v C _
  | ex s i A _ => exact eval_conjConj M v C _


proof_of eval_dnfAnd := by
  intro B
  induction B with
  | disj C R _ ihR =>
    intro D
    show msFormulaEval M (dnfOr (distLeft C D) (dnfAnd R D)) v = _
    rw [eval_dnfOr, eval_distLeft, ihR D, msFormulaEval_disj]
    cases msFormulaEval M C v <;> cases msFormulaEval M R v <;>
      cases msFormulaEval M D v <;> rfl
  | falsum => intro D; exact eval_distLeft M v _ D
  | pred P ts => intro D; exact eval_distLeft M v _ D
  | eq_ hL s t u => intro D; exact eval_distLeft M v _ D
  | conj A B _ _ => intro D; exact eval_distLeft M v _ D
  | impl A B _ _ => intro D; exact eval_distLeft M v _ D
  | equiv_ A B _ _ => intro D; exact eval_distLeft M v _ D
  | neg A _ => intro D; exact eval_distLeft M v _ D
  | all s i A _ => intro D; exact eval_distLeft M v _ D
  | ex s i A _ => intro D; exact eval_distLeft M v _ D


proof_of eval_negLit := by
  intro l
  cases l with
  | neg a =>
    show msFormulaEval M a v = hNeg (msFormulaEval M (MSFormula.neg a) v)
    rw [msFormulaEval_neg]
    cases msFormulaEval M a v <;> rfl
  | falsum => rfl
  | pred P ts => rfl
  | eq_ hL s t u => rfl
  | conj A B => rfl
  | disj A B => rfl
  | impl A B => rfl
  | equiv_ A B => rfl
  | all s i A => rfl
  | ex s i A => rfl


proof_of eval_negConj := by
  intro C
  induction C with
  | conj l R _ ihR =>
    show msFormulaEval M (dnfOr (negLit l) (negConj R)) v = _
    rw [eval_dnfOr, eval_negLit, ihR, msFormulaEval_conj]
    cases msFormulaEval M l v <;> cases msFormulaEval M R v <;> rfl
  | falsum => exact eval_negLit M v _
  | pred P ts => exact eval_negLit M v _
  | eq_ hL s t u => exact eval_negLit M v _
  | disj A B _ _ => exact eval_negLit M v _
  | impl A B _ _ => exact eval_negLit M v _
  | equiv_ A B _ _ => exact eval_negLit M v _
  | neg A _ => exact eval_negLit M v _
  | all s i A _ => exact eval_negLit M v _
  | ex s i A _ => exact eval_negLit M v _


proof_of eval_dnfNeg := by
  intro B
  induction B with
  | disj C R _ ihR =>
    show msFormulaEval M (dnfAnd (negConj C) (dnfNeg R)) v = _
    rw [eval_dnfAnd, eval_negConj, ihR, msFormulaEval_disj]
    cases msFormulaEval M C v <;> cases msFormulaEval M R v <;> rfl
  | falsum => exact eval_negConj M v _
  | pred P ts => exact eval_negConj M v _
  | eq_ hL s t u => exact eval_negConj M v _
  | conj A B _ _ => exact eval_negConj M v _
  | impl A B _ _ => exact eval_negConj M v _
  | equiv_ A B _ _ => exact eval_negConj M v _
  | neg A _ => exact eval_negConj M v _
  | all s i A _ => exact eval_negConj M v _
  | ex s i A _ => exact eval_negConj M v _


proof_of eval_toDNF := by
  intro A
  induction A with
  | falsum => intro _; rfl
  | pred P ts => intro _; rfl
  | eq_ hL s t u => intro _; rfl
  | neg A ihA =>
    intro hopen
    show msFormulaEval M (dnfNeg (toDNF A)) v = _
    rw [eval_dnfNeg, ihA hopen, msFormulaEval_neg]
  | conj A B ihA ihB =>
    intro hopen
    show msFormulaEval M (dnfAnd (toDNF A) (toDNF B)) v = _
    rw [eval_dnfAnd, ihA hopen.1, ihB hopen.2, msFormulaEval_conj]
  | disj A B ihA ihB =>
    intro hopen
    show msFormulaEval M (dnfOr (toDNF A) (toDNF B)) v = _
    rw [eval_dnfOr, ihA hopen.1, ihB hopen.2, msFormulaEval_disj]
  | impl A B ihA ihB =>
    intro hopen
    show msFormulaEval M (dnfOr (dnfNeg (toDNF A)) (toDNF B)) v = _
    rw [eval_dnfOr, eval_dnfNeg, ihA hopen.1, ihB hopen.2, msFormulaEval_impl]
    cases msFormulaEval M A v <;> cases msFormulaEval M B v <;> rfl
  | equiv_ A B ihA ihB =>
    intro hopen
    show msFormulaEval M
      (dnfOr (dnfAnd (toDNF A) (toDNF B))
        (dnfAnd (dnfNeg (toDNF A)) (dnfNeg (toDNF B)))) v = _
    rw [eval_dnfOr, eval_dnfAnd, eval_dnfAnd, eval_dnfNeg, eval_dnfNeg,
      ihA hopen.1, ihB hopen.2, msFormulaEval_equiv]
    cases msFormulaEval M A v <;> cases msFormulaEval M B v <;> rfl
  | all s i A _ => intro hopen; exact absurd hopen (by simp [MSFormula.isOpen])
  | ex s i A _ => intro hopen; exact absurd hopen (by simp [MSFormula.isOpen])


proof_of disjunctOf_eval := by
  intro B
  induction B with
  | disj C R ihC ihR =>
    intro Ci hdis hCi
    rw [msFormulaEval_disj]
    rcases hdis with hC | hR
    · rw [ihC Ci hC hCi]; rfl
    · rw [ihR Ci hR hCi]; cases msFormulaEval M C v <;> rfl
  | falsum => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | pred P ts => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | eq_ hL s t u => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | conj A B _ _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | impl A B _ _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | equiv_ A B _ _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | neg A _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | all s i A _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi
  | ex s i A _ => intro Ci hdis hCi; rw [← hdis.1]; exact hCi


proof_of msIsDisjunctOf_self := by
  cases B with
  | disj C D => simp [msIsConjunctionOfLiterals, MSFormula.isLiteral,
      LCS.FirstOrder.ManySorted.MSFormula.isAtomic] at hB
  | _ => exact ⟨rfl, hB⟩


proof_of conjunctContains_eval := by
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


proof_of sat_of_no_complementary_pair := by
  classical
  -- The Herbrand structure on the all-terms term algebra, with the
  -- positive-conjunct predicate valuation.
  let H : (s : L.SortType) → Set (MSTerm L s) := fun _ => (fun _ => True)
  have hTA : Gentzen.MSIsGeneratedTermAlgebra L H := msIsGeneratedTermAlgebra_univ L
  let S : Set (Gentzen.MSSignedFormula L) := trueConjunctsSet C
  let M : MSStructure L := Gentzen.msHintikkaStructure H S hTA
  let v : MSAssignment M := Gentzen.msIdentityAssignment H S hTA
  -- The atom-evaluation fact: a `pred P ts` atom evaluates to `T` iff it is
  -- a conjunct of `C` (via `msTermEvalIdentity` + the `interpPred` clause).
  have hAtomEval : ∀ (P : L.predSymbols)
      (ts : (i : Fin (L.predArity P).length) → MSTerm L ((L.predArity P).get i)),
      msFormulaEval M (MSFormula.pred P ts) v = BoolVal.T ↔
        msConjunctContains C (MSFormula.pred P ts) := by
    intro P ts
    have hargs : (fun i => msTermEval M v (ts i))
        = (fun i => (⟨ts i, trivial⟩ : { t // t ∈ H _ })) :=
      funext (fun i => Gentzen.msTermEvalIdentity (ts i) trivial)
    simp only [msFormulaEval, predM]
    rw [hargs]
    simp only [M, Gentzen.msHintikkaStructure]
    -- `interpPred … = if trueF (pred P ts) ∈ S then T else F`.
    constructor
    · intro h
      by_cases hmem : Gentzen.MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S
      · obtain ⟨A, hAeq, hAcon⟩ := hmem
        have : A = MSFormula.pred P ts := by
          injection hAeq with hAeq; exact hAeq.symm
        rwa [this] at hAcon
      · rw [if_neg hmem] at h; exact absurd h (by decide)
    · intro hcon
      have hmem : Gentzen.MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S :=
        ⟨MSFormula.pred P ts, rfl, hcon⟩
      rw [if_pos hmem]
  -- Every literal conjunct of `C` evaluates to `T`, by induction on the
  -- conjunction tree. We strengthen the statement: every conjunct `X` of `C`
  -- (with `C` a conj-of-literals, no-⊥, no-complementary-pair) evaluates `T`.
  have hLeaf : ∀ X, msConjunctContains C X → MSFormula.isLiteral X →
      msFormulaEval M X v = BoolVal.T := by
    intro X hXin hXlit
    rcases hXlit with hat | ⟨B, rfl, hBat⟩
    · -- `X` atomic: with no equality it is `falsum` or `pred …`; `hNoBot`
      -- excludes `falsum`, so it is a positive atom — a conjunct of `C`.
      cases X with
      | falsum => exact absurd rfl (hNoBot _ hXin (Or.inl trivial)).1
      | pred P ts => exact (hAtomEval P ts).mpr hXin
      | eq_ hL _ _ _ => exact absurd hL (by rw [hEq]; decide)
      | _ => exact absurd hat (by simp [MSFormula.isAtomic])
    · -- `X = ¬B`, `B` atomic: `B` is `falsum` (excluded by `hNoBot`) or a
      -- `pred …` atom; the latter would be a positive conjunct, giving a
      -- complementary pair (contradiction with `hno`), so its valuation is `F`.
      cases B with
      | falsum => exact absurd rfl (hNoBot _ hXin (Or.inr ⟨_, rfl, trivial⟩)).2
      | pred P ts =>
        rw [msFormulaEval_neg]
        by_cases hPcon : msConjunctContains C (MSFormula.pred P ts)
        · exact absurd ⟨MSFormula.pred P ts, hPcon, hXin, trivial⟩ hno
        · rw [show msFormulaEval M (MSFormula.pred P ts) v = BoolVal.F from by
              cases hev : msFormulaEval M (MSFormula.pred P ts) v with
              | T => exact absurd ((hAtomEval P ts).mp hev) hPcon
              | F => rfl]
          rfl
      | eq_ hL _ _ _ => exact absurd hL (by rw [hEq]; decide)
      | _ => exact absurd hBat (by simp [MSFormula.isAtomic])
  -- Now evaluate `C` itself by induction on its conjunction tree.
  have hConj : ∀ D, msIsConjunctionOfLiterals D →
      (∀ X, msConjunctContains D X → msConjunctContains C X) →
      msFormulaEval M D v = BoolVal.T := by
    intro D
    induction D with
    | conj A B _ ihB =>
      intro hDcl hsub
      rcases hDcl with hself | ⟨hAlit, hBcl⟩
      · -- a conjunction is never a literal.
        exact absurd hself (by
          simp [MSFormula.isLiteral, MSFormula.isAtomic])
      · rw [msFormulaEval_conj, hAnd_eq_T_iff]
        refine ⟨?_, ?_⟩
        · -- left conjunct `A` is a literal of `C`.
          have hAself : msConjunctContains A A := by
            cases A <;> first | rfl | exact Or.inl rfl
          have hAin : msConjunctContains (MSFormula.conj A B) A :=
            Or.inr (Or.inl hAself)
          exact hLeaf A (hsub A hAin) hAlit
        · -- right subtree `B` recurses.
          exact ihB hBcl (fun X hXin =>
            hsub X (Or.inr (Or.inr hXin)))
    | falsum =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | pred P ts =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | eq_ hL s t u =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | disj A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | impl A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | equiv_ A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | neg A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | all s i A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | ex s i A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
  exact ⟨M, v, hConj C hClit (fun _ h => h)⟩


end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
