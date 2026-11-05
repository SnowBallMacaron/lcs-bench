import LCS.Propositional.Semantics

-- Proofs follow the front declaration order.

namespace LCS.Propositional.Semantics

open LCS.Propositional.Syntax

namespace BoolVal

end BoolVal

proof_of evalExt_depends_on_vars := by
  -- BEGIN PROOF
  induction A with
  | var n =>
    simp only [evalExt]
    exact h n rfl
  | fls =>
    simp only [evalExt]
  | neg A ih =>
    simp only [evalExt]
    rw [ih h]
  | conj A B ihA ihB =>
    simp only [evalExt]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | disj A B ihA ihB =>
    simp only [evalExt]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | impl A B ihA ihB =>
    simp only [evalExt]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | equiv_ A B ihA ihB =>
    simp only [evalExt]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]

proof_of tautology_iff_neg_unsatisfiable := by
  -- BEGIN PROOF
  constructor
  · intro hValid
    intro ⟨v, hv⟩
    simp only [evalExt, hNeg] at hv
    have := hValid v
    match heq : evalExt v A with
    | .T => simp [heq] at hv
    | .F => simp [heq] at this
  · intro hUnsat
    intro v
    simp only [isUnsatisfiable, isSatisfiable, not_exists] at hUnsat
    have := hUnsat v
    simp only [evalExt, hNeg] at this
    match heq : evalExt v A with
    | .T => rfl
    | .F => simp [heq] at this

proof_of modusPonensConsequence := by
  intro v hPremises
  have hA := hPremises A (Or.inl rfl)
  have hImpl := hPremises (.impl A B) (Or.inr rfl)
  simp only [evalExt, hA] at hImpl
  cases hB : evalExt v B <;> simp_all [hImplies]

proof_of conjIntroConsequence := by
  intro v hPremises
  have hA := hPremises A (Or.inl rfl)
  have hB := hPremises B (Or.inr rfl)
  simp only [evalExt, hA, hB, hAnd]

proof_of modusTollensConsequence := by
  intro v hPremises
  have hImpl := hPremises (.impl A B) (Or.inl rfl)
  have hNegB := hPremises (.neg B) (Or.inr rfl)
  simp only [evalExt] at hImpl hNegB ⊢
  cases hA : evalExt v A <;> cases hB : evalExt v B <;>
    simp_all [hNeg, hImplies]

proof_of truthTableAllTrue := by
  -- BEGIN PROOF
  intro row hrow
  simp only [truthTableContrapositive, List.mem_cons, List.mem_nil_iff, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl <;> decide

proof_of identityTautology_valid := by
  -- BEGIN PROOF
  intro v
  simp only [identityTautology, evalExt, hImplies]
  cases evalExt v A with
  | T => rfl
  | F => rfl

proof_of doubleNegTautology_valid := by
  -- BEGIN PROOF
  intro v
  simp only [doubleNegTautology, evalExt, hNeg, hImplies]
  cases evalExt v A with
  | T => rfl
  | F => rfl

proof_of contrapositiveTautology_valid := by
  -- BEGIN PROOF
  intro v
  simp only [contrapositiveTautology, evalExt, hImplies, hNeg, hEquiv]
  cases v 0 with
  | T => cases v 1 with
    | T => rfl
    | F => rfl
  | F => cases v 1 with
    | T => rfl
    | F => rfl

proof_of satisfiableExample_assignment := rfl

proof_of satisfiableExample_satisfiable := by
  -- BEGIN PROOF
  refine ⟨fun n => if n = 0 then BoolVal.F else if n = 1 then BoolVal.T else BoolVal.F, ?_⟩
  exact satisfiableExample_assignment

proof_of unsatisfiableExample_unsatisfiable := by
  -- BEGIN PROOF
  intro ⟨v, hv⟩
  simp only [unsatisfiableExample, evalExt, hAnd, hOr, hNeg] at hv
  cases heq0 : v 0 with
  | T => cases heq1 : v 1 with
    | T => simp [heq0, heq1] at hv
    | F => simp [heq0, heq1] at hv
  | F => simp [heq0] at hv

end LCS.Propositional.Semantics
