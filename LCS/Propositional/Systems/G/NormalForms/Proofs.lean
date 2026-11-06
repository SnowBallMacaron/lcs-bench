import LCS.Propositional.Systems.G.NormalForms

namespace LCS.Propositional.Systems.G.NormalForms

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Semantics.TruthFunctions

helper /-- Double negation elimination identity: ¬¬A ≃ A. -/
theorem logEquivN_double_neg_identity (A : PropFormulaNormalized) :
    logEquivN (.neg (.neg A)) A :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hNeg]
  cases evalExtN v A <;> rfl

helper /-- De Morgan conjunction identity: ¬(A ∧ B) ≃ (¬A ∨ ¬B). -/
theorem logEquivN_demorgan_conj_identity (A B : PropFormulaNormalized) :
    logEquivN (.neg (.conj A B)) (.disj (.neg A) (.neg B)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hNeg, hAnd, hOr]
  cases evalExtN v A <;> cases evalExtN v B <;> rfl

helper /-- De Morgan disjunction identity: ¬(A ∨ B) ≃ (¬A ∧ ¬B). -/
theorem logEquivN_demorgan_disj_identity (A B : PropFormulaNormalized) :
    logEquivN (.neg (.disj A B)) (.conj (.neg A) (.neg B)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hNeg, hOr, hAnd]
  cases evalExtN v A <;> cases evalExtN v B <;> rfl

helper /-- Left distributivity of disjunction over conjunction:
    A ∨ (B ∧ C) ≃ (A ∨ B) ∧ (A ∨ C). -/
theorem logEquivN_disj_conj_distrib_left (A B C : PropFormulaNormalized) :
    logEquivN (.disj A (.conj B C))
      (.conj (.disj A B) (.disj A C)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hOr, hAnd]
  cases evalExtN v A <;> cases evalExtN v B <;> cases evalExtN v C <;> rfl

helper /-- Right distributivity of disjunction over conjunction:
    (B ∧ C) ∨ A ≃ (B ∨ A) ∧ (C ∨ A). -/
theorem logEquivN_disj_conj_distrib_right (A B C : PropFormulaNormalized) :
    logEquivN (.disj (.conj B C) A)
      (.conj (.disj B A) (.disj C A)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hOr, hAnd]
  cases evalExtN v A <;> cases evalExtN v B <;> cases evalExtN v C <;> rfl

helper /-- Conjunction associativity identity: (A ∧ B) ∧ C ≃ A ∧ (B ∧ C). -/
theorem logEquivN_conj_assoc_identity (A B C : PropFormulaNormalized) :
    logEquivN (.conj (.conj A B) C) (.conj A (.conj B C)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hAnd]
  cases evalExtN v A <;> cases evalExtN v B <;> cases evalExtN v C <;> rfl

helper /-- Disjunction associativity identity: (A ∨ B) ∨ C ≃ A ∨ (B ∨ C). -/
theorem logEquivN_disj_assoc_identity (A B C : PropFormulaNormalized) :
    logEquivN (.disj (.disj A B) C) (.disj A (.disj B C)) :=
-- BEGIN PROOF
by
  intro v; simp only [evalExtN, hEquiv, hOr]
  cases evalExtN v A <;> cases evalExtN v B <;> cases evalExtN v C <;> rfl

helper theorem logEquivN_trans {A B C : PropFormulaNormalized}
    (h1 : logEquivN A B) (h2 : logEquivN B C) : logEquivN A C := by
-- BEGIN PROOF
  have h1' := (tautological_equiv_iff_equal_evalN A B).mp h1
  have h2' := (tautological_equiv_iff_equal_evalN B C).mp h2
  intro v; simp only [hEquiv]
  rw [h1' v, h2' v]; cases evalExtN v C <;> rfl

helper theorem toNNFaux_isNNF : (pol : Bool) → (A : PropFormulaNormalized) →
    PropFormulaNormalized.isNNF (toNNFaux pol A)
  | true, .var _ => trivial
  | false, .var _ => trivial
  | true, .neg A => toNNFaux_isNNF false A
  | false, .neg A => toNNFaux_isNNF true A
  | true, .conj A B => ⟨toNNFaux_isNNF true A, toNNFaux_isNNF true B⟩
  | false, .conj A B => ⟨toNNFaux_isNNF false A, toNNFaux_isNNF false B⟩
  | true, .disj A B => ⟨toNNFaux_isNNF true A, toNNFaux_isNNF true B⟩
  | false, .disj A B => ⟨toNNFaux_isNNF false A, toNNFaux_isNNF false B⟩
  | true, .impl A B => ⟨toNNFaux_isNNF false A, toNNFaux_isNNF true B⟩
  | false, .impl A B => ⟨toNNFaux_isNNF true A, toNNFaux_isNNF false B⟩

helper theorem toNNF_isNNF (A : PropFormulaNormalized) : PropFormulaNormalized.isNNF (toNNF A) :=
-- BEGIN PROOF
  toNNFaux_isNNF true A

helper theorem toNNFaux_equiv (pol : Bool) (A : PropFormulaNormalized) (v : Valuation) :
    evalExtN v (toNNFaux pol A) =
      if pol then evalExtN v A else hNeg (evalExtN v A) := by
-- BEGIN PROOF
  induction A generalizing pol with
  | var n => cases pol <;> rfl
  | neg A ih =>
    cases pol <;> simp only [toNNFaux]
    · -- pol = false: goal is evalExtN v (toNNFaux true A) = hNeg (evalExtN v (.neg A))
      rw [ih true]; simp [evalExtN, hNeg]; cases evalExtN v A <;> rfl
    · -- pol = true: goal is evalExtN v (toNNFaux false A) = evalExtN v (.neg A)
      rw [ih false]; simp [evalExtN, hNeg]
  | conj A B ihA ihB =>
    cases pol <;> simp only [toNNFaux, evalExtN, hOr, hAnd]
    · rw [ihA false, ihB false]; simp [hNeg]
      cases evalExtN v A <;> cases evalExtN v B <;> rfl
    · rw [ihA true, ihB true]; simp
  | disj A B ihA ihB =>
    cases pol <;> simp only [toNNFaux, evalExtN, hAnd, hOr]
    · rw [ihA false, ihB false]; simp [hNeg]
      cases evalExtN v A <;> cases evalExtN v B <;> rfl
    · rw [ihA true, ihB true]; simp
  | impl A B ihA ihB =>
    cases pol <;> simp only [toNNFaux, evalExtN, hAnd, hOr]
    · rw [ihA true, ihB false]; simp [hNeg, hImplies]
      cases evalExtN v A <;> cases evalExtN v B <;> rfl
    · rw [ihA false, ihB true]; simp [hNeg, hImplies]
      cases evalExtN v A <;> cases evalExtN v B <;> rfl

helper theorem toNNF_logEquivN (A : PropFormulaNormalized) : logEquivN A (toNNF A) := by
-- BEGIN PROOF
  intro v; simp only [hEquiv, toNNF]
  rw [toNNFaux_equiv true A v]; simp; cases evalExtN v A <;> rfl

helper def cnfConj (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  .conj A B

helper theorem cnfConj_isCNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isCNF A) (hB : PropFormulaNormalized.isCNF B) :
    PropFormulaNormalized.isCNF (cnfConj A B) := ⟨hA, hB⟩

helper /-- Distribute one clause over a normal form. -/
def cnfDistribute (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  match B with
  | .conj C D => .conj (cnfDistribute A C) (cnfDistribute A D)
  | _ => .disj A B

helper theorem cnfDistribute_isCNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isClause A) (hB : PropFormulaNormalized.isCNF B) :
    PropFormulaNormalized.isCNF (cnfDistribute A B) := by
  induction B with
  | conj C D ihC ihD => exact ⟨ihC hB.1, ihD hB.2⟩
  | var _ | neg _ _ | disj _ _ _ _ | impl _ _ _ _ => exact ⟨hA, hB⟩

helper /-- Distribute both normal forms, preserving their binary grouping. -/
def cnfDisj (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  match A with
  | .conj C D => .conj (cnfDisj C B) (cnfDisj D B)
  | _ => cnfDistribute A B

helper theorem cnfDisj_isCNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isCNF A) (hB : PropFormulaNormalized.isCNF B) :
    PropFormulaNormalized.isCNF (cnfDisj A B) := by
  induction A with
  | conj C D ihC ihD => exact ⟨ihC hA.1, ihD hA.2⟩
  | var _ | neg _ _ | disj _ _ _ _ | impl _ _ _ _ => exact cnfDistribute_isCNF _ B hA hB

helper def nnfToCNF : PropFormulaNormalized → PropFormulaNormalized
  | .var n => .var n
  | .neg (.var n) => .neg (.var n)
  | .conj A B => cnfConj (nnfToCNF A) (nnfToCNF B)
  | .disj A B => cnfDisj (nnfToCNF A) (nnfToCNF B)
  | A => A

helper theorem nnfToCNF_isCNF (A : PropFormulaNormalized) (hnnf : PropFormulaNormalized.isNNF A) :
    PropFormulaNormalized.isCNF (nnfToCNF A) := by
-- BEGIN PROOF
  induction A with
  | var _ => trivial
  | neg A' => cases A' with
    | var _ => trivial
    | _ => simp [PropFormulaNormalized.isNNF] at hnnf
  | conj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToCNF]
    exact cnfConj_isCNF _ _ (ihA hA) (ihB hB)
  | disj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToCNF]
    exact cnfDisj_isCNF _ _ (ihA hA) (ihB hB)
  | impl _ _ _ _ => simp [PropFormulaNormalized.isNNF] at hnnf

helper def dnfDisj (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  .disj A B

helper theorem dnfDisj_eval (v : Valuation) (A B : PropFormulaNormalized) :
    evalExtN v (dnfDisj A B) = hOr (evalExtN v A) (evalExtN v B) := rfl

helper theorem dnfDisj_isDNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isDNF A) (hB : PropFormulaNormalized.isDNF B) :
    PropFormulaNormalized.isDNF (dnfDisj A B) := ⟨hA, hB⟩

helper /-- Distribute one term over a normal form. -/
def dnfDistribute (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  match B with
  | .disj C D => .disj (dnfDistribute A C) (dnfDistribute A D)
  | _ => .conj A B

helper theorem dnfDistribute_eval (v : Valuation) (A B : PropFormulaNormalized) :
    evalExtN v (dnfDistribute A B) = hAnd (evalExtN v A) (evalExtN v B) := by
  induction B with
  | disj C D ihC ihD =>
    simp only [dnfDistribute, evalExtN, ihC, ihD]
    cases evalExtN v A <;> cases evalExtN v C <;> cases evalExtN v D <;> rfl
  | var _ | neg _ _ | conj _ _ _ _ | impl _ _ _ _ => rfl

helper theorem dnfDistribute_isDNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isConjunctiveTerm A) (hB : PropFormulaNormalized.isDNF B) :
    PropFormulaNormalized.isDNF (dnfDistribute A B) := by
  induction B with
  | disj C D ihC ihD => exact ⟨ihC hB.1, ihD hB.2⟩
  | var _ | neg _ _ | conj _ _ _ _ | impl _ _ _ _ => exact ⟨hA, hB⟩

helper /-- Distribute both normal forms, preserving their binary grouping. -/
def dnfConj (A B : PropFormulaNormalized) : PropFormulaNormalized :=
  match A with
  | .disj C D => .disj (dnfConj C B) (dnfConj D B)
  | _ => dnfDistribute A B

helper theorem dnfConj_eval (v : Valuation) (A B : PropFormulaNormalized) :
    evalExtN v (dnfConj A B) = hAnd (evalExtN v A) (evalExtN v B) := by
  induction A with
  | disj C D ihC ihD =>
    simp only [dnfConj, evalExtN, ihC, ihD]
    cases evalExtN v C <;> cases evalExtN v D <;> cases evalExtN v B <;> rfl
  | var _ | neg _ _ | conj _ _ _ _ | impl _ _ _ _ => exact dnfDistribute_eval v _ B

helper theorem dnfConj_isDNF (A B : PropFormulaNormalized)
    (hA : PropFormulaNormalized.isDNF A) (hB : PropFormulaNormalized.isDNF B) :
    PropFormulaNormalized.isDNF (dnfConj A B) := by
  induction A with
  | disj C D ihC ihD => exact ⟨ihC hA.1, ihD hA.2⟩
  | var _ | neg _ _ | conj _ _ _ _ | impl _ _ _ _ => exact dnfDistribute_isDNF _ B hA hB

helper def nnfToDNF : PropFormulaNormalized → PropFormulaNormalized
  | .var n => .var n
  | .neg (.var n) => .neg (.var n)
  | .disj A B => dnfDisj (nnfToDNF A) (nnfToDNF B)
  | .conj A B => dnfConj (nnfToDNF A) (nnfToDNF B)
  | A => A

helper theorem nnfToDNF_eval (A : PropFormulaNormalized) (v : Valuation)
    (hnnf : PropFormulaNormalized.isNNF A) :
    evalExtN v (nnfToDNF A) = evalExtN v A := by
-- BEGIN PROOF
  induction A with
  | var _ => rfl
  | neg A' => cases A' with
    | var _ => rfl
    | _ => simp [PropFormulaNormalized.isNNF] at hnnf
  | disj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToDNF]; rw [dnfDisj_eval, ihA hA, ihB hB]; rfl
  | conj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToDNF]; rw [dnfConj_eval, ihA hA, ihB hB]; rfl
  | impl _ _ _ _ => simp [PropFormulaNormalized.isNNF] at hnnf

helper theorem nnfToDNF_isDNF (A : PropFormulaNormalized) (hnnf : PropFormulaNormalized.isNNF A) :
    PropFormulaNormalized.isDNF (nnfToDNF A) := by
-- BEGIN PROOF
  induction A with
  | var _ => trivial
  | neg A' => cases A' with
    | var _ => trivial
    | _ => simp [PropFormulaNormalized.isNNF] at hnnf
  | disj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToDNF]; exact dnfDisj_isDNF _ _ (ihA hA) (ihB hB)
  | conj A B ihA ihB =>
    have ⟨hA, hB⟩ := hnnf
    simp only [nnfToDNF]; exact dnfConj_isDNF _ _ (ihA hA) (ihB hB)
  | impl _ _ _ _ => simp [PropFormulaNormalized.isNNF] at hnnf

helper theorem toNNFaux_rewrite (pol : Bool) (A : PropFormulaNormalized)
    (hA : usesOnlyAndOrNot A) :
    CNFRewrite (if pol then A else .neg A) (toNNFaux pol A) := by
  induction A generalizing pol with
  | var n => cases pol <;> exact .refl _
  | neg A ih =>
    cases pol with
    | false => exact .trans (.doubleNeg A) (ih true hA)
    | true => exact ih false hA
  | conj A B ihA ihB =>
    cases pol with
    | false => exact .trans (.deMorganConj A B) (.disj (ihA false hA.1) (ihB false hA.2))
    | true => exact .conj (ihA true hA.1) (ihB true hA.2)
  | disj A B ihA ihB =>
    cases pol with
    | false => exact .trans (.deMorganDisj A B) (.conj (ihA false hA.1) (ihB false hA.2))
    | true => exact .disj (ihA true hA.1) (ihB true hA.2)
  | impl _ _ _ _ => exact False.elim hA

helper theorem cnfDistribute_rewrite (A B : PropFormulaNormalized) :
    CNFRewrite (.disj A B) (cnfDistribute A B) := by
  induction B with
  | conj C D ihC ihD => exact .trans (.distributeLeft A C D) (.conj ihC ihD)
  | var _ | neg _ _ | disj _ _ _ _ | impl _ _ _ _ => exact .refl _

helper theorem cnfDisj_rewrite (A B : PropFormulaNormalized) :
    CNFRewrite (.disj A B) (cnfDisj A B) := by
  induction A with
  | conj C D ihC ihD => exact .trans (.distributeRight B C D) (.conj ihC ihD)
  | var _ | neg _ _ | disj _ _ _ _ | impl _ _ _ _ => exact cnfDistribute_rewrite _ B

helper theorem nnfToCNF_rewrite (A : PropFormulaNormalized) : CNFRewrite A (nnfToCNF A) := by
  induction A with
  | var _ => exact .refl _
  | neg A _ => cases A <;> exact .refl _
  | conj A B ihA ihB => exact .conj ihA ihB
  | disj A B ihA ihB => exact .trans (.disj ihA ihB) (cnfDisj_rewrite _ _)
  | impl _ _ _ _ => exact .refl _

proof_of cnf_transformation := by
  -- BEGIN PROOF
    have h : CNFRewrite A (nnfToCNF (toNNF A)) :=
      .trans (toNNFaux_rewrite true A hA) (nnfToCNF_rewrite _)
    exact ⟨_, nnfToCNF_isCNF _ (toNNF_isNNF A), h, h.sound⟩


proof_of nnf_existence := ⟨toNNF A, toNNF_isNNF A, toNNF_logEquivN A⟩
  -- BEGIN PROOF


proof_of cnf_existence := by
  -- BEGIN PROOF
    have hnnf := toNNF_isNNF A
    refine ⟨nnfToCNF (toNNF A), nnfToCNF_isCNF _ hnnf, ?_⟩
    exact logEquivN_trans (toNNF_logEquivN A) (nnfToCNF_rewrite _).sound


proof_of dnf_existence := by
  -- BEGIN PROOF
    have hnnf := toNNF_isNNF A
    have hnnfEquiv := toNNF_logEquivN A
    refine ⟨nnfToDNF (toNNF A), nnfToDNF_isDNF _ hnnf, ?_⟩
    apply logEquivN_trans hnnfEquiv
    intro v; simp only [hEquiv]
    rw [nnfToDNF_eval _ v hnnf]; cases evalExtN v (toNNF A) <;> rfl


proof_of theorem_3_4_2 := ⟨cnf_existence A, dnf_existence A⟩
  -- BEGIN PROOF


proof_of exCNFresult_isCNF := by
  -- BEGIN PROOF
    simp only [exCNFresult, PropFormulaNormalized.isCNF, PropFormulaNormalized.isClause]
    exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩


proof_of exCNFresult_equiv := by
  -- BEGIN PROOF
    intro v
    simp only [exCNFviaSearchFormula, exCNFresult, evalExtN, hEquiv, hImplies, hNeg, hAnd, hOr]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl


proof_of exDNFresult_isDNF := by
  -- BEGIN PROOF
    simp [exDNFresult, PropFormulaNormalized.isDNF, PropFormulaNormalized.isConjunctiveTerm]


proof_of exDNFresult_equiv := by
  -- BEGIN PROOF
    intro v
    simp only [exDNFviaSearchFormula, exDNFresult, evalExtN, hEquiv, hImplies, hNeg, hAnd, hOr]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl


proof_of exNNFConverted_isNNF := by
  -- BEGIN PROOF
    unfold exNNFConverted PropFormulaNormalized.isNNF
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩


proof_of exCNFviaNNFResult_isCNF := by
  -- BEGIN PROOF
    simp only [exCNFviaNNFResult, PropFormulaNormalized.isCNF, PropFormulaNormalized.isClause]
    exact ⟨⟨⟨trivial, trivial⟩, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩


proof_of exCNFviaNNFResult_equiv := by
  -- BEGIN PROOF
    intro v
    simp only [exCNFviaNNFFormula, exCNFviaNNFResult, evalExtN, hEquiv, hImplies, hNeg, hAnd, hOr]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl


proof_of exImplEliminated_equiv := by
  intro v
  simp only [exCNFviaNNFFormula, exImplEliminated, evalExtN, hEquiv, hImplies, hNeg, hOr]
  cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl


proof_of exNNFConverted_rewrite := toNNFaux_rewrite true exImplEliminated ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩


proof_of exCNFviaNNFResult_rewrite := .trans (.distributeRight _ _ _)
    (.conj (.symm (.assocDisj _ _ _)) (.symm (.assocDisj _ _ _)))


proof_of exCNF_nonuniqueness := by
  refine ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩,
    ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩, ?_, ?_⟩
  · intro h
    cases h
  · intro v
    simp only [exCNFNonuniqueFirst, exCNFNonuniqueSecond, evalExtN, hEquiv, hAnd, hOr, hNeg]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> rfl


proof_of exCNFSearchTree_leaves := rfl


proof_of exDNFSearchTree_leaves := rfl


proof_of exCNFSearchTree_nonaxiom_leaves := by
  rw [exCNFSearchTree_leaves]
  simp [isAxiom]


proof_of exDNFSearchTree_nonaxiom_leaves := by
  rw [exDNFSearchTree_leaves]
  simp [isAxiom]


proof_of exCNFSearchTree_atomic_leaves := by
  rw [exCNFSearchTree_leaves]
  simp


proof_of exDNFSearchTree_atomic_leaves := by
  rw [exDNFSearchTree_leaves]
  simp

end LCS.Propositional.Systems.G.NormalForms
