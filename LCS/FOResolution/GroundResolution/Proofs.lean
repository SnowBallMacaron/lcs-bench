import LCS.FOResolution.GroundResolution

namespace LCS.FOResolution.GroundResolution

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence

proof_of ordinaryGroundResolution_equality_counterexample := by
  constructor
  · intro M s h
    exact h rfl
  · rintro ⟨D, hD⟩
    apply resolution_soundness _ D hD
    refine ⟨fun _ => false, ?_⟩
    intro C hC
    have hC' : C = Clause.single (.neg (encode (.eq_ hEq (.const a) (.const a)))) :=
      (LCS.Finset.mem_singleton _ _).mp hC
    subst C
    exact ⟨_, (LCS.Finset.mem_singleton _ _).mpr rfl, rfl⟩

proof_of equalityGroundRules_requirements := by
  refine ⟨?_, ?_, ?_⟩
  · intro ax
    exact ⟨LKeProofTree.eqAxiom hEq ax, True.intro⟩
  · intro A Γ Δ Λ Θ hA ⟨T1, hT1⟩ ⟨T2, hT2⟩
    exact ⟨LKeProofTree.cut A Γ Δ Λ Θ T1 T2, hA, hT1, hT2⟩
  · intro seq _hQF hValid
    exact lkeNoEssentialCuts_of_sequentValid seq hValid

open LCS.FOResolution.Unification

helper theorem exAtomMap (sigma : Nat → Term exClauseFormLang)
    (s t : Term exClauseFormLang) :
    (exPred_P s t).mapTerms (fun u => termSubstAll u sigma) =
      exPred_P (termSubstAll s sigma) (termSubstAll t sigma) := by
  change FOAtomCore.predN ExClausePred.P (fun i => termSubstAll (vec2 s t i) sigma) =
    FOAtomCore.predN ExClausePred.P (vec2 (termSubstAll s sigma) (termSubstAll t sigma))
  apply congrArg (FOAtomCore.predN (L := exClauseFormLang) ExClausePred.P)
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, h⟩ =>
    change n + 2 < 2 at h
    omega

proof_of exGroundSubstitutions_support := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : n = 1 ∨ n = 4 <;>
      simp [exGroundSubst_G1, h, exSkolemConst_a]
  · intro n
    by_cases h : n = 2 <;> simp [exGroundSubst_G2, h, exSkolemConst_a]
  · intro n
    by_cases h : n = 3 <;> simp [exGroundSubst_G3, h, exSkolemConst_a]
  · intro n
    by_cases h1 : n = 1
    · simp [exGroundSubst_G4, h1, exGroundTerm_fa]
    · by_cases h4 : n = 4 <;>
        simp [exGroundSubst_G4, h1, h4, exSkolemConst_a]
  · intro n
    by_cases h : n = 1 ∨ n = 2 ∨ n = 4 <;>
      simp [exUnificationSubst, h, exSkolemConst_a]

proof_of exGroundClause_G1_image := by
  simp [exClause_C1, exGroundClause_G1, exLiteralSubst, exAtomMap,
    termSubstAll, exGroundSubst_G1, exSkolemConst_a]

proof_of exGroundClause_G2_image := by
  simp [exClause_C2, exGroundClause_G2, exLiteralSubst, exAtomMap,
    termSubstAll, exGroundSubst_G2, exSkolemConst_a, exSkolemFunc_f,
    exGroundTerm_fa]

proof_of exGroundClause_G3_image := by
  simp [exClause_C3, exGroundClause_G3, exLiteralSubst, exAtomMap,
    termSubstAll, exGroundSubst_G3, exSkolemConst_a, exSkolemFunc_f,
    exGroundTerm_fa]

proof_of exGroundClause_G4_image := by
  simp [exClause_C1, exGroundClause_G4, exLiteralSubst, exAtomMap,
    termSubstAll, exGroundSubst_G4, exSkolemConst_a, exGroundTerm_fa]

proof_of exUnificationSubsets := by
  refine ⟨fun _ h => h, ?_, rfl⟩
  intro lit h
  simp only [exUnificationRight, List.mem_cons, List.not_mem_nil, or_false] at h
  subst lit
  exact List.mem_cons_of_mem _ List.mem_cons_self

proof_of exUnificationGroundImages := by
  constructor <;> intro lit
  · simp [exClause_C1, exGroundClause_G1, exLiteralSubst, exAtomMap,
      termSubstAll, exUnificationSubst, exSkolemConst_a]
  · simp [exClause_C2, exGroundClause_G2, exLiteralSubst, exAtomMap,
      termSubstAll, exUnificationSubst, exSkolemConst_a, exSkolemFunc_f,
      exGroundTerm_fa]

proof_of exUnificationCommonImage := by
  rw [exUnificationSubsets.2.2] at h
  simp only [exUnificationRight, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl) | rfl <;>
    simp [exLiteralSubst, exAtomMap, termSubstAll,
      exUnificationSubst, exSkolemConst_a]

proof_of exGroundGraph_inferenceVertices := by rfl

proof_of exGroundGraph_shared_G1 := by exact ⟨rfl, rfl, rfl⟩

helper theorem exGroundGraphUnfoldAt_tree (v : Fin 8) :
    exGroundGraphUnfoldAt v =
      match v.val with
      | 0 => .axiom_ exGroundClause_G1
      | 1 => .axiom_ exGroundClause_G2
      | 2 => .axiom_ exGroundClause_G3
      | 3 => .axiom_ exGroundClause_G4
      | 4 => exGroundResolution_step1
      | 5 => exGroundResolution_step2
      | 6 => exGroundResolution_step3
      | _ => exGroundResolution_refutation := by
  have h0 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 0 = .axiom_ exGroundClause_G1 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    rfl
  have h1 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 1 = .axiom_ exGroundClause_G2 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    rfl
  have h2 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 2 = .axiom_ exGroundClause_G3 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    rfl
  have h3 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 3 = .axiom_ exGroundClause_G4 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    rfl
  have h4 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 4 = exGroundResolution_step1 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    change FOResolutionTree.resolve (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 1)
      (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 0) (.pos (exPred_P exSkolemConst_a exSkolemConst_a)) = _
    rw [h1, h0]
    rfl
  have h5 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 5 = exGroundResolution_step2 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    change FOResolutionTree.resolve (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 2)
      (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 0) (.pos (exPred_P exSkolemConst_a exSkolemConst_a)) = _
    rw [h2, h0]
    rfl
  have h6 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 6 = exGroundResolution_step3 := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    change FOResolutionTree.resolve (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 5)
      (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 3) (.pos (exPred_P exGroundTerm_fa exSkolemConst_a)) = _
    rw [h5, h3]
    rfl
  have h7 : groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 7 = exGroundResolution_refutation := by
    rw [groundGraphUnfold.eq_1 (L := exClauseFormLang) rfl exGroundGraph]
    change FOResolutionTree.resolve (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 4)
      (groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph 6) (.pos (exPred_P exSkolemConst_a exGroundTerm_fa)) = _
    rw [h4, h6]
    rfl
  rcases v with ⟨n, hn⟩
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | 7 => exact h7
  | n + 8 => omega

proof_of exGroundGraph_unfold := by
  exact exGroundGraphUnfoldAt_tree 7

open LCS.FOResolution.GroundResolution.PropositionalTranslation.Proofs

proof_of exGroundGraph_labels := by
  intro v
  rw [exGroundGraphUnfoldAt_tree]
  rcases v with ⟨n, hn⟩
  match n with
  | 0 => exact ⟨rfl, exGroundClause_G1_isGround⟩
  | 1 => exact ⟨rfl, exGroundClause_G2_isGround⟩
  | 2 => exact ⟨rfl, exGroundClause_G3_isGround⟩
  | 3 => exact ⟨rfl, exGroundClause_G4_isGround⟩
  | 4 => exact step1_label'
  | 5 => exact step2_label'
  | 6 => exact step3_label'
  | 7 => exact exGroundResolution_refutation_label_empty
  | n + 8 => omega

proof_of exGroundGraph_refutation := by
  rw [exGroundGraph_unfold]
  refine ⟨?_, ?_, exGroundResolution_refutation_label_empty⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact exGroundClause_G1_isGround
    · exact exGroundClause_G2_isGround
    · exact exGroundClause_G3_isGround
    · exact exGroundClause_G4_isGround
  · simp [exGroundResolution_refutation, exGroundResolution_step4,
      exGroundResolution_step3, exGroundResolution_step2, exGroundResolution_step1,
      FOResolutionTree.leavesFrom]

proof_of exGroundInstances_unsatisfiable := by
  intro M s
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ c ∈ [exGroundClause_G1, exGroundClause_G2,
      exGroundClause_G3, exGroundClause_G4],
      FOClause.isSatisfied (L := exClauseFormLang) rfl M s c := by
    intro c hc
    exact Classical.byContradiction (fun hn => h ⟨c, hc, hn⟩)
  have h1 := hall exGroundClause_G1 (by simp)
  have h2 := hall exGroundClause_G2 (by simp)
  have h3 := hall exGroundClause_G3 (by simp)
  have h4 := hall exGroundClause_G4 (by simp)
  simp_all [FOClause.isSatisfied, FOLiteral.isSatisfied,
    exGroundClause_G1, exGroundClause_G2, exGroundClause_G3, exGroundClause_G4]

proof_of exClauseOriginal_valid := by
  apply exClauseFormConversion_valid_iff_unsatisfiable.mpr
  have hG1 := exGroundClause_G1_image
  have hG2 := exGroundClause_G2_image
  have hG3 := exGroundClause_G3_image
  have hG4 := exGroundClause_G4_image
  have hRef := exGroundGraph_refutation
  have hUnsat := exGroundInstances_unsatisfiable
  -- REPAIR(T8-40): proof pending
  sorry

proof_of ThreeStepProcedure.eventualSuccess := by
  -- REPAIR(T8-37): proof pending
  sorry

proof_of compoundInstanceSearch_eventually_finds_valid_negation := by
  -- REPAIR(T8-90): proof pending
  sorry

proof_of equalitySearch_blocking_instance := by
  -- REPAIR(T8-90): proof pending
  sorry

proof_of sequentialEqualitySearch_may_stall := by
  -- REPAIR(T8-90): proof pending
  sorry

proof_of sequentialRun_with_correct_tester := by
  exact compoundInstanceSearch_eventually_finds_valid_negation hNoEq
    (run.withTester hNoEq tester hDomain) hUnsat

proof_of qfSearchTester_available := by
  -- REPAIR(T8-91): proof pending
  sorry

proof_of qfFiniteResolutionTester_available := by
  -- REPAIR(T8-91): proof pending
  sorry

proof_of generalFO_embedding_exists := by
  obtain ⟨c, hc⟩ := L.constSymbols_countable
  obtain ⟨f, hf⟩ := L.funSymbols_countable
  obtain ⟨p, hp⟩ := L.predSymbols_countable
  exact ⟨⟨c, f, p, hc, hf, hp⟩⟩

proof_of generalFO_decode_encode := by
  -- REPAIR(T8-92): proof pending
  sorry

proof_of generalFO_syntax_recursive := by
  -- REPAIR(T8-92): proof pending
  sorry

proof_of generalFO_negation_recursive := by
  -- REPAIR(T8-92): proof pending
  sorry

proof_of generalFO_embedding_adequate := by
  -- REPAIR(T8-92): proof pending
  sorry

proof_of church_unsatisfiability_undecidable := by
  -- REPAIR(T8-92): proof pending
  sorry

proof_of church_validity_undecidable := by
  -- REPAIR(T8-92): proof pending
  sorry

end LCS.FOResolution.GroundResolution
