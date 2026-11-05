import LCS.SLD.LogicProgramming.Queries
import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.RefutationExamples
import LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
import Attach
import LCS.SLD.LogicProgramming.Correctness.Correctness.ProofsStamp

section
namespace LCS.SLD.LogicProgramming.Correctness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.LogicProgramming

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise-at-fixed-s variant of `sldStep_resolvent_validity_semantic`.
    Takes single-assignment satisfaction for both premises and returns
    single-assignment satisfaction for the conclusion. Proof mirrors the
    original with `s` moved from binder to parameter. Under the Finset-
    indexed API, `prevGoal : LCS.Finset (FOAtom L)` and the "next goal"
    is the set-theoretic splice
    `((prevGoal.erase Ak).union (ofList renamedBody)).image (subst σ)`. -/
theorem sldStep_resolvent_validity_semantic_pw {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (M : Structure L)
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (c : FOHornClause L hNoEq)
    (hClause : c ∈ D)
    (hDef : (c.isDefinite (hNoEq := hNoEq)))
    (rho sigma : Nat → Term L)
    (Ak headA : FOAtom L hNoEq)
    (hAk : Ak ∈ prevGoal)
    (hHead : (c.headFOAtom (hNoEq := hNoEq)) = some headA)
    (hUnif : (Ak.subst (hNoEq := hNoEq)) sigma = ((headA.subst (hNoEq := hNoEq)) rho).subst (hNoEq := hNoEq) sigma)
    (theta_outer : Nat → Term L)
    (s : Assignment M)
    (hSatPrevGoal : formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
          ((substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose theta_outer sigma)
            (prevGoal.toList.map FOLiteralCore.neg))) s)
    (hSatInputClause : formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
          ((substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose (SubstitutionCore.substCompose theta_outer sigma) rho)
            (FOHornClause.toFOClause hNoEq c))) s) :
    formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
        ((substLits (hNoEq := hNoEq)) theta_outer
          ((((prevGoal.erase Ak).union
              (LCS.Finset.ofList
                (c.bodyFOAtoms.map (fun a => (a.subst (hNoEq := hNoEq)) rho)))
              ).image (fun a => (a.subst (hNoEq := hNoEq)) sigma)
            ).toList.map FOLiteralCore.neg))) s := by
-- BEGIN PROOF
  have hPrevGoalQF : ∀ a ∈ prevGoal, isQuantifierFree a.toFormula :=
    (currentGoal_allQF (hNoEq := hNoEq)) D goals prev
  -- List form of previous goal via toList.
  have hPrevListQF : ∀ a ∈ prevGoal.toList,
      isQuantifierFree a.toFormula := by
    intro a ha
    rw [LCS.Finset.mem_toList] at ha
    exact hPrevGoalQF a ha
  let renamedBody := c.bodyFOAtoms.map (fun a => (a.subst (hNoEq := hNoEq)) rho)
  -- preimageFinset = (prevGoal.erase Ak).union (ofList renamedBody)
  let preimageFinset : LCS.Finset (FOAtom L hNoEq) :=
    (prevGoal.erase Ak).union (LCS.Finset.ofList renamedBody)
  have hPreimageFinsetQF : ∀ a ∈ preimageFinset,
      isQuantifierFree a.toFormula := by
    intro a _
    exact (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) a
  let s_θ : Assignment M := fun y => termEval M s (theta_outer y)
  let S' : Assignment M := fun x => termEval M s_θ (sigma x)
  let S'' : Assignment M := fun x => termEval M S' (rho x)
  have hPrevListMapQF : (ClauseQF (hNoEq := hNoEq)) (prevGoal.toList.map FOLiteralCore.neg) := by
    intro lit hmem
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    simp only [FOLiteral.formula, FOLiteralCore.formula]
    exact hPrevListQF a ha
  have hClauseToFOClauseQF : (ClauseQF (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq c) := (toFOClause_QF (hNoEq := hNoEq)) c
  have hPrevAtS' : formulaEvalN M
      ((clauseToFormula (hNoEq := hNoEq)) A (prevGoal.toList.map FOLiteralCore.neg)) S' := by
    rw [substLits_clauseToFormula_eval hNoEq M s A _ _ hPrevListMapQF] at hSatPrevGoal
    have heq : (fun x => termEval M s (SubstitutionCore.substCompose theta_outer sigma x)) = S' := by
      funext x; unfold SubstitutionCore.substCompose; rw [termSubstAll_eval]
    rw [heq] at hSatPrevGoal; exact hSatPrevGoal
  have hClauseAtS'' : formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A (FOHornClause.toFOClause hNoEq c)) S'' := by
    rw [substLits_clauseToFormula_eval hNoEq M s A _ _ hClauseToFOClauseQF] at hSatInputClause
    have heq : (fun x => termEval M s
        (SubstitutionCore.substCompose (SubstitutionCore.substCompose theta_outer sigma) rho x)) = S'' := by
      funext x; unfold SubstitutionCore.substCompose; rw [termSubstAll_eval]
      congr 1; funext y; rw [termSubstAll_eval]
    rw [heq] at hSatInputClause; exact hSatInputClause
  -- Let nextGoalFinset = preimageFinset.image (· with σ).
  -- The conclusion has substLits theta_outer applied to (nextGoalFinset.toList.map neg).
  let nextGoalFinset : LCS.Finset (FOAtom L hNoEq) :=
    preimageFinset.image (fun a => (a.subst (hNoEq := hNoEq)) sigma)
  have hNextListQF : ∀ a ∈ nextGoalFinset.toList,
      isQuantifierFree a.toFormula := by
    intro a _
    exact (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) a
  have hNextMapQF : (ClauseQF (hNoEq := hNoEq)) (nextGoalFinset.toList.map FOLiteralCore.neg) := by
    intro lit hmem
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    simp only [FOLiteral.formula, FOLiteralCore.formula]
    exact hNextListQF a ha
  rw [substLits_clauseToFormula_eval hNoEq M s A theta_outer _ hNextMapQF]
  -- Goal: prove evaluation of theta-subst'd next goal in M at s.
  -- Reduce to: find SOME member of preimageFinset that evaluates to False
  -- under S' (so its sigma-image will be False under s_θ, hence the
  -- negated-disjunction holds via one false atom).
  suffices h : ∃ a ∈ preimageFinset, ¬ formulaEvalN M a.toFormula S' by
    obtain ⟨a, hmem, hfalse⟩ := h
    -- The corresponding member of nextGoalFinset is `a.subst sigma`.
    apply (clauseToFormula_true_of_mem (hNoEq := hNoEq)) M s_θ A _
      (FOLiteralCore.neg ((a.subst (hNoEq := hNoEq)) sigma))
    · refine List.mem_map.mpr ⟨(a.subst (hNoEq := hNoEq)) sigma, ?_, rfl⟩
      rw [LCS.Finset.mem_toList, LCS.Finset.mem_image]
      exact ⟨a, hmem, rfl⟩
    · simp only [clauseToFormula.litToFormula, formulaEvalN]
      intro hc
      apply hfalse
      exact ((formulaSubstAll_eval (hNoEq := hNoEq)) M s_θ sigma a.toFormula
        (hPreimageFinsetQF a hmem)).mp
        ((atomSubst_toFormula_formulaSubstAll (hNoEq := hNoEq)) a sigma ▸ hc)
  -- Find a false atom in prevGoal.toList under S'.
  have ⟨fa, hfaMem, hfaFalse⟩ :
      ∃ a ∈ prevGoal, ¬ formulaEvalN M a.toFormula S' := by
    obtain ⟨lit, hmem, heval⟩ :=
      (clauseToFormula_exists_of_true (hNoEq := hNoEq)) M S' A _ hPrevAtS'
    rw [List.mem_map] at hmem
    obtain ⟨a, ha_mem, rfl⟩ := hmem
    rw [LCS.Finset.mem_toList] at ha_mem
    exact ⟨a, ha_mem, by
      simp [clauseToFormula.litToFormula, formulaEvalN] at heval
      exact heval⟩
  -- Case split: is fa = Ak, or fa ∈ prevGoal.erase Ak?
  by_cases hFaAk : fa = Ak
  · -- fa = Ak: use unification + clause satisfaction to find a false body atom.
    subst hFaAk
    have hFaQF : isQuantifierFree fa.toFormula :=
      (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) fa
    have hHeadQF : isQuantifierFree headA.toFormula :=
      (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) headA
    have hUnifFormula :
        formulaSubstAll fa.toFormula sigma =
          formulaSubstAll
            (formulaSubstAll headA.toFormula rho) sigma := by
      calc
        formulaSubstAll fa.toFormula sigma =
            ((fa.subst (hNoEq := hNoEq)) sigma).toFormula :=
          ((atomSubst_toFormula_formulaSubstAll (hNoEq := hNoEq)) fa sigma).symm
        _ = (((headA.subst (hNoEq := hNoEq)) rho).subst (hNoEq := hNoEq) sigma).toFormula :=
          congrArg FOAtomCore.toFormula hUnif
        _ = formulaSubstAll ((headA.subst (hNoEq := hNoEq)) rho).toFormula sigma :=
          (atomSubst_toFormula_formulaSubstAll (hNoEq := hNoEq)) ((headA.subst (hNoEq := hNoEq)) rho) sigma
        _ = formulaSubstAll
              (formulaSubstAll headA.toFormula rho) sigma := by
          rw [atomSubst_toFormula_formulaSubstAll]
    have hHeadFalse : ¬ formulaEvalN M headA.toFormula S'' := by
      intro h
      apply hfaFalse
      rw [← formulaSubstAll_eval hNoEq M s_θ sigma fa.toFormula hFaQF,
          hUnifFormula,
          formulaSubstAll_eval hNoEq M s_θ sigma
            (formulaSubstAll headA.toFormula rho)
            (isQF_formulaSubstAll headA.toFormula rho hHeadQF),
          formulaSubstAll_eval hNoEq M S' rho headA.toFormula hHeadQF]
      exact h
    have ⟨ba, hbMem, hbFalse⟩ :
        ∃ ba ∈ (c.bodyFOAtoms (hNoEq := hNoEq)), ¬ formulaEvalN M ba.toFormula S'' := by
      cases c with
      | rule head body =>
        simp [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] at hHead
        subst hHead
        simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]
        simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause] at hClauseAtS''
        obtain ⟨lit, hmem, heval⟩ :=
          (clauseToFormula_exists_of_true (hNoEq := hNoEq)) M S'' A _ hClauseAtS''
        rw [List.mem_append] at hmem
        cases hmem with
        | inl hL =>
          rw [List.mem_map] at hL
          obtain ⟨a, ha, rfl⟩ := hL
          exact ⟨a, ha, by
            simp [clauseToFormula.litToFormula, formulaEvalN] at heval
            exact heval⟩
        | inr hR =>
          simp at hR; subst hR
          exact absurd (by
            simp [clauseToFormula.litToFormula] at heval
            exact heval) hHeadFalse
      | fact head =>
        simp [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] at hHead
        subst hHead
        simp [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, clauseToFormula,
          clauseToFormula.litToFormula] at hClauseAtS''
        exact absurd hClauseAtS'' hHeadFalse
      | goal _ => exact absurd hDef id
    refine ⟨(ba.subst (hNoEq := hNoEq)) rho, ?_, ?_⟩
    · -- The rho-instance of ba lies in the renamed-body arm.
      show (ba.subst (hNoEq := hNoEq)) rho ∈ preimageFinset
      rw [LCS.Finset.mem_union]
      right
      rw [LCS.Finset.mem_ofList]
      exact List.mem_map.mpr ⟨ba, hbMem, rfl⟩
    · rw [atomSubst_toFormula_formulaSubstAll]
      exact fun h => hbFalse (((formulaSubstAll_eval (hNoEq := hNoEq)) M S' rho ba.toFormula
        ((FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) ba)).mp h)
  · -- fa ≠ Ak: fa ∈ preimageFinset via (prevGoal.erase Ak).
    refine ⟨fa, ?_, hfaFalse⟩
    show fa ∈ preimageFinset
    rw [LCS.Finset.mem_union]
    left
    rw [LCS.Finset.mem_erase]
    exact ⟨hfaMem, hFaAk⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 9.5.3 (required helper): One-step resolvent semantic propagation
    for SLD-refutation, mirroring the textbook step-case in the proof of
    Lemma 9.5.3. Given an indexed step node in FOSLDDerivation and a
    structure M that pointwise satisfies

      θ_2(σ_1(N_0))           = substLits hNoEq (SubstitutionCore.substCompose θ_outer σ) prevGoal
      θ_2((ρ_1 ∘ σ_1)(C_1))   = substLits hNoEq (SubstitutionCore.substCompose (SubstitutionCore.substCompose θ_outer σ) ρ) c

    (with θ_2 = θ_outer and the Lean SubstitutionCore.substCompose convention
    `SubstitutionCore.substCompose A B x = termSubstAll (B x) A`, so `SubstitutionCore.substCompose A B`
    applied to a term means "apply B first, then A"), M pointwise
    satisfies the substituted "next goal" under θ_outer = θ_2. The
    asymmetry — ρ applied only to C_1, not N_0 — encodes the textbook
    convention "ρ_1 is a renaming substitution, it is the identity on
    N_0" (per §9.5.3 proof, and per the separating pair (Id, ρ_1) of
    Definition 9.4.2). -/
theorem sldStep_resolvent_validity_semantic {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (M : Structure L)
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (c : FOHornClause L hNoEq)
    (hClause : c ∈ D)
    (hDef : (c.isDefinite (hNoEq := hNoEq)))
    (rho sigma : Nat → Term L)
    (Ak headA : FOAtom L hNoEq)
    (hAk : Ak ∈ prevGoal)
    (hHead : (c.headFOAtom (hNoEq := hNoEq)) = some headA)
    (hUnif : (Ak.subst (hNoEq := hNoEq)) sigma = ((headA.subst (hNoEq := hNoEq)) rho).subst (hNoEq := hNoEq) sigma)
    (theta_outer : Nat → Term L)
    (hSatPrevGoal : ∀ s, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
          ((substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose theta_outer sigma)
            (prevGoal.toList.map FOLiteralCore.neg))) s)
    (hSatInputClause : ∀ s, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
          ((substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose (SubstitutionCore.substCompose theta_outer sigma) rho)
            (FOHornClause.toFOClause hNoEq c))) s) :
    ∀ s, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
        ((substLits (hNoEq := hNoEq)) theta_outer
          ((((prevGoal.erase Ak).union
              (LCS.Finset.ofList
                (c.bodyFOAtoms.map (fun a => (a.subst (hNoEq := hNoEq)) rho)))
              ).image (fun a => (a.subst (hNoEq := hNoEq)) sigma)
            ).toList.map FOLiteralCore.neg))) s := by
-- BEGIN PROOF
  intro s
  exact (sldStep_resolvent_validity_semantic_pw (hNoEq := hNoEq)) A D goals M prev c
    hClause hDef rho sigma Ak headA hAk hHead hUnif
    theta_outer s (hSatPrevGoal s) (hSatInputClause s)







-- Helper: collectInputClauses is functorial in theta. If theta1 i = f(theta2 i)
-- for all i (where f is a substitution composition), then
-- collectInputClauses d theta1 = (collectInputClauses d theta2).map (substLits f).
-- This is actually phrased concretely: if theta1 = (fun i => SubstitutionCore.substCompose outer (theta2 i))
-- then collectInputClauses d theta1 = (collectInputClauses d theta2).map (substLits outer).
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem collectInputClauses_functorial {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    (outer : Nat → Term L) :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
      (theta : Nat → (Nat → Term L)),
    substitutedClauseSet.collectInputClauses hNoEq d
        (fun i => SubstitutionCore.substCompose outer (theta i)) =
    (substitutedClauseSet.collectInputClauses hNoEq d theta).map
        (fun C => (substLits (hNoEq := hNoEq)) outer C) := by
-- BEGIN PROOF
  intro cg d
  induction d with
  | init _ _ =>
    intro theta
    simp [substitutedClauseSet.collectInputClauses]
  | @step _ pd pcl _ _ _ _ _ _ _ _ _ _ ih =>
    intro theta
    simp only [substitutedClauseSet.collectInputClauses, List.map_append,
      List.map_cons, List.map_nil]
    congr 1
    · exact ih theta
    · simp only [substLits_comp]

-- Helper: collectInputClauses depends only on theta's values at derivation
-- indices, so two thetas that agree on those indices give the same result.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem collectInputClauses_theta_congr {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)} :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
      (theta1 theta2 : Nat → (Nat → Term L)),
    (∀ i, 1 ≤ i → i ≤ (FOSLDDerivation.length hNoEq d) → theta1 i = theta2 i) →
    substitutedClauseSet.collectInputClauses hNoEq d theta1 =
    substitutedClauseSet.collectInputClauses hNoEq d theta2 := by
-- BEGIN PROOF
  intro cg d
  induction d with
  | init _ _ =>
    intro theta1 theta2 _
    simp [substitutedClauseSet.collectInputClauses]
  | @step _ pd pcl _ _ _ _ _ _ _ _ _ _ ih =>
    intro theta1 theta2 hEq
    simp only [substitutedClauseSet.collectInputClauses]
    congr 1
    · apply ih
      intro i hi1 hi2
      exact hEq i hi1 (by simp [FOSLDDerivation.length]; omega)
    · rw [hEq ((FOSLDDerivation.length hNoEq pd) + 1) (by omega) (by simp [FOSLDDerivation.length])]

-- Decomposition of substitutedClauseSet on a step:
--   substitutedClauseSet (step prev c rho sigma ...) =
--   (substitutedClauseSet prev).map (substLits hNoEq (SubstitutionCore.substCompose sigma rho)) ++
--     [substLits hNoEq (SubstitutionCore.substCompose sigma rho) c.toFOClause].
-- Crucial for the inductive step of Lemma 9.5.3: each clause in prev's set
-- appears in R's set after composing with the new step's (sigma ∘ rho).
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem substitutedClauseSet_step_eq {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (c : FOHornClause L hNoEq) (hClauseInD : c ∈ D) (hDefClause : (c.isDefinite (hNoEq := hNoEq)))
    (rho sigma : Nat → Term L)
    (Ak headA : FOAtom L hNoEq)
    (hAk : Ak ∈ prevGoal)
    (hHead : (c.headFOAtom (hNoEq := hNoEq)) = some headA)
    (hUnif : (IsAtomMGU (hNoEq := hNoEq)) Ak ((headA.subst (hNoEq := hNoEq)) rho) sigma)
    (hSep : (IsSeparatingPair (L := L) (hNoEq := hNoEq)) Term.var rho
              (prevGoal.toList.map FOLiteralCore.neg) (FOHornClause.toFOClause hNoEq c))
    (hStdApart :
      ∀ x, (clauseFV (hNoEq := hNoEq)) (prevGoal.toList.map FOLiteralCore.neg) x →
           ¬ (clauseFV (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq c) x) :
    (substitutedClauseSet (hNoEq := hNoEq)) (FOSLDDerivation.step prev c hClauseInD hDefClause
        Ak headA hAk hHead rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) =
    ((substitutedClauseSet (hNoEq := hNoEq)) prev).map
        (fun C' => (substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose sigma rho) C') ++
      [(substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose sigma rho) (FOHornClause.toFOClause hNoEq c)] := by
-- BEGIN PROOF
  -- Relationship: theta_R i = SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho)
  -- (theta_prev i) for 1 ≤ i ≤ prev.length.
  have hRel : ∀ i, 1 ≤ i → i ≤ (FOSLDDerivation.length hNoEq prev) →
      (intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step prev c hClauseInD hDefClause
          Ak headA hAk hHead rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) i =
        SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho) ((intermediateResultSubst (hNoEq := hNoEq)) prev i) := by
    intro i hi1 hi2
    simp only [intermediateResultSubst, intermediateResultSubst.go]
    have hne : ¬ (i = (FOSLDDerivation.length hNoEq prev) + 1) := by omega
    simp [hne]; rw [substCompose_id_left_subst]
    exact (go_factor_from_id (hNoEq := hNoEq)) prev i ⟨hi1, hi2⟩ (SubstitutionCore.substCompose sigma rho)
  have hThetaR_top :
      (intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step prev c hClauseInD hDefClause
          Ak headA hAk hHead rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) ((FOSLDDerivation.length hNoEq prev) + 1) =
        SubstitutionCore.substCompose sigma rho := by
    simp only [intermediateResultSubst, intermediateResultSubst.go]
    simp; rw [substCompose_id_left_subst]
  -- Case on prev.
  cases hPrev : prev with
  | init goal hGoal =>
    let sigmaInit : Nat → Term L := Term.var
    subst hPrev
    simp only [substitutedClauseSet, substitutedClauseSet.getInitGoal,
      substitutedClauseSet.getInitSigma,
      substitutedClauseSet.collectInputClauses, FOSLDDerivation.length,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    have hTheta1 : (intermediateResultSubst (hNoEq := hNoEq))
        ((FOSLDDerivation.init goal hGoal).step c hClauseInD
          hDefClause Ak headA hAk hHead rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) 1 =
        SubstitutionCore.substCompose sigma rho := by
      simp only [intermediateResultSubst, intermediateResultSubst.go,
        FOSLDDerivation.length]; simp
      rw [substCompose_id_left_subst]
    simp [hTheta1]
  | @step pprevGoal pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2 psig2 phU2 phS2 =>
    subst hPrev
    -- Unfold both sides.
    simp only [substitutedClauseSet, substitutedClauseSet.getInitGoal,
      substitutedClauseSet.getInitSigma,
      substitutedClauseSet.collectInputClauses, FOSLDDerivation.length,
      List.map_cons, List.map_append, List.map_nil, List.cons_append,
      List.nil_append, List.append_assoc]
    -- Rewrite intermediateResultSubst hNoEq R 1 via hRel.
    have hTheta1 : (intermediateResultSubst (hNoEq := hNoEq))
        ((FOSLDDerivation.step pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2 psig2
          phU2 phS2).step c hClauseInD hDefClause Ak headA hAk hHead
          rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) 1 =
        SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho)
          ((intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step pprev pc phC phD pAk2
            phA2 phAk2 phH2 prho2 psig2 phU2 phS2) 1) := by
      apply hRel 1 (by omega)
      show 1 ≤ FOSLDDerivation.length hNoEq (FOSLDDerivation.step pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2
        psig2 phU2 phS2)
      simp [FOSLDDerivation.length]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · -- goalClause equality.
      rw [hTheta1, ← substLits_comp]
    · -- collectInputClauses equality.
      have hR_eq : (intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step
          (FOSLDDerivation.step pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2
            psig2 phU2 phS2) c hClauseInD hDefClause Ak headA hAk hHead
          rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) ((FOSLDDerivation.length hNoEq pprev) + 1) =
          SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho)
            (SubstitutionCore.substCompose psig2 prho2) := by
        have := hRel ((FOSLDDerivation.length hNoEq pprev) + 1) (by omega) (by
          simp [FOSLDDerivation.length])
        rw [this]
        simp only [intermediateResultSubst, intermediateResultSubst.go]; simp
        rw [substCompose_id_left_subst]
      -- Rewrite theta_R on pprev indices via hRel.
      have hCongr : substitutedClauseSet.collectInputClauses hNoEq pprev
          ((intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step (FOSLDDerivation.step
            pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2 psig2 phU2 phS2) c
            hClauseInD hDefClause Ak headA hAk hHead rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep)) =
          substitutedClauseSet.collectInputClauses hNoEq pprev
            (fun i => SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho)
              ((intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step pprev pc phC phD
                pAk2 phA2 phAk2 phH2 prho2 psig2 phU2 phS2) i)) := by
        apply (collectInputClauses_theta_congr (hNoEq := hNoEq))
        intro i hi1 hi2
        exact hRel i hi1 (by simp [FOSLDDerivation.length]; omega)
      rw [hCongr]
      -- Apply collectInputClauses_functorial.
      rw [collectInputClauses_functorial]
      have : (intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step
          (FOSLDDerivation.step pprev pc phC phD pAk2 phA2 phAk2 phH2 prho2
            psig2 phU2 phS2) c hClauseInD hDefClause Ak headA hAk hHead
          rho sigma (isAtomMGU_toCore hNoEq hUnif) hSep) ((FOSLDDerivation.length hNoEq pprev) + 1 + 1) =
          SubstitutionCore.substCompose sigma rho := hThetaR_top
      rw [this, hR_eq]
      have hTheta_prev_top : (intermediateResultSubst (hNoEq := hNoEq)) (FOSLDDerivation.step pprev
          pc phC phD pAk2 phA2 phAk2 phH2 prho2 psig2 phU2 phS2)
          ((FOSLDDerivation.length hNoEq pprev) + 1) = SubstitutionCore.substCompose psig2 prho2 := by
        simp only [intermediateResultSubst, intermediateResultSubst.go]; simp
        rw [substCompose_id_left_subst]
      rw [hTheta_prev_top, ← substLits_comp]


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise-at-fixed-s variant of `sldDerivation_substituted_invariant`.
    Takes a single-assignment satisfaction premise and yields a
    single-assignment satisfaction conclusion. Proof mirrors the original
    with `s` threaded as a parameter rather than universally quantified.
    The pointwise form is what Thm 9.5.1 needs: at each s, we assume
    (for contradiction) all negSubseq pairs hold at s, and derive
    false-at-s via the invariant's conclusion on the empty current goal. -/
theorem sldDerivation_substituted_invariant_pw {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (M : Structure L) :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg),
      ∀ (τ : Nat → Term L) (s : Assignment M),
      (∀ C ∈ (substitutedClauseSet (hNoEq := hNoEq)) R,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) τ C)) s) →
      formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
            ((substLits (hNoEq := hNoEq)) τ (cg.toList.map FOLiteralCore.neg))) s := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies/renamed-head steps
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 9.5.3: Given a Horn set P and SLD-refutation R, the
    quantifier-free substituted set
    {theta_1(N_0), theta_1(C_1),...,theta_p(C_p)} is unsatisfiable.
    Under the indexed FOSLDDerivation API, well-formedness is
    automatic from the constructor fields. -/
theorem sldDerivation_substituted_invariant {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (M : Structure L) :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg),
      ∀ (τ : Nat → Term L),
      (∀ C ∈ (substitutedClauseSet (hNoEq := hNoEq)) R, ∀ s,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) τ C)) s) →
      ∀ s, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
            ((substLits (hNoEq := hNoEq)) τ (cg.toList.map FOLiteralCore.neg))) s := by
-- BEGIN PROOF
  intro cg R τ hSat s
  exact (sldDerivation_substituted_invariant_pw (hNoEq := hNoEq)) A D goals hGoalType M R
    τ s (fun C hC => hSat C hC s)

/-- Lemma 9.5.3: If an SLD-refutation R exists for the clause set
    D ∪ goals, then the substituted clause set
    {θ_1(N_0), θ_1(C_1), ..., θ_p(C_p)} is unsatisfiable. This
    captures the textbook claim that the sequence of substituted
    clauses gathered along the refutation is jointly unsatisfiable
    at the identity substitution τ = Term.var. -/
@[blueprint "chap9__lemma_9_5_3" (main := true)]
theorem sldRefutation_unsatisfiable {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D : List (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (hRef : (R.isRefutation (hNoEq := hNoEq))) :
    (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq))
      (fun c => c ∈ (substitutedClauseSet (hNoEq := hNoEq)) R) 

-- ===================================================================
-- Theorem 9.5.1: Correctness of SLD-resolution
-- ===================================================================

-- Converse of unsat_from_pw_false: unsatisfiability implies pointwise
-- failure. If S is unsatisfiable, no structure can satisfy all clause
-- formulas at all assignments simultaneously.









/-- Theorem 9.5.1: every positive-length refutation from the Horn
    translation of the same P ∧ ¬G yields the disjunction of complemented
    query occurrences over the original universally satisfied P. Arbitrary
    P is represented by a set; D and goals are finite input witnesses in
    its full translation (SQ30). Empty extraction denotes false (SQ38). -/
@[attach_debt, blueprint "chap9__theorem_9_5_1" (main := true)]
theorem sldResolution_correct {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (lp : LogicProgram L hNoEq)
    (D goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg)
    (hInput : ∀ c ∈ D ++ goals, c ∈ queryHornTranslation lp)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal (hNoEq := hNoEq) body)
    (hPositive : 0 < FOSLDDerivation.length hNoEq R) (hRef : R.isRefutation hNoEq) :
    ∀ M : Structure L, hornProgramModels lp.prog M → ∀ s : Assignment M,
      ∃ pair ∈ negativeClauseSubsequence hNoEq R (lp.qry.map AntiHornClause.negatedClause),
        ¬ formulaEvalN M (clauseToFormula hNoEq Afalsum pair.2) s

-- ===================================================================
-- Theorem 9.5.1 (corollary): Single-atom query answer entailment
-- ===================================================================

/-- Theorem 9.5.1 (companion): `resultSubstitution` coincides with
    `intermediateResultSubst hNoEq R 1`. Both definitions accumulate the
    per-step MGU compositions `(ρ_i ∘ σ_i)` from innermost to outermost,
    so at index 1 (the innermost step) they produce the same substitution.
    For `init`, both are `Term.var`. -/
@[blueprint "chap9__theorem_9_5_1"]
theorem resultSubstitution_eq_intermediate_one {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (R.resultSubstitution (hNoEq := hNoEq)) = (intermediateResultSubst (hNoEq := hNoEq)) R 1 

/-- Theorem 9.5.1 (companion): both `getInitGoal` variants (top-level
    and the one inside `substitutedClauseSet`'s where-block) agree on
    every derivation. -/
@[blueprint "chap9__theorem_9_5_1"]
theorem substitutedClauseSet_getInitGoal_eq_top {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) R = (getInitGoal (hNoEq := hNoEq)) R 

/-- Theorem 9.5.1 (corollary, single-atom query case): If `R` is an
    SLD-refutation of `P ∪ {?- A}` whose `init` constructor used the
    identity substitution `sigmaInit = Term.var` (the textbook's
    convention B for single-atom queries), then for every structure
    `M` validating every clause of the program `P` pointwise, the
    query atom `A` substituted by the refutation's result substitution
    `σ = R.resultSubstitution` is satisfied at every assignment.

    This is the textbook's boxed paragraph after Thm 9.5.1 (the
    "Corollary" specialising the general subsequence form to
    single-atom queries): `⊨ P ⊃ A[σ]`. The proof is by
    contradiction using Lem 9.5.3 (`sldRefutation_unsatisfiable`)
    and the pointwise invariant (`sldDerivation_substituted_invariant_pw`):
    assuming `¬ A[σ]` at some `(M, s)`, every clause of the
    substituted clause set is satisfied at `(M, s)` — the initial
    goal entry via the contradiction hypothesis (after
    `resultSubstitution_eq_intermediate_one` + the `sigmaInit = Term.var`
    hypothesis collapse the substitution chain), step entries via
    `substLits_preserves_validity` on `P`-clauses — contradicting
    the empty-goal conclusion of the invariant. -/
@[blueprint "chap9__theorem_9_5_1" (main := true)]
theorem sldAnswer_entails {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (P : List (FOHornClause L hNoEq)) (queryAtom : FOAtom L hNoEq)
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ P) [(FOHornClause.goal (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom)] cg)
    (hRef : (R.isRefutation (hNoEq := hNoEq)))
    (hInitVar : substitutedClauseSet.getInitSigma hNoEq R = Term.var) :
    ∀ (M : Structure L),
      (∀ c ∈ P, ∀ s : Assignment M,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) Afalsum (FOHornClause.toFOClause hNoEq c)) s) →
      ∀ (s : Assignment M),
        formulaEvalN M
          (formulaSubstAll queryAtom.toFormula (R.resultSubstitution (hNoEq := hNoEq))) s 

/-- A finite nonempty family of uniform q-tuples is nonground when at
    least one coordinate in at least one tuple contains a variable (SQ45).
    Variable names are shared across the entire family; q = 0 has no such
    family. Ground DisjunctiveAnswer is a separate carrier. -/
@[blueprint "chap9__theorem_9_5_1"]
def NongroundAnswerFamily (L : Language) (q : Nat) : Type :=
  { S : LCS.Finset (Fin q → Term L) //
      (∃ t, t ∈ S) ∧ ∃ t ∈ S, ∃ i v, termFV (t i) v }

/-- Corollary of Theorem 9.5.1: every common finite-support η grounding
    all output images gives a ground answer to the entire positive query.
    The same η is applied to every coordinate, including fixed coordinates,
    so shared residual variables remain shared (SQ37, SQ39). P is arbitrary;
    D records the finite clauses used by this refutation (SQ30). -/
@[attach_debt, blueprint "chap9__theorem_9_5_1"]
theorem sldAnswer_commonGrounding_valid {L : Language} (hNoEq : L.withoutEquality)
    (P : Set (FOHornClause L hNoEq))
    (hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : AntiHornClause L hNoEq) (hPositive : G.negLiteral = none)
    (D : List (FOHornClause L hNoEq)) (hD : ∀ c ∈ D, c ∈ P)
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : FOSLDDerivation hNoEq (fun c => c ∈ D) [G.negatedClause] cg)
    (hRef : R.isRefutation hNoEq) (hSteps : 0 < FOSLDDerivation.length hNoEq R)
    (eta : Nat → Term L)
    (hFinite : ∃ support : List Nat, ∀ v, v ∉ support → eta v = .var v)
    (hGround : ∀ z ∈ G.existVars,
      Term.isClosed (termSubstAll (R.resultSubstitution hNoEq z) eta)) :
    programConsequence P (formulaSubstAll G.matrix
      (answerSubstitution G.existVars
        (fun i => termSubstAll (R.resultSubstitution hNoEq (G.existVars.get i)) eta)))

/-- Logical computation in PROLOG is a successful finite run of its main
    procedure, SLD-resolution. The derivation field checks every actual SLD
    transition and ends at the empty goal; finite input witnesses belong to
    the full Horn translation of the same program and query (SQ01, SQ30).
    This logical view supplies the refutation component of the correctness
    argument; the source's qualitative proof-effort comparison is OD-9-10. -/
@[blueprint "chap9__theorem_9_5_1"]
structure LogicalComputation {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) where
  prolog : LogicProgram.isPROLOG hNoEq lp
  inputs : List (FOHornClause L hNoEq)
  goals : List (FOHornClause L hNoEq)
  sameInput : ∀ c ∈ inputs ++ goals, c ∈ queryHornTranslation lp
  negativeGoals : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal (hNoEq := hNoEq) body
  derivation : FOSLDDerivation hNoEq (fun c => c ∈ inputs) goals ∅
  positiveSteps : 0 < FOSLDDerivation.length hNoEq derivation

/-- The same logical PROLOG computation exists exactly when its main SLD
    procedure has a positive-length refutation of P ∧ ¬G. This identifies
    successful logical computations, not termination of arbitrary searches. -/
@[attach_debt, blueprint "chap9__theorem_9_5_1"]
theorem logicalComputation_iff_sldRefutation {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) :
    Nonempty (LogicalComputation hNoEq lp) ↔
      LogicProgram.isPROLOG hNoEq lp ∧ ∃ (D goals : List (FOHornClause L hNoEq))
        (R : FOSLDDerivation hNoEq (fun c => c ∈ D) goals ∅),
        (∀ c ∈ D ++ goals, c ∈ queryHornTranslation lp) ∧
        (∀ g ∈ goals, ∃ body, g = FOHornClause.goal (hNoEq := hNoEq) body) ∧
        0 < FOSLDDerivation.length hNoEq R

/-- The four displayed completed traces, projected to original outputs
    (Y,Z). Each pair retains the initial negative clause and the answer
    pattern; auxiliary variables are observed only through those outputs. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exDisplayedAnswers :
    List (FOHornClause exCorrectnessLang exCorrectnessLang_noEq ×
      (Term exCorrectnessLang × Term exCorrectnessLang)) :=
  [(exCorrectnessGoalClause1, (exRefutation_i.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_i.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause1, (exRefutation_ii.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_ii.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause2, (exRefutation_iii.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_iii.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause2, (exRefutation_iv.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_iv.resultSubstitution exCorrectnessLang_noEq 1))]

/-- Example 9.5.4 has four distinct displayed-policy answer patterns, two
    for each negative goal. SQ40 counts these projected patterns, modulo
    fresh auxiliary renaming, rather than every raw refutation. -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exDisplayedRefutation_answerClasses :
    exDisplayedAnswers =
      [(exCorrectnessGoalClause1, (.const .jean, .var 1)),
       (exCorrectnessGoalClause1, (.const .susan, .var 1)),
       (exCorrectnessGoalClause2, (.var 2, .const .jackson)),
       (exCorrectnessGoalClause2, (.var 22, .var 22))] ∧
    (exDisplayedAnswers.map Prod.snd).Nodup ∧
    exDisplayedAnswers.length = 4 ∧
    (exDisplayedAnswers.take 2).map Prod.fst = [exCorrectnessGoalClause1, exCorrectnessGoalClause1] ∧
    (exDisplayedAnswers.drop 2).map Prod.fst = [exCorrectnessGoalClause2, exCorrectnessGoalClause2]

/-- The open answer matrix ¬rocksinger(Y) ∨ rich(Z) of Example 9.5.4. -/
@[blueprint "chap9__example_9_5_4"]
def exAnswerMatrix (y z : Term exCorrectnessLang) : FormulaN exCorrectnessLang :=
  .disj (.neg (mkCorrAtom .rocksinger y).toFormula) (mkCorrAtom .rich z).toFormula

/-- The first three displayed cases have independent free coordinates:
    (jean,t), (susan,t), and (t,jackson), for every ambient ground t. -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exAnswer_groundCoordinateCases (t : GroundTerm exCorrectnessLang) :
    programConsequence exOriginalProgram (exAnswerMatrix (.const .jean) t.val) ∧
    programConsequence exOriginalProgram (exAnswerMatrix (.const .susan) t.val) ∧
    programConsequence exOriginalProgram (exAnswerMatrix t.val (.const .jackson))

/-- The fourth displayed answer uses one common finite η on the residual
    variable Y₁, hence both output coordinates are the same ground term.
    It is valid over the original P (SQ37, SQ39, SQ40). -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exAnswer_diagonalCase (eta : Nat → Term exCorrectnessLang)
    (hFinite : ∃ support : List Nat, ∀ v, v ∉ support → eta v = .var v)
    (hGround : Term.isClosed (eta 22)) :
    programConsequence exOriginalProgram
      (exAnswerMatrix (termSubstAll (exIndefiniteAnswer 2) eta)
        (termSubstAll (exIndefiniteAnswer 1) eta)) ∧
    termSubstAll (exIndefiniteAnswer 2) eta = eta 22 ∧
    termSubstAll (exIndefiniteAnswer 1) eta = eta 22

-- ===================================================================
-- Cast-invariance simp-lemmas
--
-- `FOSLDDerivation` carries its current-goal Finset as a *type index*,
-- so users frequently wrap their constructed refutations in
-- `h ▸ d`-style transports to bridge between the raw `.step` output
-- index and a cleaner `Finset.ofList […]` form.  These transports are
-- opaque to `rfl`/`simp`, so every recursor on a derivation stalls at
-- them.  The three `@[simp]` lemmas below declare that
-- `getInitSigma`, `getInitGoal`, and `resultSubstitution` are
-- invariant under such casts — destructuring the equality collapses
-- the transport to its underlying constructor.
-- ===================================================================

-- retained: used by LCS.Examples.PrologAppend, LCS.Examples.PrologArithmetic, LCS.Examples.PrologMember, LCS.Examples.PrologPath, LCS.Examples.PrologReverse.Refutation
/-- `substitutedClauseSet.getInitSigma` is invariant under the
    current-goal-Finset cast used to wrap `.step` outputs. -/
@[simp]
theorem getInitSigma_cast {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {idx1 idx2 : LCS.Finset (FOAtom L hNoEq)}
    (h : idx1 = idx2) (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals idx1) :
    substitutedClauseSet.getInitSigma hNoEq (h ▸ d) =
    substitutedClauseSet.getInitSigma hNoEq d := by
-- BEGIN PROOF
  cases h; rfl





-- retained: used by LCS.Examples.PrologArithmetic
/-- `FOSLDDerivation.resultSubstitution` is invariant under the
    current-goal-Finset cast used to wrap `.step` outputs. -/
@[simp]
theorem resultSubstitution_cast {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {idx1 idx2 : LCS.Finset (FOAtom L hNoEq)}
    (h : idx1 = idx2) (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals idx1) :
    (FOSLDDerivation.resultSubstitution (hNoEq := hNoEq)) (h ▸ d) =
    (FOSLDDerivation.resultSubstitution (hNoEq := hNoEq)) d := by
-- BEGIN PROOF
  cases h; rfl

/-- Every initial node carries the identity substitution; following any
    finite chain of steps back to that node preserves it. -/
theorem getInitSigma_eq_id {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg) :
    substitutedClauseSet.getInitSigma hNoEq d = Term.var := by
  induction d with
  | init _ _ => rfl
  | step _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

end LCS.SLD.LogicProgramming.Correctness
end
