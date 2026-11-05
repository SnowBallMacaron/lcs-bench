import LCS.SLD.LogicProgramming.Correctness.Correctness

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

helper /-- Lemma 9.5.3: Given a Horn set P and SLD-refutation R, the
    quantifier-free substituted set
    {theta_1(N_0), theta_1(C_1),...,theta_p(C_p)} is unsatisfiable.
    Under the indexed FOSLDDerivation API, well-formedness is
    automatic from the constructor fields. -/
-- Identity substitution is identity on formulas and clauses.
theorem substFormula_id {L : Language} (A : FormulaN L) :
    substLit.substFormula (L := L) Term.var A = A := by
-- BEGIN PROOF
  induction A with
  | predN P args =>
    simp [substLit.substFormula]; funext i
    exact termSubstAll_id_subst (args i)
  | eq_ _ t1 t2 =>
    simp [substLit.substFormula]
    exact ⟨termSubstAll_id_subst t1, termSubstAll_id_subst t2⟩
  | neg _ ih => simp [substLit.substFormula, ih]
  | conj _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | disj _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | impl _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | all _ _ ih => simp [substLit.substFormula, ih]
  | ex _ _ ih => simp [substLit.substFormula, ih]

helper theorem substLit_id {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (substLit (L := L) (hNoEq := hNoEq)) Term.var lit = lit := by
-- BEGIN PROOF
  cases lit <;> simp [substLit, atomSubst_id]

helper theorem substLits_id {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) :
    (substLits (L := L) (hNoEq := hNoEq)) Term.var C = C := by
-- BEGIN PROOF
  simp only [substLits]
  induction C with
  | nil => rfl
  | cons lit rest ih =>
    simp only [List.map_cons, substLit_id, ih]

proof_of sldRefutation_unsatisfiable := by
  -- BEGIN PROOF
    -- Proof of Lemma 9.5.3: apply the strong invariant with τ = Term.var
    -- (identity substitution). Refutation means cg = [], so the invariant's
    -- conclusion gives us M satisfying clauseToFormula A [] = FormulaN.falsum A,
    -- a contradiction in any structure with non-empty carrier.
    apply (unsat_from_pw_false (hNoEq := hNoEq))
    intro M hAllSat
    have hInv := (sldDerivation_substituted_invariant (hNoEq := hNoEq)) A D goals hGoalType M
      R Term.var
      (fun C hC s => by
        -- Since substLits Term.var C = C, hAllSat directly gives the result.
        have h := hAllSat C hC s
        rw [substLits_id]
        exact h)
    -- Refutation: cg = ∅ (Finset), so cg.toList has no elements. The
    -- disjunction over (cg.toList.map neg) is then `clauseToFormula A nil`
    -- which equals `FormulaN.falsum A`, unsatisfiable.
    have hRef' : cg = (∅ : LCS.Finset (FOAtom L hNoEq)) := hRef
    -- Show that cg.toList.map neg has no literals, so clauseToFormula
    -- evaluates to falsum at any assignment.
    have hCgToListEmpty : ∀ a, ¬ a ∈ cg.toList := by
      intro a ha
      rw [LCS.Finset.mem_toList, hRef'] at ha
      exact LCS.Finset.not_mem_empty ha
    have hMapEmpty : ∀ lit, ¬ lit ∈ cg.toList.map FOLiteralCore.neg := by
      intro lit hmem
      rw [List.mem_map] at hmem
      obtain ⟨a, ha, _⟩ := hmem
      exact hCgToListEmpty a ha
    have hFalse := hInv (fun _ => Classical.choice M.carrierNonempty)
    -- substLits τ [] = [] and any clauseToFormula over an empty list is falsum.
    -- We need to argue via `clauseToFormula_exists_of_true`: if the formula is
    -- true, some literal in the substLits Term.var (cg.toList.map neg) is true.
    -- But substLits Term.var = id (substLits_id), so literals are from
    -- cg.toList.map neg, which is empty — contradiction.
    rw [substLits_id] at hFalse
    obtain ⟨lit, hlit, _⟩ :=
      (clauseToFormula_exists_of_true (hNoEq := hNoEq)) M _ A _ hFalse
    exact hMapEmpty lit hlit


helper theorem pw_false_from_unsat {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (S : FOClause L hNoEq → Prop)
    (h : (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq)) S) :
    ∀ (M : Structure L),
      (∀ C, S C → ∀ (s : Assignment M), formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A C) s) →
      False := by
-- BEGIN PROOF
  intro M hAll
  apply h
  refine ⟨M, fun C hC => ?_⟩
  let fvs := (C.map (fun lit => formulaVarsList lit.formula)).flatten
  apply FOClause.validIn_of_universalClosure hNoEq M A C fvs
  · intro n hn
    obtain ⟨lit, hmem, hfv⟩ := hn
    exact List.mem_flatten.mpr ⟨formulaVarsList lit.formula,
      List.mem_map_of_mem hmem, formulaVarsList_cover _ n hfv⟩
  · exact universalClosure_lift hNoEq M A C fvs (hAll C hC)

helper /-- Characterization helper: every clause in `collectInputClauses d theta`
    is obtained by substituting `theta (stepIdx)` into `c.toFOClause`
    for some step clause `c ∈ D` with `c.isDefinite`. -/
theorem collectInputClauses_mem_characterization {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)} :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
      (theta : Nat → (Nat → Term L)) (C : FOClause L hNoEq),
    C ∈ substitutedClauseSet.collectInputClauses hNoEq d theta →
    ∃ (c : FOHornClause L hNoEq) (stepIdx : Nat),
      c ∈ D ∧ (c.isDefinite (hNoEq := hNoEq)) ∧ C = (substLits (hNoEq := hNoEq)) (theta stepIdx) (FOHornClause.toFOClause hNoEq c) := by
-- BEGIN PROOF
  intro cg d
  induction d with
  | init _ _ =>
    intro theta C hC
    simp [substitutedClauseSet.collectInputClauses] at hC
  | @step prevGoal prev c hClauseInD hDefClause
        Ak headA hAk hHead rho sigma hUnif hSep ih =>
    intro theta C hC
    simp only [substitutedClauseSet.collectInputClauses] at hC
    rw [List.mem_append] at hC
    rcases hC with hL | hR
    · obtain ⟨c', stepIdx', hc'D, hc'Def, hEq⟩ := ih theta C hL
      exact ⟨c', stepIdx', hc'D, hc'Def, hEq⟩
    · simp at hR
      exact ⟨c, (FOSLDDerivation.length hNoEq prev) + 1, hClauseInD, hDefClause, hR⟩

helper /-- Helper: `substitutedClauseSet.getInitGoal hNoEq R` = `getInitGoal R` (the two
    definitions of the initial goal walker agree). -/
theorem substitutedClauseSet_getInitGoal_eq {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)} (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) d = (getInitGoal (hNoEq := hNoEq)) d := by
-- BEGIN PROOF
  induction d with
  | init _ _ => rfl
  | @step _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp [substitutedClauseSet.getInitGoal, getInitGoal, ih]

proof_of sldResolution_correct := by
  -- REPAIR(T9-26): proof pending — complement the query occurrences in the same P ∧ ¬G refutation
  sorry

proof_of resultSubstitution_eq_intermediate_one := by
  -- BEGIN PROOF
    induction R with
    | init _ _ =>
      simp only [FOSLDDerivation.resultSubstitution,
        intermediateResultSubst, intermediateResultSubst.go]
    | @step prevGoal prev c hClauseInD hDefClause Ak headA hAk hHead
        rho sigma hUnif hSep ih =>
      -- Rewrite resultSubstitution using its step definition.
      show SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho) ((FOSLDDerivation.resultSubstitution hNoEq prev)) =
           (intermediateResultSubst (hNoEq := hNoEq))
             (FOSLDDerivation.step prev c hClauseInD hDefClause Ak headA hAk hHead
               rho sigma hUnif hSep) 1
      rw [ih]
      -- Consider prev.length cases.
      by_cases hlen0 : (FOSLDDerivation.length hNoEq prev) = 0
      · -- prev is init. Since length 0 ⟹ init, intermediateResultSubst prev 1 = Term.var.
        have hprevIsVar : (intermediateResultSubst (hNoEq := hNoEq)) prev 1 = Term.var := by
          -- Induction on prev.
          cases prev
          · simp only [intermediateResultSubst, intermediateResultSubst.go]
          · exfalso
            simp only [FOSLDDerivation.length] at hlen0
            omega
        rw [hprevIsVar, substCompose_id_right_subst]
        -- RHS: intermediateResultSubst (step prev c ...) 1 = SubstitutionCore.substCompose σ ρ
        -- (since stepIdx = (FOSLDDerivation.length hNoEq prev) + 1 = 1).
        simp only [intermediateResultSubst, intermediateResultSubst.go,
          FOSLDDerivation.length]
        rw [if_pos (by omega : 1 = (FOSLDDerivation.length hNoEq prev) + 1)]
        rw [substCompose_id_left_subst]
      · -- prev has length ≥ 1: recurse via go_factor_from_id.
        have hprevLen : 1 ≤ (FOSLDDerivation.length hNoEq prev) := by omega
        simp only [intermediateResultSubst, intermediateResultSubst.go,
          FOSLDDerivation.length]
        rw [if_neg (by omega : ¬ (1 = (FOSLDDerivation.length hNoEq prev) + 1))]
        rw [substCompose_id_left_subst]
        rw [go_factor_from_id hNoEq prev 1 ⟨Nat.le_refl _, hprevLen⟩
          (SubstitutionCore.substCompose sigma rho)]


proof_of substitutedClauseSet_getInitGoal_eq_top := by
  -- BEGIN PROOF
    induction R with
    | init _ _ => rfl
    | step _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih


proof_of sldAnswer_entails := by
  -- BEGIN PROOF
    intro M hProgSat s
    -- Proof of Theorem 9.5.1 (corollary): contradiction with Lem 9.5.3
    -- after assuming ¬ A[σ] at (M, s) and filling the invariant's
    -- pointwise satisfaction premise.
    apply Classical.byContradiction
    intro hNotA
    -- Shortcut for the goal-type predicate.
    have hGoalType : ∀ g ∈ [(FOHornClause.goal (L := L) (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom)],
        ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body := by
      intro g hg
      rw [List.mem_singleton] at hg
      exact ⟨LCS.Finset.singleton queryAtom, hg⟩
    -- Key identity: intermediateResultSubst hNoEq R 1 = R.resultSubstitution.
    have hSubstEq : (intermediateResultSubst (hNoEq := hNoEq)) R 1 = (R.resultSubstitution (hNoEq := hNoEq)) :=
      ((resultSubstitution_eq_intermediate_one (hNoEq := hNoEq)) R).symm
    -- getInitGoal R = FOHornClause.goal [queryAtom] (unique goal in list).
    have hInitGoalEq :
        (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) R = (FOHornClause.goal (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom) := by
      rw [substitutedClauseSet_getInitGoal_eq_top]
      have hMem := (getInitGoal_mem_goals (hNoEq := hNoEq)) P [(FOHornClause.goal (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom)] R
      exact List.mem_singleton.mp hMem
    -- Build the pointwise satisfaction: for every clause in
    -- `substitutedClauseSet R`, the clause formula evaluates to True
    -- at `(M, s)`.  The initial goal entry uses hNotA; step entries use
    -- hProgSat + substLits_preserves_validity.
    have hAllSat : ∀ C ∈ (substitutedClauseSet (hNoEq := hNoEq)) R,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) Afalsum ((substLits (hNoEq := hNoEq)) Term.var C)) s := by
      intro C hC
      rw [substLits_id]
      cases hReq : R with
      | init initGoal hInit =>
        let sigmaInit : Nat → Term L := Term.var
        rw [hReq] at hC
        simp only [substitutedClauseSet] at hC
        rw [List.mem_singleton] at hC
        subst hC
        -- refutation forces currentGoal = ∅, which for init means
        -- ofList ([queryAtom].map (FOAtomCore.subst sigmaInit)) = ∅ — impossible.
        exfalso
        rw [List.mem_singleton] at hInit
        subst hInit
        have hRef' : (LCS.Finset.ofList
            (([queryAtom] : List (FOAtom L hNoEq)).map
              (fun a => (a.subst (hNoEq := hNoEq)) sigmaInit))) =
            (∅ : LCS.Finset (FOAtom L hNoEq)) := by
          simpa only [sigmaInit, (map_atomSubst_id (hNoEq := hNoEq)), FOSLDDerivation.isRefutation, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.goal, finset_toList_singleton] using hRef
        have hMem : (queryAtom.subst (hNoEq := hNoEq)) sigmaInit ∈
            (LCS.Finset.ofList (([queryAtom] : List (FOAtom L hNoEq)).map
              (fun a => (a.subst (hNoEq := hNoEq)) sigmaInit))) := by
          rw [LCS.Finset.mem_ofList, List.mem_map]
          exact ⟨queryAtom, List.mem_singleton.mpr rfl, rfl⟩
        rw [hRef'] at hMem
        exact LCS.Finset.not_mem_empty hMem
      | @step prevGoal prev c hClauseInD hDefClause Ak headA hAk hHead rho
          sigma hUnif hSep =>
        rw [hReq] at hC
        simp only [substitutedClauseSet] at hC
        rw [List.mem_cons] at hC
        rcases hC with hInitLit | hStepLit
        · -- C is the substituted initial goal. Discharge via hNotA.
          subst hInitLit
          -- The current target uses the concrete step form; rewrite back
          -- to the abstract R via ← hReq.
          rw [← hReq]
          -- Collapse the substitution chain using hInitVar + hSubstEq + hInitGoalEq.
          -- The clause is substLits hNoEq (theta 1) (substLits initSigma initGoal.toFOClause).
          -- With hInitVar: initSigma = Term.var, the inner substLits collapses.
          -- With hSubstEq: theta 1 = R.resultSubstitution.
          -- With hInitGoalEq: initGoal = FOHornClause.goal [queryAtom].
          rw [show substLits hNoEq (intermediateResultSubst hNoEq R 1)
                (substLits hNoEq (substitutedClauseSet.getInitSigma hNoEq R)
                  ((substitutedClauseSet.getInitGoal hNoEq R).toFOClause (hNoEq := hNoEq))) =
                substLits hNoEq (R.resultSubstitution hNoEq) [FOLiteralCore.neg queryAtom]
              from by
                rw [hInitVar, substLits_id, hInitGoalEq, hSubstEq]; simp [FOHornClause.toFOClause, FOHornClause.goal, FOHornClauseCore.toFOClause]]
          -- clauseToFormula A [neg queryAtom[σ]] = FormulaN.neg (queryAtom[σ]).
          simp only [substLits, substLit, List.map_singleton, clauseToFormula,
            clauseToFormula.litToFormula, formulaEvalN]
          rw [atomSubst_toFormula_formulaSubstAll]
          exact hNotA
        · -- C is a substituted step clause. Discharge via hProgSat +
          -- substLits_preserves_validity.
          obtain ⟨c'', _stepIdx', hc''P, _hc''Def, hCeq⟩ :=
            (collectInputClauses_mem_characterization (hNoEq := hNoEq)) _ _ C hStepLit
          rw [hCeq]
          have hc''ClauseQF : (ClauseQF (hNoEq := hNoEq)) (c''.toFOClause (hNoEq := hNoEq)) := (toFOClause_QF (hNoEq := hNoEq)) c''
          exact (substLits_preserves_validity (hNoEq := hNoEq)) Afalsum M (c''.toFOClause (hNoEq := hNoEq)) _
            hc''ClauseQF (hProgSat c'' hc''P) s
    -- Apply invariant_pw with τ = Term.var to get M ⊨ clauseToFormula of the
    -- current goal at s. Under hRef, currentGoal = ∅, so the clauseToFormula
    -- is FormulaN.falsum — unsatisfiable.
    have hInv := (sldDerivation_substituted_invariant_pw (hNoEq := hNoEq)) Afalsum P
      [(FOHornClause.goal (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom)] hGoalType M R Term.var s hAllSat
    have hRef' : cg = (∅ : LCS.Finset (FOAtom L hNoEq)) := hRef
    have hCgToListEmpty : ∀ a, ¬ a ∈ cg.toList := by
      intro a ha
      rw [LCS.Finset.mem_toList, hRef'] at ha
      exact LCS.Finset.not_mem_empty ha
    have hMapEmpty : ∀ lit, ¬ lit ∈ cg.toList.map FOLiteralCore.neg := by
      intro lit hmem
      rw [List.mem_map] at hmem
      obtain ⟨a, ha, _⟩ := hmem
      exact hCgToListEmpty a ha
    rw [substLits_id] at hInv
    obtain ⟨lit, hlit, _⟩ := (clauseToFormula_exists_of_true (hNoEq := hNoEq)) M _ Afalsum _ hInv
    exact hMapEmpty lit hlit




helper /-- `substitutedClauseSet.getInitGoal` is invariant under the
    current-goal-Finset cast used to wrap `.step` outputs. -/
@[simp]
theorem substitutedClauseSet_getInitGoal_cast {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {idx1 idx2 : LCS.Finset (FOAtom L hNoEq)}
    (h : idx1 = idx2) (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals idx1) :
    (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) (h ▸ d) =
    (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) d := by
-- BEGIN PROOF
  cases h; rfl

helper /-- `getInitGoal` (the top-level variant) is invariant under the
    current-goal-Finset cast used to wrap `.step` outputs. -/
@[simp]
theorem getInitGoal_cast {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {idx1 idx2 : LCS.Finset (FOAtom L hNoEq)}
    (h : idx1 = idx2) (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals idx1) :
    (getInitGoal (hNoEq := hNoEq)) (h ▸ d) = (getInitGoal (hNoEq := hNoEq)) d := by
-- BEGIN PROOF
  cases h; rfl



proof_of sldAnswer_commonGrounding_valid := by
  -- REPAIR(T9-42): proof pending — soundness of the full positive query under one common finite grounding
  sorry

proof_of logicalComputation_iff_sldRefutation := by
  -- REPAIR(T9-47): proof pending — identify the logical computation record with its successful SLD run
  sorry

proof_of exDisplayedRefutation_answerClasses := by
  -- REPAIR(T9-55): proof pending — four distinct displayed output patterns and two traces per goal
  sorry

proof_of exAnswer_groundCoordinateCases := by
  -- REPAIR(T9-55): proof pending — validity of all three independent free-coordinate families over P
  sorry

proof_of exAnswer_diagonalCase := by
  -- REPAIR(T9-55): proof pending — common finite grounding of both shared-variable coordinates over P
  sorry

end LCS.SLD.LogicProgramming.Correctness

end
