import LCS.SLD.LogicProgramming.Queries
import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.RefutationExamples
import Attach
import LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions.ProofsStamp

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
/-- Ex 9.5.4 (ii), init node: same initial goal clause as (i). -/
noncomputable def exRefutation_ii_init :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      (LCS.Finset.ofList (exCorrectnessGoalClause1.bodyFOAtoms.map
        (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))) := by
  simpa only [map_atomSubst_id, FOHornClause.bodyFOAtoms] using
   (FOSLDDerivation.init (D := fun c => c ∈ exCorrectnessProgram) (goals := exCorrectnessGoals_i)
    exCorrectnessGoalClause1
    (by unfold exCorrectnessGoals_i; simp))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (ii), step 1 (resolve teacher(X) with teacher(susan)). -/
noncomputable def exRefutation_ii_step1 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      ((((LCS.Finset.ofList
          (exCorrectnessGoalClause1.bodyFOAtoms.map
            (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
          (mkCorrAtom .teacher (Term.var 0))).union
        (LCS.Finset.ofList
          (ex954_C3.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho1)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma1)) :=
  FOSLDDerivation.step
    (prev := exRefutation_ii_init)
    (clause := ex954_C3)
    (hClause := by change ex954_C3 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C3; simp)
    (hDef := by unfold ex954_C3 FOHornClauseCore.isDefinite; trivial)
    (Ak := mkCorrAtom .teacher (Term.var 0))
    (headA := mkCorrAtom .teacher (Term.const .susan))
    (hAk := by
      rw [LCS.Finset.mem_ofList, map_atomSubst_id]
      simp [exCorrectnessGoalClause1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton])
    (hHead := rfl)
    (rho := ex954_ii_rho1)
    (sigma := ex954_ii_sigma1)
    (hMGU := by
      apply isAtomMGU_toCore exCorrectnessLang_noEq
      apply corrMGU
      first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
      · rfl
      · intro n hn; simp [ex954_ii_sigma1, hn]
      · rfl)
    (hSep :=
      (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
        ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
          simp only [LCS.Finset.mem_toList, LCS.Finset.mem_ofList,
            map_atomSubst_id, exCorrectnessGoalClause1,
            FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton]))
        ex954_ii_hSep1)


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (ii), step 1 currentGoal collapses to `{rich(susan)}`. -/
theorem exRefutation_ii_step1_currentGoal :
    ((((LCS.Finset.ofList
        (exCorrectnessGoalClause1.bodyFOAtoms.map
          (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
        (mkCorrAtom .teacher (Term.var 0))).union
      (LCS.Finset.ofList
        (ex954_C3.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho1)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma1)) =
    LCS.Finset.ofList [mkCorrAtom .rich (Term.const .susan)] := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [LCS.Finset.mem_union] at hb
    rcases hb with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      rw [map_atomSubst_id] at hmem
      simp [exCorrectnessGoalClause1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hmem
      rcases hmem with hteacher | hrich
      · exact absurd hteacher hne
      · subst hrich
        simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_ii_sigma1]
    · rw [LCS.Finset.mem_ofList] at himg
      simp [ex954_C3, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at himg
  · intro h
    simp at h
    subst h
    refine ⟨mkCorrAtom .rich (Term.var 0), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; left
      rw [LCS.Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rw [LCS.Finset.mem_ofList, map_atomSubst_id]
        simp [exCorrectnessGoalClause1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton]
      · intro h; have hp := (FOAtomCore.predN.inj h).1; cases hp
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_ii_sigma1]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (ii), step 2 (resolve rich(susan) with rich(X):-rocksinger(X)). -/
noncomputable def exRefutation_ii_step2 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      ((((LCS.Finset.ofList [mkCorrAtom .rich (Term.const .susan)]).erase
          (mkCorrAtom .rich (Term.const .susan))).union
        (LCS.Finset.ofList
          (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho2)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma2)) := by
  have step2raw :=
    FOSLDDerivation.step
      (prev := exRefutation_ii_step1)
      (clause := ex954_C4)
      (hClause := by change ex954_C4 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C4; simp)
      (hDef := by unfold ex954_C4 FOHornClauseCore.isDefinite; trivial)
      (Ak := mkCorrAtom .rich (Term.const .susan))
      (headA := mkCorrAtom .rich (Term.var 0))
      (hAk := by
        rw [exRefutation_ii_step1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := rfl)
      (rho := ex954_ii_rho2)
      (sigma := ex954_ii_sigma2)
      (hMGU := by
        apply isAtomMGU_toCore exCorrectnessLang_noEq
        apply corrMGU
        first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
        · rfl
        · intro n hn; simp [ex954_ii_sigma2, hn]
        · rfl)
      (hSep :=
        (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
          ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
            rw [LCS.Finset.mem_toList, exRefutation_ii_step1_currentGoal,
              LCS.Finset.mem_ofList]))
          ex954_ii_hSep2)

  rw [exRefutation_ii_step1_currentGoal] at step2raw
  exact step2raw

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (ii), step 2 currentGoal collapses to `{rocksinger(susan)}`. -/
theorem exRefutation_ii_step2_currentGoal :
    ((((LCS.Finset.ofList [mkCorrAtom .rich (Term.const .susan)]).erase
        (mkCorrAtom .rich (Term.const .susan))).union
      (LCS.Finset.ofList
        (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho2)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma2)) =
    LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .susan)] := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [LCS.Finset.mem_union] at hb
    rcases hb with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨a', ha', rfl⟩ := himg
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at ha'
      subst ha'
      simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll,
        ex954_ii_rho2, ex954_ii_sigma2]
  · intro h
    simp at h
    subst h
    refine ⟨mkCorrAtom .rocksinger (Term.var 10), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList]
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton,
        mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_ii_rho2]
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_ii_sigma2]

/-- Example 9.5.4 (companion, refutation (ii)): As refutation (i)
    but using C_3 = teacher(susan) at step 1 instead of C_2. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exRefutation_ii :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
  have step3raw :
      (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
        ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .susan)]).erase
            (mkCorrAtom .rocksinger (Term.const .susan))).union
          (LCS.Finset.ofList
            (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho3)))
          ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma3)) := by
    have h :=
      FOSLDDerivation.step
        (prev := exRefutation_ii_step2)
        (clause := ex954_C5)
        (hClause := by change ex954_C5 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C5; simp)
        (hDef := by unfold ex954_C5 FOHornClauseCore.isDefinite; trivial)
        (Ak := mkCorrAtom .rocksinger (Term.const .susan))
        (headA := mkCorrAtom .rocksinger (Term.var 2))
        (hAk := by
          rw [exRefutation_ii_step2_currentGoal, LCS.Finset.mem_ofList]
          simp)
        (hHead := rfl)
        (rho := ex954_ii_rho3)
        (sigma := ex954_ii_sigma3)
        (hMGU := by
          apply isAtomMGU_toCore exCorrectnessLang_noEq
          apply corrMGU
          first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
          · rfl
          · intro n hn; simp [ex954_ii_sigma3, hn]
          · rfl)
        (hSep :=
          (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
            ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
              rw [LCS.Finset.mem_toList, exRefutation_ii_step2_currentGoal,
                LCS.Finset.mem_ofList]))
            ex954_ii_hSep3)

    rw [exRefutation_ii_step2_currentGoal] at h
    exact h
  have hIdx :
      ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .susan)]).erase
          (mkCorrAtom .rocksinger (Term.const .susan))).union
        (LCS.Finset.ofList
          (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_rho3)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_ii_sigma3)) =
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
    apply LCS.Finset.ext
    intro a
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [ex954_C5, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  rw [hIdx] at step3raw
  exact step3raw

-- -------------------------------------------------------------------
-- Refutation (iii): decomposed step-by-step (2 steps for :-rich(Z)).
-- -------------------------------------------------------------------

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iii), init node: goal clause is `[rich(var 1)]`. -/
noncomputable def exRefutation_iii_init :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      (LCS.Finset.ofList (exCorrectnessGoalClause2.bodyFOAtoms.map
        (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))) := by
  simpa only [map_atomSubst_id, FOHornClause.bodyFOAtoms] using
   (FOSLDDerivation.init (D := fun c => c ∈ exCorrectnessProgram) (goals := exCorrectnessGoals_ii)
    exCorrectnessGoalClause2
    (by unfold exCorrectnessGoals_ii; simp))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iii), step 1 (resolve rich(Z) with rich(X):-rocksinger(X)). -/
noncomputable def exRefutation_iii_step1 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      ((((LCS.Finset.ofList
          (exCorrectnessGoalClause2.bodyFOAtoms.map
            (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
          (mkCorrAtom .rich (Term.var 1))).union
        (LCS.Finset.ofList
          (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_rho1)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_sigma1)) :=
  FOSLDDerivation.step
    (prev := exRefutation_iii_init)
    (clause := ex954_C4)
    (hClause := by change ex954_C4 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C4; simp)
    (hDef := by unfold ex954_C4 FOHornClauseCore.isDefinite; trivial)
    (Ak := mkCorrAtom .rich (Term.var 1))
    (headA := mkCorrAtom .rich (Term.var 0))
    (hAk := by
      rw [LCS.Finset.mem_ofList, map_atomSubst_id]
      simp [exCorrectnessGoalClause2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton])
    (hHead := rfl)
    (rho := ex954_iii_rho1)
    (sigma := ex954_iii_sigma1)
    (hMGU := by
      apply isAtomMGU_toCore exCorrectnessLang_noEq
      apply corrMGU
      first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
      · rfl
      · intro n hn; simp [ex954_iii_sigma1, hn]
      · rfl)
    (hSep :=
      (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
        ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
          simp only [LCS.Finset.mem_toList, LCS.Finset.mem_ofList,
            map_atomSubst_id, exCorrectnessGoalClause2,
            FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton]))
        ex954_iii_hSep1)


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iii), step 1 currentGoal collapses to `{rocksinger(var 10)}`. -/
theorem exRefutation_iii_step1_currentGoal :
    ((((LCS.Finset.ofList
        (exCorrectnessGoalClause2.bodyFOAtoms.map
          (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
        (mkCorrAtom .rich (Term.var 1))).union
      (LCS.Finset.ofList
        (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_rho1)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_sigma1)) =
    LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)] := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [LCS.Finset.mem_union] at hb
    rcases hb with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      rw [map_atomSubst_id] at hmem
      simp [exCorrectnessGoalClause2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨a', ha', rfl⟩ := himg
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at ha'
      subst ha'
      simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll,
        ex954_iii_rho1, ex954_iii_sigma1]
  · intro h
    simp at h
    subst h
    refine ⟨mkCorrAtom .rocksinger (Term.var 10), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList]
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton,
        mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_iii_rho1]
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_iii_sigma1]

/-- Example 9.5.4 (companion, refutation (iii)): SLD-refutation
    starting from :-rich(Z) that resolves rich(Z) with
    C_4 = rich(X):-rocksinger(X), then rocksinger(X_1) with
    C_1 = rocksinger(jackson). The answer substitution binds Z to jackson. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exRefutation_iii :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
  have step2raw :
      (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
        ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)]).erase
            (mkCorrAtom .rocksinger (Term.var 10))).union
          (LCS.Finset.ofList
            (ex954_C1.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_rho2)))
          ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_sigma2)) := by
    have h :=
      FOSLDDerivation.step
        (prev := exRefutation_iii_step1)
        (clause := ex954_C1)
        (hClause := by change ex954_C1 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C1; simp)
        (hDef := by unfold ex954_C1 FOHornClauseCore.isDefinite; trivial)
        (Ak := mkCorrAtom .rocksinger (Term.var 10))
        (headA := mkCorrAtom .rocksinger (Term.const .jackson))
        (hAk := by
          rw [exRefutation_iii_step1_currentGoal, LCS.Finset.mem_ofList]
          simp)
        (hHead := rfl)
        (rho := ex954_iii_rho2)
        (sigma := ex954_iii_sigma2)
        (hMGU := by
          apply isAtomMGU_toCore exCorrectnessLang_noEq
          apply corrMGU
          first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
          · rfl
          · intro n hn; simp [ex954_iii_sigma2, hn]
          · rfl)
        (hSep :=
          (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
            ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
              rw [LCS.Finset.mem_toList, exRefutation_iii_step1_currentGoal,
                LCS.Finset.mem_ofList]))
            ex954_iii_hSep2)

    rw [exRefutation_iii_step1_currentGoal] at h
    exact h
  have hIdx :
      ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)]).erase
          (mkCorrAtom .rocksinger (Term.var 10))).union
        (LCS.Finset.ofList
          (ex954_C1.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_rho2)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iii_sigma2)) =
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
    apply LCS.Finset.ext
    intro a
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [ex954_C1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  rw [hIdx] at step2raw
  exact step2raw

-- -------------------------------------------------------------------
-- Refutation (iv): decomposed step-by-step (2 steps for :-rich(Z) with
-- indefinite answer Y_1/Y, Y_1/Z).
-- -------------------------------------------------------------------

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iv), init node: goal clause is `[rich(var 1)]`. -/
noncomputable def exRefutation_iv_init :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      (LCS.Finset.ofList (exCorrectnessGoalClause2.bodyFOAtoms.map
        (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))) := by
  simpa only [map_atomSubst_id, FOHornClause.bodyFOAtoms] using
   (FOSLDDerivation.init (D := fun c => c ∈ exCorrectnessProgram) (goals := exCorrectnessGoals_ii)
    exCorrectnessGoalClause2
    (by unfold exCorrectnessGoals_ii; simp))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iv), step 1 (resolve rich(Z) with rich(X):-rocksinger(X)). -/
noncomputable def exRefutation_iv_step1 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      ((((LCS.Finset.ofList
          (exCorrectnessGoalClause2.bodyFOAtoms.map
            (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
          (mkCorrAtom .rich (Term.var 1))).union
        (LCS.Finset.ofList
          (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_rho1)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_sigma1)) :=
  FOSLDDerivation.step
    (prev := exRefutation_iv_init)
    (clause := ex954_C4)
    (hClause := by change ex954_C4 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C4; simp)
    (hDef := by unfold ex954_C4 FOHornClauseCore.isDefinite; trivial)
    (Ak := mkCorrAtom .rich (Term.var 1))
    (headA := mkCorrAtom .rich (Term.var 0))
    (hAk := by
      rw [LCS.Finset.mem_ofList, map_atomSubst_id]
      simp [exCorrectnessGoalClause2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton])
    (hHead := rfl)
    (rho := ex954_iv_rho1)
    (sigma := ex954_iv_sigma1)
    (hMGU := by
      apply isAtomMGU_toCore exCorrectnessLang_noEq
      apply corrMGU
      first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
      · rfl
      · intro n hn; simp [ex954_iv_sigma1, hn]
      · rfl)
    (hSep :=
      (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
        ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
          simp only [LCS.Finset.mem_toList, LCS.Finset.mem_ofList,
            map_atomSubst_id, exCorrectnessGoalClause2,
            FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton]))
        ex954_iv_hSep1)


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (iv), step 1 currentGoal collapses to `{rocksinger(var 10)}`. -/
theorem exRefutation_iv_step1_currentGoal :
    ((((LCS.Finset.ofList
        (exCorrectnessGoalClause2.bodyFOAtoms.map
          (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
        (mkCorrAtom .rich (Term.var 1))).union
      (LCS.Finset.ofList
        (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_rho1)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_sigma1)) =
    LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)] := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [LCS.Finset.mem_union] at hb
    rcases hb with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      rw [map_atomSubst_id] at hmem
      simp [exCorrectnessGoalClause2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨a', ha', rfl⟩ := himg
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at ha'
      subst ha'
      simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll,
        ex954_iv_rho1, ex954_iv_sigma1]
  · intro h
    simp at h
    subst h
    refine ⟨mkCorrAtom .rocksinger (Term.var 10), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList]
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton,
        mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_iv_rho1]
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_iv_sigma1]

/-- Example 9.5.4 (companion, refutation (iv)): SLD-refutation starting
    from :-rich(Z) that resolves rich(Z) with C_4, then rocksinger with
    C_5 = rocksinger(Y). Yields the indefinite answer Y_1/Y, Y_1/Z. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exRefutation_iv :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
  have step2raw :
      (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_ii
        ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)]).erase
            (mkCorrAtom .rocksinger (Term.var 10))).union
          (LCS.Finset.ofList
            (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_rho2)))
          ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_sigma2)) := by
    have h :=
      FOSLDDerivation.step
        (prev := exRefutation_iv_step1)
        (clause := ex954_C5)
        (hClause := by change ex954_C5 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C5; simp)
        (hDef := by unfold ex954_C5 FOHornClauseCore.isDefinite; trivial)
        (Ak := mkCorrAtom .rocksinger (Term.var 10))
        (headA := mkCorrAtom .rocksinger (Term.var 2))
        (hAk := by
          rw [exRefutation_iv_step1_currentGoal, LCS.Finset.mem_ofList]
          simp)
        (hHead := rfl)
        (rho := ex954_iv_rho2)
        (sigma := ex954_iv_sigma2)
        (hMGU := by
          apply isAtomMGU_toCore exCorrectnessLang_noEq
          apply corrMGU
          first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
          · rfl
          · intro n hn; simp [ex954_iv_sigma2, hn]
          · rfl)
        (hSep :=
          (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
            ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
              rw [LCS.Finset.mem_toList, exRefutation_iv_step1_currentGoal,
                LCS.Finset.mem_ofList]))
            ex954_iv_hSep2)

    rw [exRefutation_iv_step1_currentGoal] at h
    exact h
  have hIdx :
      ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.var 10)]).erase
          (mkCorrAtom .rocksinger (Term.var 10))).union
        (LCS.Finset.ofList
          (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_rho2)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_iv_sigma2)) =
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
    apply LCS.Finset.ext
    intro a
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [ex954_C5, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  rw [hIdx] at step2raw
  exact step2raw

/-- Example 9.5.4 (companion): The indefinite answer substitution
    (Y_1/Y, Y_1/Z): maps both Y (var 2) and Z (var 1) to the fresh
    variable Y_1 (var 22). For all other variables, acts as identity. -/
@[blueprint "chap9__example_9_5_4"]
def exIndefiniteAnswer : Nat → Term exCorrectnessLang
  | 1 => Term.var 22   -- Z -> Y_1
  | 2 => Term.var 22   -- Y -> Y_1
  | n => Term.var n

/-- The original five-clause P of Examples 9.5.1 and 9.5.4.
    The two query clauses are added only in exCorrectnessProgram. -/
@[blueprint "chap9__example_9_5_4"]
def exOriginalProgram : Set (FOHornClause exCorrectnessLang exCorrectnessLang_noEq) :=
  fun c => c ∈ [ex954_C1, ex954_C2, ex954_C3, ex954_C4, exCorrectnessGoalClause1]

/-- Example 9.5.4: the open diagonal answer follows from the original P
    in every ordinary structure and at every assignment (SQ37, SQ40). -/
@[blueprint "chap9__example_9_5_4"]
theorem exIndefiniteAnswerValidity :
    programConsequence exOriginalProgram
      (.disj (.neg (mkCorrAtom .rocksinger (.var 22)).toFormula)
        (mkCorrAtom .rich (.var 22)).toFormula)

-- ===================================================================
-- Lemma 9.5.3 (required defs): Intermediate result substitutions
-- ===================================================================

/-- Lemma 9.5.3 (required): Computes the base result substitution
    theta_p = rho_p circ sigma_p for the final step of the
    SLD-refutation. Under Gallier's convention B (Def 8.4.1), the
    composition rho_p ∘ sigma_p applies rho first, sigma second. In
    Lean (standard-math SubstitutionCore.substCompose), that is `SubstitutionCore.substCompose sigma rho`
    (at x: evaluate rho(x) then apply sigma homomorphically on top). -/
@[blueprint "chap9__lemma_9_5_3"]
def baseResultSubst {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} → (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → (Nat → Term L)
  | _, .init _ _ => Term.var
  | _, .step _ _ _ _ _ _ _ _ rho sigma _ _ => SubstitutionCore.substCompose sigma rho

/-- Lemma 9.5.3 (required): Computes the intermediate result
    substitution theta_i for step i of the SLD-refutation.
    theta_p = rho_p circ sigma_p (base case at the last step).
    theta_i = (rho_i circ sigma_i) circ theta_{i+1} for i < p
    (recursive case). The index i counts from 1 (innermost step = 1).
    Uses an accumulator that processes steps from outside-in: at each
    step node j, thetaHere = (rho_j circ sigma_j) circ acc represents
    theta_j. Under Gallier convention B, (rho_j ∘ sigma_j) ∘ acc applied
    at x is acc(sigma_j(rho_j(x))) — order: rho_j, sigma_j, acc. In Lean
    standard-math SubstitutionCore.substCompose, that is `SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho)`. -/
@[blueprint "chap9__lemma_9_5_3"]
def intermediateResultSubst {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat) : (Nat → Term L) :=
  go d i Term.var
where
  go :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → Nat → (Nat → Term L) → (Nat → Term L)
    | _, .init _ _, _, _ => Term.var
    | _, .step prev _ _ _ _ _ _ _ rho sigma _ _, i, acc =>
      let stepIdx := (FOSLDDerivation.length hNoEq prev) + 1
      let thetaHere := SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho)
      if i = stepIdx then thetaHere
      else go prev i thetaHere

/-- Lemma 9.5.3 (required): Constructs the set
    {theta_1(N_0), theta_1(C_1), ..., theta_p(C_p)} of quantifier-free
    clauses obtained by applying intermediate result substitutions to
    the initial goal and each input clause used in the refutation.
    Returns a list of FOClauses. Each input clause C_i at step i gets
    theta_i applied; the initial goal N_0 gets theta_1. -/
@[blueprint "chap9__lemma_9_5_3"]
noncomputable def substitutedClauseSet {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → List (FOClause L hNoEq)
  | _, .init goal _ =>
    let sigmaInit : Nat → Term L := Term.var
    -- The init constructor starts at the original goal, with identity
    -- substitution; retain the clause-substitution recurrence.
    [(substLits (hNoEq := hNoEq)) sigmaInit (FOHornClause.toFOClause hNoEq goal)]
  | _, d@(.step ..) =>
    let theta := (intermediateResultSubst (hNoEq := hNoEq)) d
    -- Apply theta_1 to the initial goal's clause.
    let initGoal := getInitGoal d
    let initSigma := getInitSigma d
    let goalClause :=
      (substLits (hNoEq := hNoEq)) (theta 1) ((substLits (hNoEq := hNoEq)) initSigma (FOHornClause.toFOClause hNoEq initGoal))
    -- theta_i(C_i) for each input clause C_i at step i
    goalClause :: collectInputClauses d theta
where
  getInitGoal :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → FOHornClause L hNoEq
    | _, .init goal _ => goal
    | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => getInitGoal prev
  getInitSigma :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → (Nat → Term L)
    | _, .init _ _ => Term.var
    | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => getInitSigma prev
  collectInputClauses :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → (Nat → Nat → Term L) → List (FOClause L hNoEq)
    | _, .init _ _, _ => []
    | _, .step prev clause _ _ _ _ _ _ _ _ _ _, theta =>
      let stepIdx := (FOSLDDerivation.length hNoEq prev) + 1
      -- Recurse to collect C_1,...,C_{i-1}, then append theta_i(C_i)
      collectInputClauses prev theta ++
        [(substLits (hNoEq := hNoEq)) (theta stepIdx) (FOHornClause.toFOClause hNoEq clause)]

-- ===================================================================
-- Theorem 9.5.1 (required defs): Negative clause subsequence,
-- computed answer tuple, ground substitution for output variables
-- ===================================================================

/-- Original input occurrences in their derivation order: N₀ has index 0,
    and the input Cᵢ has its actual step index i (SQ38). -/
@[blueprint "chap9__theorem_9_5_1"]
def inputClauseOccurrences {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} → FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg →
      List (Nat × FOHornClause L hNoEq)
  | _, .init goal _ => [(0, goal)]
  | _, .step prev clause _ _ _ _ _ _ _ _ _ _ =>
      inputClauseOccurrences hNoEq prev ++ [(FOSLDDerivation.length hNoEq prev + 1, clause)]

/-- Query occurrences are selected by membership of the original clause in
    the Horn translation of ¬G, before substitution. Definite query clauses
    are included. Repetitions and actual indices are retained; the family may
    be empty. The stored clause is the negated component, so its falsity is
    the truth of the answer component. N₀ uses θ₁ (SQ25, SQ38). -/
@[blueprint "chap9__theorem_9_5_1"]
noncomputable def negativeClauseSubsequence {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg) (queryClauses : List (FOHornClause L hNoEq)) :
    List (Nat × FOClause L hNoEq) := by
  classical
  exact ((inputClauseOccurrences hNoEq d).filter fun pair => pair.2 ∈ queryClauses).map
    fun (i, c) => (i, substLits hNoEq (intermediateResultSubst hNoEq d (max 1 i))
      (c.toFOClause hNoEq))

/-- Corollary of Theorem 9.5.1 (required companion): Extracts the
    computed answer: the tuple (t_1,...,t_q) obtained by applying the
    result substitution sigma to the output variables z_1,...,z_q.
    Used by the corollary: for ground instances t_i of sigma(z_i),
    ⊨ P ⊃ B[t_1/z_1,...,t_q/z_q]. -/
@[blueprint "chap9__theorem_9_5_1"]
def computedAnswerTuple {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
    (outputVars : List Nat) :
    List (List (Term L)) :=
  let sigma := (d.resultSubstitution (hNoEq := hNoEq))
  [outputVars.map sigma]

/-- Corollary of Theorem 9.5.1 (required companion): Constructs a
    ground substitution (t_1/z_1,...,t_q/z_q) where each t_i is a
    ground instance of sigma(z_i). The corollary states that
    ⊨ P ⊃ B[t_1/z_1,...,t_q/z_q] for any such ground substitution. -/
@[blueprint "chap9__theorem_9_5_1"]
def groundSubstForOutputVars {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L)
    (outputVars : List Nat)
    (defaultConst : L.constSymbols) :
    Nat → Term L :=
  fun n =>
    if outputVars.contains n then
      groundify (sigma n) defaultConst
    else
      sigma n
where
  groundify {L : Language} : Term L → L.constSymbols → Term L
    | .var _, c => Term.const c
    | .const c, _ => Term.const c
    | .func f args, c => Term.func f (fun i => groundify (args i) c)

-- ===================================================================
-- Lemma 9.5.3: Unsatisfiability of substituted clause set
-- ===================================================================

-- Helper: the empty clause is in any set that contains it, so the set
-- is unsatisfiable by universalClosure_nil_validIn_false.


-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_preserves_validity {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (M : Structure L) (C : FOClause L hNoEq) (sigma : Nat → Term L)
    (hQF : (ClauseQF (hNoEq := hNoEq)) C)
    (h : ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A C) s) :
    ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) sigma C)) s := by
  intro s
  exact ((substLits_clauseToFormula_eval (A := A) (hNoEq := hNoEq)) M s sigma C hQF).mpr (h _)

-- Bridge: if for all M, pointwise satisfaction of all clause formulas in
-- S implies False, then S is FOClauseSet.isUnsatisfiable.
-- Uses resolvent_subtree_pw to strip universal closures to pointwise satisfaction.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem unsat_from_pw_false {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (S : FOClause L hNoEq → Prop)
    (h : ∀ (M : Structure L),
      (∀ C, S C → ∀ (s : Assignment M), formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A C) s) →
      False) :
    (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq)) S := by
-- BEGIN PROOF
  intro ⟨M, hSat⟩
  exact h M (fun C hC => (resolvent_subtree_pw (hNoEq := hNoEq)) M A C
    (fun fvs _ => FOClause.universalClosure_of_validIn hNoEq M C (hSat C hC) A fvs))

-- The clause formula of the current goal (all literals negated) is a conjunction
-- of negated body atoms. If it holds at assignment s, each body atom is false at s.
-- sld_goal_invariant (already proved) gives us: if M satisfies all clauses in
-- D ++ goals, then clauseToFormula(currentGoal.map neg) holds at all s.

-- Helper: extract the initial goal from a derivation.
-- Under the indexed API, goals is a type parameter, but the specific
-- goal clause used at init is recoverable from the init constructor.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[blueprint "chap9__theorem_9_5_1"]
def getInitGoal {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → FOHornClause L hNoEq
  | _, .init goal _ => goal
  | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => (getInitGoal (hNoEq := hNoEq)) prev

-- Helper: initial goal is in goals. Under the indexed API this is
-- automatic from the `hGoal` field carried by the .init constructor.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem getInitGoal_mem_goals {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (getInitGoal (hNoEq := hNoEq)) d ∈ goals := by
-- BEGIN PROOF
  induction d with
  | init goal hGoal => exact hGoal
  | step _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

-- Helper: collect all input clauses from the derivation (unsubstituted)


-- Helper: all collected clauses are in D. Under the indexed API this
-- is automatic from the `hClause` field carried by the .step
-- constructor.


-- Substitution composition helpers for the Lemma 9.5.3 proof
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem termSubstAll_id_subst {L : Language} (t : Term L) :
    termSubstAll t Term.var = t := by
-- BEGIN PROOF
  induction t with
  | var n => exact termSubstAll_var n Term.var
  | const c => simp [termSubstAll]
  | func f args ih => simp [termSubstAll]; funext i; exact ih i

-- retained: used by LCS.FOResolution.Unification.Part1, LCS.FOResolution.Unification.Part2, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_assoc {L : Language} (a b c : Nat → Term L) :
    SubstitutionCore.substCompose (SubstitutionCore.substCompose a b) c = SubstitutionCore.substCompose a (SubstitutionCore.substCompose b c) := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose, SubstitutionCore.termSubstAll_compose]

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_id_left_subst {L : Language} (sigma : Nat → Term L) :
    SubstitutionCore.substCompose Term.var sigma = sigma := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose]; exact termSubstAll_id_subst (sigma x)

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_id_right_subst {L : Language} (sigma : Nat → Term L) :
    SubstitutionCore.substCompose sigma Term.var = sigma := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose, termSubstAll]



-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLit_comp {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (sigma theta : Nat → Term L) :
    (substLit (hNoEq := hNoEq)) theta ((substLit (hNoEq := hNoEq)) sigma lit) =
    (substLit (hNoEq := hNoEq)) (SubstitutionCore.substCompose theta sigma) lit := by
-- BEGIN PROOF
  cases lit <;>
    simp [substLit, LCS.SLD.FirstOrder.atomSubst_comp]

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_comp {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (sigma theta : Nat → Term L) :
    (substLits (hNoEq := hNoEq)) theta ((substLits (hNoEq := hNoEq)) sigma C) =
    (substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose theta sigma) C := by
-- BEGIN PROOF
  simp only [substLits, List.map_map, Function.comp_def, substLit_comp]

-- intermediateResultSubst.go factorization (accumulator-outer form).
-- Under the convention-B composition order, the acc threads in as the
-- OUTER substitution. If we start the fold at (SubstitutionCore.substCompose outer acc)
-- rather than acc, the result factors as (SubstitutionCore.substCompose outer (go d i acc)).
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem go_factor {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat)
    (hi : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq d)) :
    ∀ (outer acc : Nat → Term L),
    intermediateResultSubst.go hNoEq d i (SubstitutionCore.substCompose outer acc) =
    SubstitutionCore.substCompose outer (intermediateResultSubst.go hNoEq d i acc) := by
-- BEGIN PROOF
  induction d with
  | init _ _ => simp [FOSLDDerivation.length] at hi; omega
  | @step prevGoal prev _ _ _ _ _ _ _ rho sigma _ _ ih =>
    simp only [FOSLDDerivation.length] at hi; intro outer acc
    simp only [intermediateResultSubst.go]
    by_cases heq : i = (FOSLDDerivation.length hNoEq prev) + 1
    · simp [heq]; rw [substCompose_assoc]
    · simp [heq]
      have hi_prev : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq prev) := by omega
      rw [substCompose_assoc outer acc (SubstitutionCore.substCompose sigma rho)]
      exact ih hi_prev outer (SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho))

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem go_factor_from_id {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat)
    (hi : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq d)) (outer : Nat → Term L) :
    intermediateResultSubst.go hNoEq d i outer =
    SubstitutionCore.substCompose outer (intermediateResultSubst.go hNoEq d i Term.var) := by
-- BEGIN PROOF
  have h := (go_factor (hNoEq := hNoEq)) d i hi outer Term.var
  rw [substCompose_id_right_subst] at h; exact h

-- If rho acts as the identity on the free variables of a term t, then
-- precomposing with rho under SubstitutionCore.substCompose does not change the result of
-- termSubstAll. Used to strip a separating renaming rho from previously-
-- established pointwise satisfaction facts about prevGoal.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem termSubstAll_rho_id_on_fv {L : Language}
    (ω rho : Nat → Term L) (t : Term L)
    (hRho : ∀ x, termFV t x → rho x = Term.var x) :
    termSubstAll t (SubstitutionCore.substCompose ω rho) = termSubstAll t ω := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp [termSubstAll, SubstitutionCore.substCompose]
    rw [hRho x rfl]; simp [termSubstAll]
  | const c => simp [termSubstAll]
  | func f args ih =>
    simp [termSubstAll]; funext i
    exact ih i (fun x hx => hRho x ⟨i, hx⟩)

-- Formula version of `termSubstAll_rho_id_on_fv`, restricted to
-- quantifier-free formulas (which is the only case used in Lemma 9.5.3).
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substFormula_rho_id_on_fv_qf {L : Language}
    (ω rho : Nat → Term L) (F : FormulaN L)
    (hQF : isQuantifierFree F)
    (hRho : ∀ x, formulaFVN F x → rho x = Term.var x) :
    substLit.substFormula (SubstitutionCore.substCompose ω rho) F =
    substLit.substFormula ω F := by
-- BEGIN PROOF
  induction F with
  | predN P args =>
    simp [substLit.substFormula]; funext i
    exact termSubstAll_rho_id_on_fv ω rho (args i)
      (fun x hx => hRho x ⟨i, hx⟩)
  | eq_ hL t1 t2 =>
    simp [substLit.substFormula]
    exact ⟨termSubstAll_rho_id_on_fv ω rho t1
            (fun x hx => hRho x (Or.inl hx)),
           termSubstAll_rho_id_on_fv ω rho t2
            (fun x hx => hRho x (Or.inr hx))⟩
  | neg A ih =>
    simp [substLit.substFormula]; exact ih hQF hRho
  | conj A B ihA ihB =>
    simp [substLit.substFormula]
    exact ⟨ihA hQF.1 (fun x hx => hRho x (Or.inl hx)),
           ihB hQF.2 (fun x hx => hRho x (Or.inr hx))⟩
  | disj A B ihA ihB =>
    simp [substLit.substFormula]
    exact ⟨ihA hQF.1 (fun x hx => hRho x (Or.inl hx)),
           ihB hQF.2 (fun x hx => hRho x (Or.inr hx))⟩
  | impl A B ihA ihB =>
    simp [substLit.substFormula]
    exact ⟨ihA hQF.1 (fun x hx => hRho x (Or.inl hx)),
           ihB hQF.2 (fun x hx => hRho x (Or.inr hx))⟩
  | all _ _ _ => exact absurd hQF id
  | ex _ _ _ => exact absurd hQF id

-- Literal version.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLit_rho_id_on_fv_qf {L : Language} (hNoEq : L.withoutEquality)
    (ω rho : Nat → Term L) (lit : FOLiteral L hNoEq)
    (hQF : isQuantifierFree lit.formula)
    (hRho : ∀ x, formulaFVN lit.formula x → rho x = Term.var x) :
    (substLit (hNoEq := hNoEq)) (SubstitutionCore.substCompose ω rho) lit = (substLit (hNoEq := hNoEq)) ω lit := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [substLit]
    congr 1
    apply FOAtomCore.toFormula_injective
    simpa only [(LCS.FOResolution.Method.atomSubst_toFormula (hNoEq := hNoEq))] using
      substFormula_rho_id_on_fv_qf ω rho B.toFormula hQF hRho
  | neg B =>
    simp only [substLit]
    congr 1
    apply FOAtomCore.toFormula_injective
    simpa only [(LCS.FOResolution.Method.atomSubst_toFormula (hNoEq := hNoEq))] using
      substFormula_rho_id_on_fv_qf ω rho B.toFormula hQF hRho

-- Clause version: if rho is identity on FV of every literal formula in C,
-- then SubstitutionCore.substCompose ω rho and ω act identically on C.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_rho_id_on_fv_qf {L : Language} (hNoEq : L.withoutEquality)
    (ω rho : Nat → Term L) (C : FOClause L hNoEq)
    (hQF : ∀ lit ∈ C, isQuantifierFree lit.formula)
    (hRho : ∀ lit ∈ C, ∀ x,
      formulaFVN lit.formula x → rho x = Term.var x) :
    (substLits (hNoEq := hNoEq)) (SubstitutionCore.substCompose ω rho) C = (substLits (hNoEq := hNoEq)) ω C := by
-- BEGIN PROOF
  simp only [substLits]
  induction C with
  | nil => rfl
  | cons lit rest ih =>
    have hQFh : isQuantifierFree lit.formula :=
      hQF lit List.mem_cons_self
    have hRhoh := hRho lit List.mem_cons_self
    have hQFt : ∀ l ∈ rest, isQuantifierFree l.formula :=
      fun l hl => hQF l (List.mem_cons_of_mem _ hl)
    have hRhot : ∀ l ∈ rest, ∀ x,
        formulaFVN l.formula x → rho x = Term.var x :=
      fun l hl => hRho l (List.mem_cons_of_mem _ hl)
    simp only [List.map_cons,
      substLit_rho_id_on_fv_qf hNoEq ω rho lit hQFh hRhoh,
      ih hQFt hRhot]

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Bridge lemma: for any term t, `termFV` (the FV(t) set of Def 5.2.4)
    and `termVars` (the Def 8.2.1 companion) agree as predicates. -/
theorem termFV_iff_termVars {L : Language} (t : Term L) :
    ∀ n, termFV t n ↔ termVars t n := by
-- BEGIN PROOF
  induction t with
  | var i =>
    intro n
    show (Set.singleton i) n ↔ n = i
    simp [Set.singleton]
  | const _ =>
    intro n
    show (∅ : Set Nat) n ↔ False
    constructor
    · intro h; exact h
    · intro h; exact False.elim h
  | func _ _ ih =>
    intro n
    show (Set.iUnion _) n ↔ _
    simp only [Set.iUnion]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨j, (ih j n).mp hj⟩
    · rintro ⟨j, hj⟩; exact ⟨j, (ih j n).mpr hj⟩

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Bridge lemma: for a QF formula, `formulaFVN` (the FV(A) set of
    §5.2.4.a) and `formulaVars` (the Def 8.2.1 companion) agree as
    predicates. QF is required because `formulaVars` is just
    all-occurring-variables and for quantifier-bearing formulas it
    disagrees with `formulaFVN` on bound variables. -/
theorem formulaFVN_iff_formulaVars_of_QF {L : Language}
    (A : FormulaN L) (hQF : isQuantifierFree A) :
    ∀ n, formulaFVN A n ↔ formulaVars A n := by
-- BEGIN PROOF
  induction A with
  | predN P args =>
    intro n
    show (Set.iUnion _) n ↔ _
    simp only [Set.iUnion, formulaVars]
    constructor
    · rintro ⟨j, ht⟩
      exact ⟨j, (termFV_iff_termVars (args j) n).mp ht⟩
    · rintro ⟨j, ht⟩
      exact ⟨j, (termFV_iff_termVars (args j) n).mpr ht⟩
  | eq_ hL t1 t2 =>
    intro n
    show (termFV t1 ∪ termFV t2) n ↔ _
    change (termFV t1 n ∨ termFV t2 n) ↔ (termVars t1 n ∨ termVars t2 n)
    constructor
    · rintro (h | h)
      · exact Or.inl ((termFV_iff_termVars t1 n).mp h)
      · exact Or.inr ((termFV_iff_termVars t2 n).mp h)
    · rintro (h | h)
      · exact Or.inl ((termFV_iff_termVars t1 n).mpr h)
      · exact Or.inr ((termFV_iff_termVars t2 n).mpr h)
  | neg A ih => intro n; exact ih hQF n
  | conj A B ihA ihB =>
    intro n
    show (formulaFVN A ∪ formulaFVN B) n ↔ _
    change (formulaFVN A n ∨ formulaFVN B n) ↔ (formulaVars A n ∨ formulaVars B n)
    constructor
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mp h)
      · exact Or.inr ((ihB hQF.2 n).mp h)
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mpr h)
      · exact Or.inr ((ihB hQF.2 n).mpr h)
  | disj A B ihA ihB =>
    intro n
    show (formulaFVN A ∪ formulaFVN B) n ↔ _
    change (formulaFVN A n ∨ formulaFVN B n) ↔ (formulaVars A n ∨ formulaVars B n)
    constructor
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mp h)
      · exact Or.inr ((ihB hQF.2 n).mp h)
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mpr h)
      · exact Or.inr ((ihB hQF.2 n).mpr h)
  | impl A B ihA ihB =>
    intro n
    show (formulaFVN A ∪ formulaFVN B) n ↔ _
    change (formulaFVN A n ∨ formulaFVN B n) ↔ (formulaVars A n ∨ formulaVars B n)
    constructor
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mp h)
      · exact Or.inr ((ihB hQF.2 n).mp h)
    · rintro (h | h)
      · exact Or.inl ((ihA hQF.1 n).mpr h)
      · exact Or.inr ((ihB hQF.2 n).mpr h)
  | all _ _ _ => exact absurd hQF id
  | ex _ _ _ => exact absurd hQF id

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Derivation lemma for the `.step` constructor: the combination of
    `hSep` (which implies support(rho) ⊆ FV(clause)) and `hStdApart`
    (which states FV(prevGoal) ∩ FV(clause) = ∅) forces rho to act as
    the identity on FV(prevGoal). This realizes the textbook's "since
    ρ is a renaming substitution, it is the identity on N_{i-1}"
    reading of Def 9.4.2's separating pair (Id, ρ). The QF hypothesis
    bridges between `formulaFVN` (§5.2.4.a) and `formulaVars` /
    `clauseFV` (Def 8.2.1 companion) used in the `hSep` / `hStdApart`
    constructor fields. Used by `sldDerivation_substituted_invariant_pw`
    to strip ρ from the induction hypothesis without requiring a
    separate standing-assumption premise. -/
theorem step_rho_id_on_prev {L : Language} (hNoEq : L.withoutEquality)
    (prevGoal : List (FOAtom L hNoEq))
    (clause : FOHornClause L hNoEq)
    (rho : Nat → Term L)
    (hSep : (IsSeparatingPair (L := L) (hNoEq := hNoEq)) Term.var rho
              (prevGoal.map FOLiteralCore.neg) (FOHornClause.toFOClause hNoEq clause))
    (hStdApart :
      ∀ x, (clauseFV (hNoEq := hNoEq)) (prevGoal.map FOLiteralCore.neg) x →
           ¬ (clauseFV (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq clause) x)
    (y : Nat) (hy : ∃ atom ∈ prevGoal, atom.vars y) :
    rho y = Term.var y := by
-- BEGIN PROOF
  obtain ⟨atom, hAtomMem, hFV⟩ := hy
  -- Build a clauseFV fact for prevGoal.map FOLiteralCore.neg.
  have hClauseFV_prev : (clauseFV (L := L) (hNoEq := hNoEq)) (prevGoal.map FOLiteralCore.neg) y := by
    exact ⟨FOLiteralCore.neg atom, List.mem_map_of_mem hAtomMem, hFV⟩
  -- By hStdApart: y ∉ FV(clause.toFOClause).
  have hNotInClause : ¬ (clauseFV (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq clause) y := hStdApart y hClauseFV_prev
  -- By hSep's support field for rho: rho y = Term.var y.
  exact hSep.2.2.2.2.2.2 y hNotInClause

-- Every structural Horn clause translates to a quantifier-free FO clause.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem toFOClause_QF {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) : (ClauseQF (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq c) := by
-- BEGIN PROOF
  intro lit _
  cases lit with
  | pos atom | neg atom =>
      simpa only [FOLiteral.formula, FOLiteralCore.formula] using (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) atom

end LCS.SLD.LogicProgramming.Correctness
end

