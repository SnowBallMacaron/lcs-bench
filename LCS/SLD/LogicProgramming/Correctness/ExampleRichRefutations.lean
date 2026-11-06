import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Queries
import LCS.SLD.LogicProgramming.Correctness.ExampleProgram
import Attach
import LCS.SLD.LogicProgramming.Correctness.ExampleRichRefutations.ProofsStamp

/-! # Example 9.5.4: refutations (iii) and (iv)

Section 9.5.3: the two SLD-refutations starting from the goal :- rich(Z), with their renamings, unifiers and side conditions. -/

noncomputable section
attribute [local instance] Classical.propDecidable
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

-- ρ / σ pairs for refutation (iii) — two steps (goal :-rich(Z),
-- output (jackson/Z)).

/-- Example 9.5.4 (companion, refutation (iii), step 1): Renaming ρ_1
    for C_4 (var 0 ↦ var 10). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iii_rho1 : Nat → Term exCorrectnessLang
  | 0 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (iii), step 1): MGU σ_1
    identifying Z (var 1) and the renamed C_4 variable (var 10).
    Maps both to var 10. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iii_sigma1 : Nat → Term exCorrectnessLang
  | 1 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (iii), step 2): Identity
    renaming for C_1 (fact rocksinger(jackson), no free variables). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iii_rho2 : Nat → Term exCorrectnessLang := Term.var

/-- Example 9.5.4 (companion, refutation (iii), step 2): MGU σ_2
    sending var 10 ↦ jackson. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iii_sigma2 : Nat → Term exCorrectnessLang
  | 10 => Term.const .jackson
  | n => Term.var n

-- ρ / σ pairs for refutation (iv) — two steps (goal :-rich(Z),
-- indefinite output (Y_1/Y, Y_1/Z) where Y_1 = var 22).

/-- Example 9.5.4 (companion, refutation (iv), step 1): Renaming ρ_1
    for C_4 (var 0 ↦ var 10). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iv_rho1 : Nat → Term exCorrectnessLang
  | 0 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (iv), step 1): MGU σ_1
    identifying Z (var 1) and the renamed C_4 variable (var 10). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iv_sigma1 : Nat → Term exCorrectnessLang
  | 1 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (iv), step 2): Renaming ρ_2
    for C_5 (var 2 ↦ var 22 = Y_1). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iv_rho2 : Nat → Term exCorrectnessLang
  | 2 => Term.var 22
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (iv), step 2): MGU σ_2
    identifying var 10 with the renamed var 22. Maps both to var 22. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_iv_sigma2 : Nat → Term exCorrectnessLang
  | 10 => Term.var 22
  | n => Term.var n

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (iii) step 1. Previous goal
    FV = {1}; ρ_1 maps C_4's FV (={0}) to {10}; the two ranges
    {1} and {10} are disjoint. -/
theorem ex954_iii_hSep1 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_iii_rho1
      ([mkCorrAtom .rich (Term.var 1)].map FOLiteralCore.neg)
      (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _
    rcases x with _ | n
    · exact ⟨10, rfl⟩
    · exact ⟨n+1, rfl⟩
  · intro x y _ _ h; cases h; rfl
  · intro x y hx hy h
    have hx0 : x = 0 := by
      obtain ⟨lit, hMem, hV⟩ := hx
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      rcases hMem with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
    have hy0 : y = 0 := by
      obtain ⟨lit, hMem, hV⟩ := hy
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      rcases hMem with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
    rw [hx0, hy0]
  · funext n
    apply propext
    constructor
    · rintro ⟨⟨a, hA, hvA⟩, ⟨b, hBin, hvB⟩⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h1⟩ := hV; subst h1
      cases hvA
      obtain ⟨lit2, hMem2, hV2⟩ := hBin
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem2
      rcases hMem2 with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV2
        obtain ⟨_, h0⟩ := hV2; subst h0
        simp [ex954_iii_rho1] at hvB
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV2
        obtain ⟨_, h0⟩ := hV2; subst h0
        simp [ex954_iii_rho1] at hvB
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₁ ⊆ FV(C₄) = {0}: ρ₁ is identity except at 0
    intro x hx
    rcases x with _ | n
    · exfalso; apply hx
      refine ⟨FOLiteralCore.pos (mkCorrAtom .rich (Term.var 0)),
        by simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList], ?_⟩
      exact ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    · rfl

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (iii) step 2. ρ_2 is identity
    and C_1 is the ground fact rocksinger(jackson), so the argument is
    analogous to `ex954_i_hSep1`. -/
theorem ex954_iii_hSep2 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_iii_rho2
      ([mkCorrAtom .rocksinger (Term.var 10)].map FOLiteralCore.neg)
      (ex954_C1.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x y _ _ h; cases h; rfl
  · intro x y _ _ h; cases h; rfl
  · funext n
    apply propext
    constructor
    · rintro ⟨_, b, hBin, _⟩
      obtain ⟨lit, hMem, hV⟩ := hBin
      simp only [ex954_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
      subst hMem
      obtain ⟨_, hVi⟩ := hV
      cases hVi
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₂ (= Term.var) ⊆ FV(C₁): trivial
    intro _ _; rfl

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (iv) step 1. Identical in
    structure to `ex954_iii_hSep1`: previous goal FV = {1}, ρ_1 maps
    C_4's FV (={0}) to {10}, ranges disjoint. -/
theorem ex954_iv_hSep1 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_iv_rho1
      ([mkCorrAtom .rich (Term.var 1)].map FOLiteralCore.neg)
      (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _
    rcases x with _ | n
    · exact ⟨10, rfl⟩
    · exact ⟨n+1, rfl⟩
  · intro x y _ _ h; cases h; rfl
  · intro x y hx hy h
    have hx0 : x = 0 := by
      obtain ⟨lit, hMem, hV⟩ := hx
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      rcases hMem with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
    have hy0 : y = 0 := by
      obtain ⟨lit, hMem, hV⟩ := hy
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      rcases hMem with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
        obtain ⟨_, h0⟩ := hV; exact h0
    rw [hx0, hy0]
  · funext n
    apply propext
    constructor
    · rintro ⟨⟨a, hA, hvA⟩, ⟨b, hBin, hvB⟩⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h1⟩ := hV; subst h1
      cases hvA
      obtain ⟨lit2, hMem2, hV2⟩ := hBin
      simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem2
      rcases hMem2 with rfl | rfl
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV2
        obtain ⟨_, h0⟩ := hV2; subst h0
        simp [ex954_iv_rho1] at hvB
      · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV2
        obtain ⟨_, h0⟩ := hV2; subst h0
        simp [ex954_iv_rho1] at hvB
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₁ ⊆ FV(C₄) = {0}: ρ₁ is identity except at 0
    intro x hx
    rcases x with _ | n
    · exfalso; apply hx
      refine ⟨FOLiteralCore.pos (mkCorrAtom .rich (Term.var 0)),
        by simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList], ?_⟩
      exact ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    · rfl

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (iv) step 2. Previous goal
    FV = {10}; ρ_2 maps C_5's FV (={2}) to {22}; ranges {10} and {22}
    are disjoint. -/
theorem ex954_iv_hSep2 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_iv_rho2
      ([mkCorrAtom .rocksinger (Term.var 10)].map FOLiteralCore.neg)
      (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _
    unfold ex954_iv_rho2
    split
    · exact ⟨22, rfl⟩
    · exact ⟨_, rfl⟩
  · intro x y _ _ h; cases h; rfl
  · intro x y hx hy h
    have hx2 : x = 2 := by
      obtain ⟨lit, hMem, hV⟩ := hx
      simp [ex954_C5, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h0⟩ := hV; exact h0
    have hy2 : y = 2 := by
      obtain ⟨lit, hMem, hV⟩ := hy
      simp [ex954_C5, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h0⟩ := hV; exact h0
    rw [hx2, hy2]
  · funext n
    apply propext
    constructor
    · rintro ⟨⟨a, hA, hvA⟩, ⟨b, hBin, hvB⟩⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h10⟩ := hV; subst h10
      cases hvA
      obtain ⟨lit2, hMem2, hV2⟩ := hBin
      simp [ex954_C5, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem2
      subst hMem2
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV2
      obtain ⟨_, h2⟩ := hV2; subst h2
      simp [ex954_iv_rho2] at hvB
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₂ ⊆ FV(C₅) = {2}: ρ₂ is identity at x ≠ 2
    intro x hx
    match x, hx with
    | 2, hx =>
      exfalso; apply hx
      refine ⟨FOLiteralCore.pos (mkCorrAtom .rocksinger (Term.var 2)),
        by simp [ex954_C5, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList], ?_⟩
      exact ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    | 0, _ => rfl
    | 1, _ => rfl
    | n+3, _ => rfl

end LCS.SLD.LogicProgramming.Correctness
end
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

end LCS.SLD.LogicProgramming.Correctness
end
