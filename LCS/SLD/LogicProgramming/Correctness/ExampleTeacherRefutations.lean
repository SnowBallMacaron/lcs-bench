import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Queries
import LCS.SLD.LogicProgramming.Correctness.ExampleProgram
import Attach
import LCS.SLD.LogicProgramming.Correctness.ExampleTeacherRefutations.ProofsStamp

/-! # Example 9.5.4: refutations (i) and (ii)

Section 9.5.3: the two SLD-refutations starting from the goal :- teacher(X), rich(X), with their renamings, unifiers and side conditions. -/

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

-- ρ / σ pairs for refutation (i) — three steps.

/-- Example 9.5.4 (companion, refutation (i), step 1): Identity renaming
    for C_2 (fact teacher(jean), no free variables). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_rho1 : Nat → Term exCorrectnessLang := Term.var

/-- Example 9.5.4 (companion, refutation (i), step 1): MGU σ_1 sending
    X (var 0) ↦ jean, identity elsewhere. Unifies teacher(X) with
    teacher(jean). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_sigma1 : Nat → Term exCorrectnessLang
  | 0 => Term.const .jean
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (i), step 2): Renaming ρ_2
    sending C_4's variable X (var 0) to fresh var 10. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_rho2 : Nat → Term exCorrectnessLang
  | 0 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (i), step 2): MGU σ_2 sending
    the renamed var 10 ↦ jean. Unifies rich(jean) with rich(var 10). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_sigma2 : Nat → Term exCorrectnessLang
  | 10 => Term.const .jean
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (i), step 3): Renaming ρ_3
    sending C_5's variable Y (var 2) to fresh var 11. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_rho3 : Nat → Term exCorrectnessLang
  | 2 => Term.var 11
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (i), step 3): MGU σ_3 sending
    the renamed var 11 ↦ jean. Unifies rocksinger(jean) with
    rocksinger(var 11). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_i_sigma3 : Nat → Term exCorrectnessLang
  | 11 => Term.const .jean
  | n => Term.var n

-- ρ / σ pairs for refutation (ii) — three steps, mirrors (i) with susan.

/-- Example 9.5.4 (companion, refutation (ii), step 1): Identity renaming
    for C_3 (fact teacher(susan), no free variables). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_rho1 : Nat → Term exCorrectnessLang := Term.var

/-- Example 9.5.4 (companion, refutation (ii), step 1): MGU σ_1 sending
    X (var 0) ↦ susan. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_sigma1 : Nat → Term exCorrectnessLang
  | 0 => Term.const .susan
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (ii), step 2): Renaming ρ_2
    for C_4 (var 0 ↦ var 10). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_rho2 : Nat → Term exCorrectnessLang
  | 0 => Term.var 10
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (ii), step 2): MGU σ_2 sending
    the renamed var 10 ↦ susan. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_sigma2 : Nat → Term exCorrectnessLang
  | 10 => Term.const .susan
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (ii), step 3): Renaming ρ_3
    for C_5 (var 2 ↦ var 11). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_rho3 : Nat → Term exCorrectnessLang
  | 2 => Term.var 11
  | n => Term.var n

/-- Example 9.5.4 (companion, refutation (ii), step 3): MGU σ_3 sending
    the renamed var 11 ↦ susan. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_ii_sigma3 : Nat → Term exCorrectnessLang
  | 11 => Term.const .susan
  | n => Term.var n

-- -------------------------------------------------------------------
-- Per-step separating-pair (ρ-side) helpers.
-- Each is `IsSeparatingPair Term.var ρ_i prev_goal_as_FOClause
-- input_clause.toFOClause` for the concrete ρ_i and input clause of
-- the given step. These helpers factor out the Set-theoretic reasoning
-- (clauseFV enumeration, range disjointness via funext + propext) that
-- would otherwise clutter each refutation term. They are NOT tagged
-- `@[lcsmain]`. -/

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Separating-pair helper for refutation (i) step 1. Since ρ_1 is the
    identity and C_2 (fact teacher(jean)) has no free variables, all
    seven conjuncts of IsSeparatingPair reduce either to
    Term.var-triviality or vacuous enumeration over the empty FV set. -/
theorem ex954_i_hSep1 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_i_rho1
      ([mkCorrAtom .teacher (Term.var 0),
        mkCorrAtom .rich (Term.var 0)].map FOLiteralCore.neg)
      (ex954_C2.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
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
      simp only [ex954_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
      subst hMem
      obtain ⟨_, hVi⟩ := hV
      cases hVi
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₁ ⊆ FV(C₂): ρ₁ = Term.var is identity everywhere,
    -- so the implication is trivial
    intro _ _; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Separating-pair helper for refutation (i) step 2. Previous goal
    rich(jean) is ground (no free variables), so Term.var's range on
    prev is empty, giving trivial range-disjointness. ρ_2 maps C_4's
    single free variable (var 0) to the fresh var 10, so
    substIsVar / substInjectiveOnSet on clauseFV C_4 = {0} are direct. -/
theorem ex954_i_hSep2 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_i_rho2
      ([mkCorrAtom .rich (Term.const .jean)].map FOLiteralCore.neg)
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
    · rintro ⟨⟨a, hA, hvA⟩, _⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₂ ⊆ FV(C₄) = {0}: ρ₂ is identity except at 0
    intro x hx
    rcases x with _ | n
    · -- x = 0 case: need hx contradiction (0 ∈ FV(C₄))
      exfalso; apply hx
      refine ⟨FOLiteralCore.pos (mkCorrAtom .rich (Term.var 0)),
        by simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList], ?_⟩
      exact ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    · -- x = n+1 case: ρ₂ (n+1) = var (n+1) by definition
      rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Separating-pair helper for refutation (i) step 3. Previous goal
    rocksinger(jean) is ground, so Term.var's range on prev is empty,
    giving trivial range-disjointness. ρ_3 maps C_5's single FV (var 2)
    to var 11. -/
theorem ex954_i_hSep3 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_i_rho3
      ([mkCorrAtom .rocksinger (Term.const .jean)].map FOLiteralCore.neg)
      (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _
    unfold ex954_i_rho3
    split
    · exact ⟨11, rfl⟩
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
    · rintro ⟨⟨a, hA, hvA⟩, _⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₃ ⊆ FV(C₅) = {2}: ρ₃ is identity at x ≠ 2
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

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (ii) step 1. Since ρ_1 is the
    identity and C_3 (fact teacher(susan)) has no free variables, all
    seven conjuncts reduce as in `ex954_i_hSep1`. -/
theorem ex954_ii_hSep1 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_ii_rho1
      ([mkCorrAtom .teacher (Term.var 0),
        mkCorrAtom .rich (Term.var 0)].map FOLiteralCore.neg)
      (ex954_C3.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
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
      simp only [ex954_C3, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
      subst hMem
      obtain ⟨_, hVi⟩ := hV
      cases hVi
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₁ (= Term.var) ⊆ FV(C₃): trivial
    intro _ _; rfl

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (ii) step 2. Same structure
    as `ex954_i_hSep2` with susan replacing jean. -/
theorem ex954_ii_hSep2 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_ii_rho2
      ([mkCorrAtom .rich (Term.const .susan)].map FOLiteralCore.neg)
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
    · rintro ⟨⟨a, hA, hvA⟩, _⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₂ ⊆ FV(C₄) = {0}: ρ₂ is identity except at 0
    intro x hx
    rcases x with _ | n
    · exfalso; apply hx
      refine ⟨FOLiteralCore.pos (mkCorrAtom .rich (Term.var 0)),
        by simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList], ?_⟩
      exact ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    · rfl

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Separating-pair helper for refutation (ii) step 3. Same structure
    as `ex954_i_hSep3` with susan replacing jean. -/
theorem ex954_ii_hSep3 :
    (IsSeparatingPair (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq)) Term.var ex954_ii_rho3
      ([mkCorrAtom .rocksinger (Term.const .susan)].map FOLiteralCore.neg)
      (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; exact ⟨x, rfl⟩
  · intro x _
    unfold ex954_ii_rho3
    split
    · exact ⟨11, rfl⟩
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
    · rintro ⟨⟨a, hA, hvA⟩, _⟩
      obtain ⟨lit, hMem, hV⟩ := hA
      simp at hMem
      subst hMem
      simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    · intro h; exact absurd h id
  · -- support of Term.var ⊆ FV(prevGoal): trivial
    intro _ _; rfl
  · -- support of ρ₃ ⊆ FV(C₅) = {2}: ρ₃ is identity at x ≠ 2
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

-- -------------------------------------------------------------------
-- Per-step standardization-apart (hStdApart) helpers.
-- Each witnesses that FV(prevGoal.map FOLiteral.neg) ∩ FV(clause.toFOClause) = ∅
-- for the concrete prevGoal / input-clause pair of that step.
-- -------------------------------------------------------------------

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (i), init node: N_0 = `ofList (bodyAtoms · Term.var)` for
    the first goal clause (two atoms: teacher(X), rich(X)). -/
noncomputable def exRefutation_i_init :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      (LCS.Finset.ofList (exCorrectnessGoalClause1.bodyFOAtoms.map
        (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))) := by
  simpa only [map_atomSubst_id, FOHornClause.bodyFOAtoms] using
   (FOSLDDerivation.init (D := fun c => c ∈ exCorrectnessProgram) (goals := exCorrectnessGoals_i)
    exCorrectnessGoalClause1
    (by unfold exCorrectnessGoals_i; simp))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (i), step 1 (resolve teacher(X) with teacher(jean)).
    Produces a new goal `rich(jean)` (after σ₁ applies). -/
noncomputable def exRefutation_i_step1 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      ((((LCS.Finset.ofList
          (exCorrectnessGoalClause1.bodyFOAtoms.map
            (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
          (mkCorrAtom .teacher (Term.var 0))).union
        (LCS.Finset.ofList
          (ex954_C2.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho1)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma1)) :=
  FOSLDDerivation.step
    (prev := exRefutation_i_init)
    (clause := ex954_C2)
    (hClause := by change ex954_C2 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C2; simp)
    (hDef := by unfold ex954_C2 FOHornClauseCore.isDefinite; trivial)
    (Ak := mkCorrAtom .teacher (Term.var 0))
    (headA := mkCorrAtom .teacher (Term.const .jean))
    (hAk := by
      rw [LCS.Finset.mem_ofList, map_atomSubst_id]
      simp [exCorrectnessGoalClause1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton])
    (hHead := rfl)
    (rho := ex954_i_rho1)
    (sigma := ex954_i_sigma1)
    (hMGU := by
      apply isAtomMGU_toCore exCorrectnessLang_noEq
      apply corrMGU
      first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
      · rfl
      · intro n hn; simp [ex954_i_sigma1, hn]
      · rfl)
    (hSep :=
      (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
        ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
          simp only [LCS.Finset.mem_toList, LCS.Finset.mem_ofList,
            map_atomSubst_id, exCorrectnessGoalClause1,
            FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton]))
        ex954_i_hSep1)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (i), step 1's currentGoal Finset collapses to the singleton
    `{rich(jean)}`. Used to rewrite the prev Finset of step 2. -/
theorem exRefutation_i_step1_currentGoal :
    ((((LCS.Finset.ofList
        (exCorrectnessGoalClause1.bodyFOAtoms.map
          (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) Term.var))).erase
        (mkCorrAtom .teacher (Term.var 0))).union
      (LCS.Finset.ofList
        (ex954_C2.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho1)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma1)) =
    LCS.Finset.ofList [mkCorrAtom .rich (Term.const .jean)] := by
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
        simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_i_sigma1]
    · rw [LCS.Finset.mem_ofList] at himg
      simp [ex954_C2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton] at himg
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
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_i_sigma1]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (i), step 2 (resolve rich(jean) with rich(X):-rocksinger(X)). -/
noncomputable def exRefutation_i_step2 :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      ((((LCS.Finset.ofList [mkCorrAtom .rich (Term.const .jean)]).erase
          (mkCorrAtom .rich (Term.const .jean))).union
        (LCS.Finset.ofList
          (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho2)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma2)) := by
  have step2raw :=
    FOSLDDerivation.step
      (prev := exRefutation_i_step1)
      (clause := ex954_C4)
      (hClause := by change ex954_C4 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C4; simp)
      (hDef := by unfold ex954_C4 FOHornClauseCore.isDefinite; trivial)
      (Ak := mkCorrAtom .rich (Term.const .jean))
      (headA := mkCorrAtom .rich (Term.var 0))
      (hAk := by
        rw [exRefutation_i_step1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := rfl)
      (rho := ex954_i_rho2)
      (sigma := ex954_i_sigma2)
      (hMGU := by
        apply isAtomMGU_toCore exCorrectnessLang_noEq
        apply corrMGU
        first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
        · rfl
        · intro n hn; simp [ex954_i_sigma2, hn]
        · rfl)
      (hSep :=
        (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
          ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
            rw [LCS.Finset.mem_toList, exRefutation_i_step1_currentGoal,
              LCS.Finset.mem_ofList]))
          ex954_i_hSep2)

  rw [exRefutation_i_step1_currentGoal] at step2raw
  exact step2raw

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Ex 9.5.4 (i), step 2's currentGoal Finset collapses to the singleton
    `{rocksinger(jean)}`. Used to rewrite the prev Finset of step 3. -/
theorem exRefutation_i_step2_currentGoal :
    ((((LCS.Finset.ofList [mkCorrAtom .rich (Term.const .jean)]).erase
        (mkCorrAtom .rich (Term.const .jean))).union
      (LCS.Finset.ofList
        (ex954_C4.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho2)))
      ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma2)) =
    LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .jean)] := by
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
        ex954_i_rho2, ex954_i_sigma2]
  · intro h
    simp at h
    subst h
    refine ⟨mkCorrAtom .rocksinger (Term.var 10), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList]
      simp [ex954_C4, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton,
        mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_i_rho2]
    · simp [mkCorrAtom, FOAtomCore.subst, FOAtomCore.mapTerms, termSubstAll, ex954_i_sigma2]

/-- Ex 9.5.4 (i), step 3 (resolve rocksinger(jean) with rocksinger(Y)).
    Yields the empty goal. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exRefutation_i :
    (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
      (∅ : LCS.Finset (FOAtom exCorrectnessLang exCorrectnessLang_noEq)) := by
  have step3raw :
      (FOSLDDerivation (hNoEq := exCorrectnessLang_noEq)) (fun c => c ∈ exCorrectnessProgram) exCorrectnessGoals_i
        ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .jean)]).erase
            (mkCorrAtom .rocksinger (Term.const .jean))).union
          (LCS.Finset.ofList
            (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho3)))
          ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma3)) := by
    have h :=
      FOSLDDerivation.step
        (prev := exRefutation_i_step2)
        (clause := ex954_C5)
        (hClause := by change ex954_C5 ∈ exCorrectnessProgram; unfold exCorrectnessProgram ex954_C5; simp)
        (hDef := by unfold ex954_C5 FOHornClauseCore.isDefinite; trivial)
        (Ak := mkCorrAtom .rocksinger (Term.const .jean))
        (headA := mkCorrAtom .rocksinger (Term.var 2))
        (hAk := by
          rw [exRefutation_i_step2_currentGoal, LCS.Finset.mem_ofList]
          simp)
        (hHead := rfl)
        (rho := ex954_i_rho3)
        (sigma := ex954_i_sigma3)
        (hMGU := by
          apply isAtomMGU_toCore exCorrectnessLang_noEq
          apply corrMGU
          first | apply singlePairMGU | (apply pairMGU_swap; apply singlePairMGU)
          · rfl
          · intro n hn; simp [ex954_i_sigma3, hn]
          · rfl)
        (hSep :=
          (IsSeparatingPair_of_clauseFV_eq (hNoEq := exCorrectnessLang_noEq)) _ _ _ _ _
            ((clauseFV_neg_congr_of_mem_iff (hNoEq := exCorrectnessLang_noEq)) _ _ (fun a => by
              rw [LCS.Finset.mem_toList, exRefutation_i_step2_currentGoal,
                LCS.Finset.mem_ofList]))
            ex954_i_hSep3)

    rw [exRefutation_i_step2_currentGoal] at h
    exact h
  have hIdx :
      ((((LCS.Finset.ofList [mkCorrAtom .rocksinger (Term.const .jean)]).erase
          (mkCorrAtom .rocksinger (Term.const .jean))).union
        (LCS.Finset.ofList
          (ex954_C5.bodyFOAtoms.map (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_rho3)))
        ).image (fun a => (a.subst (hNoEq := exCorrectnessLang_noEq)) ex954_i_sigma3)) =
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

end LCS.SLD.LogicProgramming.Correctness
end
