import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import Attach
import LCS.SLD.LogicProgramming.Correctness.RefutationExamples.ProofsStamp

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- `clauseFV` is invariant under list membership equivalence (specifically
    permutation): if two lists have the same elements, their literal-
    negation clauseFV sets coincide. -/
theorem clauseFV_neg_congr_of_mem_iff {L : Language} (hNoEq : L.withoutEquality)
    (l1 l2 : List (FOAtom L hNoEq))
    (hMem : ∀ a, a ∈ l1 ↔ a ∈ l2) :
    (clauseFV (hNoEq := hNoEq)) (l1.map FOLiteralCore.neg) = (clauseFV (hNoEq := hNoEq)) (l2.map FOLiteralCore.neg) := by
-- BEGIN PROOF
  funext n
  apply propext
  constructor
  · rintro ⟨lit, hLit, hV⟩
    rw [List.mem_map] at hLit
    obtain ⟨F, hF, rfl⟩ := hLit
    exact ⟨FOLiteralCore.neg F, List.mem_map.mpr ⟨F, (hMem F).mp hF, rfl⟩, hV⟩
  · rintro ⟨lit, hLit, hV⟩
    rw [List.mem_map] at hLit
    obtain ⟨F, hF, rfl⟩ := hLit
    exact ⟨FOLiteralCore.neg F, List.mem_map.mpr ⟨F, (hMem F).mpr hF, rfl⟩, hV⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Congruence of `IsSeparatingPair` in its first argument under
    clauseFV-equality. Every field of `IsSeparatingPair` uses the first
    clause only through `clauseFV`, so if two clauses have the same
    clauseFV, `IsSeparatingPair` agrees. -/
theorem IsSeparatingPair_of_clauseFV_eq {L : Language} (hNoEq : L.withoutEquality)
    (rho rho' : Nat → Term L) (A1 A2 : FOClause L hNoEq) (C' : FOClause L hNoEq)
    (hEq : (clauseFV (hNoEq := hNoEq)) A1 = (clauseFV (hNoEq := hNoEq)) A2)
    (h : (IsSeparatingPair (hNoEq := hNoEq)) rho rho' A1 C') :
    (IsSeparatingPair (hNoEq := hNoEq)) rho rho' A2 C' := by
-- BEGIN PROOF
  have := hEq.symm
  rw [IsSeparatingPair] at h ⊢
  rw [← hEq]; exact h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- `hStdApart` is stated in terms of `clauseFV`, so congruence holds
    under clauseFV-equality. -/
theorem hStdApart_of_clauseFV_eq {L : Language} (hNoEq : L.withoutEquality)
    (A1 A2 : List (FOLiteral L hNoEq)) (C' : FOClause L hNoEq)
    (hEq : (clauseFV (hNoEq := hNoEq)) A1 = (clauseFV (hNoEq := hNoEq)) A2)
    (h : ∀ x, (clauseFV (hNoEq := hNoEq)) A1 x → ¬ (clauseFV (hNoEq := hNoEq)) C' x)
    (x : Nat) : (clauseFV (hNoEq := hNoEq)) A2 x → ¬ (clauseFV (hNoEq := hNoEq)) C' x := by
-- BEGIN PROOF
  rw [← hEq]; exact h x

-- ===================================================================
-- Example 9.5.4 (companion types): Language for the correctness example
-- ===================================================================
/-- Example 9.5.4 (companion type): Predicate symbols for the
    correctness example: unary predicates rocksinger, teacher, rich. -/
@[blueprint "chap9__example_9_5_4"]
inductive ExCorrectnessPred : Type where
  | rocksinger : ExCorrectnessPred
  | teacher : ExCorrectnessPred
  | rich : ExCorrectnessPred

/-- Example 9.5.4 (companion type): Constant symbols for the
    correctness example: jackson, jean, susan. -/
@[blueprint "chap9__example_9_5_4"]
inductive ExCorrectnessConst : Type where
  | jackson : ExCorrectnessConst
  | jean : ExCorrectnessConst
  | susan : ExCorrectnessConst

-- ===================================================================
-- Example 9.5.4 (companion): Language definition
-- ===================================================================
/-- Example 9.5.4 (companion): The first-order language for the
    correctness example with predicates rocksinger, teacher, rich
    (each unary) and constants jackson, jean, susan. -/
@[blueprint "chap9__example_9_5_4"]
def exCorrectnessLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := ExCorrectnessConst
  predSymbols := ExCorrectnessPred
  predArity := fun
    | .rocksinger => 1
    | .teacher => 1
    | .rich => 1
  hasEquality := false

/-- Example 9.5.4 uses only predicate atoms. -/
@[blueprint "chap9__example_9_5_4"]
theorem exCorrectnessLang_noEq : exCorrectnessLang.withoutEquality 

/-- Example 9.5.4 (companion): Helper to build an atomic formula P(t)
    in exCorrectnessLang. -/
@[blueprint "chap9__example_9_5_4"]
def mkCorrAtom (p : ExCorrectnessPred)
    (t : Term exCorrectnessLang) : FOAtom exCorrectnessLang exCorrectnessLang_noEq :=
  FOAtomCore.predN p (fun _ => t)

-- ===================================================================
-- Example 9.5.4: The clause set for P wedge neg G
-- ===================================================================
/-- Example 9.5.4 (companion): The first negative clause from neg G:
    :-teacher(X),rich(X), encoded as a goal clause with body atoms
    [teacher(var 0), rich(var 0)]. -/
@[blueprint "chap9__example_9_5_4"]
def exCorrectnessGoalClause1 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.goal (hNoEq := exCorrectnessLang_noEq))
    (LCS.Finset.ofList [ mkCorrAtom .teacher (Term.var 0),
      mkCorrAtom .rich (Term.var 0) ])

/-- Example 9.5.4 (companion): The second negative clause from neg G:
    :-rich(Z), encoded as a goal clause with body atom [rich(var 1)].
    Variable Z = var 1. -/
@[blueprint "chap9__example_9_5_4"]
def exCorrectnessGoalClause2 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.goal (hNoEq := exCorrectnessLang_noEq))
    (LCS.Finset.singleton (mkCorrAtom .rich (Term.var 1)))

/-- Example 9.5.4: The full clause set for P wedge neg G with five definite/fact clauses
    (rocksinger, teacher, rich(X):-rocksinger(X)) and two negative clauses (:-teacher,rich; :-rich). -/
@[blueprint "chap9__example_9_5_4" (main := true)]
def exCorrectnessProgram : List (FOHornClause exCorrectnessLang exCorrectnessLang_noEq) :=
  [ -- rocksinger(jackson).
    (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .rocksinger (Term.const .jackson)),
    -- teacher(jean).
    (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .teacher (Term.const .jean)),
    -- teacher(susan).
    (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .teacher (Term.const .susan)),
    -- rich(X) :- rocksinger(X).
    (FOHornClause.rule (hNoEq := exCorrectnessLang_noEq))
      (mkCorrAtom .rich (Term.var 0))
      (LCS.Finset.singleton (mkCorrAtom .rocksinger (Term.var 0))),
    -- :-teacher(X),rich(X).
    exCorrectnessGoalClause1,
    -- rocksinger(Y).
    (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .rocksinger (Term.var 2)),
    -- :-rich(Z).
    exCorrectnessGoalClause2 ]

-- ===================================================================
-- Example 9.5.4 (companion): Four SLD-refutations
-- ===================================================================

/-- Example 9.5.4 (companion): The list of goal clauses for
    refutations (i) and (ii), each starting from :-teacher(X),rich(X). -/
@[blueprint "chap9__example_9_5_4"]
def exCorrectnessGoals_i : List (FOHornClause exCorrectnessLang exCorrectnessLang_noEq) :=
  [exCorrectnessGoalClause1]

/-- Example 9.5.4 (companion): The list of goal clauses for refutations
    (iii) and (iv), each starting from :-rich(Z). -/
@[blueprint "chap9__example_9_5_4"]
def exCorrectnessGoals_ii : List (FOHornClause exCorrectnessLang exCorrectnessLang_noEq) :=
  [exCorrectnessGoalClause2]

-- -------------------------------------------------------------------
-- Per-step rho / sigma substitutions and concrete input clauses
-- for the four textbook SLD-refutations of Example 9.5.4.
-- -------------------------------------------------------------------

/-- Example 9.5.4 (companion): The definite clause C_2 = teacher(jean),
    used in refutation (i) at step 1. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_C2 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .teacher (Term.const .jean))

/-- Example 9.5.4 (companion): The definite clause C_3 = teacher(susan),
    used in refutation (ii) at step 1. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_C3 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .teacher (Term.const .susan))

/-- Example 9.5.4 (companion): The definite clause
    C_4 = rich(X) :- rocksinger(X), used in refutations (i)/(ii)/(iii)/(iv). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_C4 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.rule (hNoEq := exCorrectnessLang_noEq))
    (mkCorrAtom .rich (Term.var 0))
    (LCS.Finset.singleton (mkCorrAtom .rocksinger (Term.var 0)))

/-- Example 9.5.4 (companion): The definite clause C_1 = rocksinger(jackson),
    used in refutation (iii). -/
@[blueprint "chap9__example_9_5_4"]
def ex954_C1 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .rocksinger (Term.const .jackson))

/-- Example 9.5.4 (companion): The definite clause C_5 = rocksinger(Y)
    (with Y = var 2), used in refutations (i)/(ii)/(iv) for the
    final rocksinger resolution step. -/
@[blueprint "chap9__example_9_5_4"]
def ex954_C5 : FOHornClause exCorrectnessLang exCorrectnessLang_noEq :=
  (FOHornClause.fact (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom .rocksinger (Term.var 2))

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

-- -------------------------------------------------------------------
-- Per-step standardization-apart (hStdApart) helpers.
-- Each witnesses that FV(prevGoal.map FOLiteral.neg) ∩ FV(clause.toFOClause) = ∅
-- for the concrete prevGoal / input-clause pair of that step.
-- -------------------------------------------------------------------

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Std-apart helper for refutation (i) step 1: clause C_2 is the
    ground fact teacher(jean), so FV(C_2.toFOClause) = ∅ and the
    implication is trivial. -/
theorem ex954_i_hStdApart1 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .teacher (Term.var 0),
             mkCorrAtom .rich (Term.var 0)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C2.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x _ hIn
  obtain ⟨lit, hMem, hV⟩ := hIn
  simp only [ex954_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Std-apart helper for refutation (i) step 2: prev goal
    rich(jean) is ground (FV = ∅), so the hypothesis is vacuous. -/
theorem ex954_i_hStdApart2 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rich (Term.const .jean)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev
  obtain ⟨lit, hMem, hV⟩ := hPrev
  simp at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Std-apart helper for refutation (i) step 3: prev goal
    rocksinger(jean) is ground (FV = ∅), so the hypothesis is vacuous. -/
theorem ex954_i_hStdApart3 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rocksinger (Term.const .jean)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev
  obtain ⟨lit, hMem, hV⟩ := hPrev
  simp at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (ii) step 1: clause C_3 is the
    ground fact teacher(susan), so the implication is trivial. -/
theorem ex954_ii_hStdApart1 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .teacher (Term.var 0),
             mkCorrAtom .rich (Term.var 0)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C3.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x _ hIn
  obtain ⟨lit, hMem, hV⟩ := hIn
  simp only [ex954_C3, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (ii) step 2: prev goal
    rich(susan) is ground (FV = ∅). -/
theorem ex954_ii_hStdApart2 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rich (Term.const .susan)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev
  obtain ⟨lit, hMem, hV⟩ := hPrev
  simp at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (ii) step 3: prev goal
    rocksinger(susan) is ground (FV = ∅). -/
theorem ex954_ii_hStdApart3 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rocksinger (Term.const .susan)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev
  obtain ⟨lit, hMem, hV⟩ := hPrev
  simp at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (iii) step 1: prev goal
    FV = {1}, clause C_4 FV = {0}. Disjoint. -/
theorem ex954_iii_hStdApart1 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rich (Term.var 1)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev hClause
  -- hPrev: x ∈ FV({rich(V 1)}) so x = 1
  have hx1 : x = 1 := by
    obtain ⟨lit, hMem, hV⟩ := hPrev
    simp at hMem
    subst hMem
    simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    obtain ⟨_, h⟩ := hV; exact h
  -- hClause: x ∈ FV(C_4.toFOClause) so x = 0
  have hx0 : x = 0 := by
    obtain ⟨lit, hMem, hV⟩ := hClause
    simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
    rcases hMem with rfl | rfl
    · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h⟩ := hV; exact h
    · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h⟩ := hV; exact h
  omega

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (iii) step 2: clause C_1 is the
    ground fact rocksinger(jackson), so the implication is trivial. -/
theorem ex954_iii_hStdApart2 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rocksinger (Term.var 10)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C1.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x _ hIn
  obtain ⟨lit, hMem, hV⟩ := hIn
  simp only [ex954_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, List.mem_singleton] at hMem
  subst hMem
  simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (iv) step 1: same shape as (iii)
    step 1 — FV of prev goal = {1}, FV of C_4 = {0}. -/
theorem ex954_iv_hStdApart1 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rich (Term.var 1)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C4.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev hClause
  have hx1 : x = 1 := by
    obtain ⟨lit, hMem, hV⟩ := hPrev
    simp at hMem
    subst hMem
    simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    obtain ⟨_, h⟩ := hV; exact h
  have hx0 : x = 0 := by
    obtain ⟨lit, hMem, hV⟩ := hClause
    simp [ex954_C4, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
    rcases hMem with rfl | rfl
    · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h⟩ := hV; exact h
    · simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
      obtain ⟨_, h⟩ := hV; exact h
  omega

-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Std-apart helper for refutation (iv) step 2: prev goal FV = {10},
    clause C_5 FV = {2}. Disjoint. -/
theorem ex954_iv_hStdApart2 :
    ∀ x, (clauseFV (L := exCorrectnessLang) (hNoEq := exCorrectnessLang_noEq))
           ([mkCorrAtom .rocksinger (Term.var 10)].map FOLiteralCore.neg) x →
         ¬ (clauseFV (hNoEq := exCorrectnessLang_noEq)) (ex954_C5.toFOClause (hNoEq := exCorrectnessLang_noEq)) x := by
  intro x hPrev hClause
  have hx10 : x = 10 := by
    obtain ⟨lit, hMem, hV⟩ := hPrev
    simp at hMem
    subst hMem
    simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    obtain ⟨_, h⟩ := hV; exact h
  have hx2 : x = 2 := by
    obtain ⟨lit, hMem, hV⟩ := hClause
    simp [ex954_C5, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at hMem
    subst hMem
    simp [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars, mkCorrAtom, termVars] at hV
    obtain ⟨_, h⟩ := hV; exact h
  omega

-- -------------------------------------------------------------------
-- The four concrete SLD-refutations.
-- Each is a concrete chain of `FOSLDDerivation.init` / `.step`
-- applications with concrete ρ, σ, selected-atom, and head witnesses.
-- The `hUnif` fields are discharged by `rfl` (MGU equation reduces
-- definitionally for these concrete substitutions); `hSep` delegates
-- to the per-step helpers above.
-- -------------------------------------------------------------------

-- ===================================================================
-- Example 9.5.4 refutations (i)-(iv) — decomposed step-by-step
-- ===================================================================
-- Each refutation is built as a chain of named `noncomputable def`
-- named `<refutation>_step<n>`, to pin down the intermediate `prevGoal`
-- Finset explicitly at each stage and thereby support the bridge from
-- the concrete-list `hSep` / `hStdApart` helpers (stated over
-- list forms like `[teacher(X), rich(X)].map FOLiteral.neg`) to the
-- Finset-toList form required by the new API. The bridge uses
-- `clauseFV_neg_congr_of_mem_iff` (permutation invariance of `clauseFV`)
-- together with `IsSeparatingPair_of_clauseFV_eq` /
-- `hStdApart_of_clauseFV_eq` (congruence in clause-fv).

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A substitution binding one variable is most general when it fixes the
    replacement term and all other variables. -/
theorem singlePairMGU {L : Language} (x : Nat) (t : Term L)
    (sigma : Nat → Term L) (hAt : sigma x = t)
    (hAway : ∀ y, y ≠ x → sigma y = Term.var y)
    (hFix : termSubstAll t sigma = t) :
    IsPairwiseMGU sigma [(Term.var x, t)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hp
    rcases List.mem_singleton.mp hp with rfl
    simpa only [termSubstAll] using hAt.trans hFix.symm
  · intro y hy
    have heq : y = x := Classical.byContradiction (fun h => hy (hAway y h))
    subst y
    exact ⟨(Term.var x, t), by simp, Or.inl rfl⟩
  · intro other hOther
    refine ⟨other, ?_⟩
    intro y
    by_cases hy : y = x
    · subst y
      simpa only [SubstitutionCore.substCompose, hAt, termSubstAll] using
        hOther (Term.var x, t) (by simp)
    · simp [SubstitutionCore.substCompose, hAway y hy, termSubstAll]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem pairMGU_swap {L : Language} (a b : Term L) (sigma : Nat → Term L)
    (h : IsPairwiseMGU sigma [(b, a)]) : IsPairwiseMGU sigma [(a, b)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hp
    rcases List.mem_singleton.mp hp with rfl
    exact (h.1 (b, a) (by simp)).symm
  · intro x hx
    obtain ⟨pair, hp, hv⟩ := h.2.1 x hx
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨(a, b), by simp, hv.elim Or.inr Or.inl⟩
  · intro other hOther
    apply h.2.2 other
    intro pair hp
    rcases List.mem_singleton.mp hp with rfl
    exact (hOther (a, b) (by simp)).symm

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem corrMGU (p : ExCorrectnessPred) (a b : Term exCorrectnessLang)
    (sigma : Nat → Term exCorrectnessLang)
    (h : IsPairwiseMGU sigma [(a, b)]) :
    (IsAtomMGU (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom p a) (mkCorrAtom p b) sigma := by
  refine ⟨[(a, b)], ?_, h⟩
  erw [mkCorrAtom, mkCorrAtom, (atomUnifPairs?_predN_same (hNoEq := exCorrectnessLang_noEq))]
  cases p <;> change some (List.ofFn (fun _ : Fin 1 => (a, b))) = some [(a, b)]
  all_goals simp only [List.ofFn_succ, List.ofFn_zero]

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

