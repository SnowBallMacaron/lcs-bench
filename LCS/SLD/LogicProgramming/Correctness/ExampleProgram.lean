import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import Attach
import LCS.SLD.LogicProgramming.Correctness.ExampleProgram.ProofsStamp

/-! # Example 9.5.4: program, clauses and unifiers

Section 9.5.3: the logic program of Example 9.5.1 as a clause set, its definite clauses C_1-C_5, the two goals, and the unifier and separation facts shared by the four refutations. -/

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

theorem corrMGU (p : ExCorrectnessPred) (a b : Term exCorrectnessLang)
    (sigma : Nat → Term exCorrectnessLang)
    (h : IsPairwiseMGU sigma [(a, b)]) :
    (IsAtomMGU (hNoEq := exCorrectnessLang_noEq)) (mkCorrAtom p a) (mkCorrAtom p b) sigma := by
  refine ⟨[(a, b)], ?_, h⟩
  erw [mkCorrAtom, mkCorrAtom, (atomUnifPairs?_predN_same (hNoEq := exCorrectnessLang_noEq))]
  cases p <;> change some (List.ofFn (fun _ : Fin 1 => (a, b))) = some [(a, b)]
  all_goals simp only [List.ofFn_succ, List.ofFn_zero]

end LCS.SLD.LogicProgramming.Correctness
end
