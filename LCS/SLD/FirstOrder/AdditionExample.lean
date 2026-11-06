import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.SLDDerivations
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.SLDRefutations
import Attach
import LCS.SLD.FirstOrder.AdditionExample.ProofsStamp

/-! # Example 9.4.1: addition of natural numbers

Section 9.4.1: the program axiomatizing addition, its two-step SLD-refutation for the goal :- add(succ(0), V, succ(succ(0))), the query and the computed answer. -/

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

/-- Example 9.4.1 (companion type): Predicate symbols for the addition
    example: one ternary predicate add. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddPred : Type where
  | add : ExAddPred

/-- Example 9.4.1 (companion type): Function symbols for the addition
    example: one unary function succ. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddFunc : Type where
  | succ : ExAddFunc

/-- Example 9.4.1 (companion type): Constant symbols for the addition
    example: zero. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddConst : Type where
  | zero : ExAddConst

/-- Example 9.4.1 (companion): The first-order language for the
    addition example with predicate add (rank 3), function succ
    (rank 1), constant zero, and no equality. -/
@[blueprint "chap9__example_9_4_1"]
def exAddLang : Language where
  funSymbols := ExAddFunc
  funArity := fun | .succ => 1
  constSymbols := ExAddConst
  predSymbols := ExAddPred
  predArity := fun | .add => 3
  hasEquality := false

/-- Example 9.4.1 (companion): build a Fin 3 -> alpha function from three values. -/
@[blueprint "chap9__example_9_4_1"]
def addVec3 (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- Example 9.4.1 (companion): build a Fin 1 -> alpha function from one value. -/
@[blueprint "chap9__example_9_4_1"]
def addVec1 (a : α) : Fin 1 → α
  | ⟨0, _⟩ => a

/-- Example 9.4.1 (companion): build the add(t1, t2, t3) atomic formula. -/
@[blueprint "chap9__example_9_4_1"]
def mkAdd (t1 t2 t3 : Term exAddLang) : FOAtom exAddLang rfl :=
  FOAtomCore.predN ExAddPred.add (addVec3 t1 t2 t3)

/-- Example 9.4.1 (companion): build succ(t). -/
@[blueprint "chap9__example_9_4_1"]
def mkSucc (t : Term exAddLang) : Term exAddLang :=
  Term.func ExAddFunc.succ (addVec1 t)

/-- Example 9.4.1 (companion): zero constant. -/
@[blueprint "chap9__example_9_4_1"]
def zeroTm : Term exAddLang :=
  Term.const ExAddConst.zero

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem termSubstAll_zeroTm (sigma : Nat → Term exAddLang) :
    termSubstAll zeroTm sigma = zeroTm := by
  rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): push structural atom
    substitution through `mkAdd`. -/
theorem formulaSubstAll_mkAdd (t1 t2 t3 : Term exAddLang)
    (σ : Nat → Term exAddLang) :
    (mkAdd t1 t2 t3).subst (hNoEq := by all_goals rfl) σ =
      mkAdd (termSubstAll t1 σ) (termSubstAll t2 σ) (termSubstAll t3 σ) := by
  -- BEGIN PROOF
  unfold mkAdd FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN ExAddPred.add
      (fun i => termSubstAll (addVec3 t1 t2 t3 i) σ) =
    FOAtomCore.predN ExAddPred.add
      (addVec3 (termSubstAll t1 σ)
        (termSubstAll t2 σ) (termSubstAll t3 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): push `termSubstAll σ` through `mkSucc`. -/
theorem termSubstAll_mkSucc (t : Term exAddLang) (σ : Nat → Term exAddLang) :
    termSubstAll (mkSucc t) σ = mkSucc (termSubstAll t σ) := by
  -- BEGIN PROOF
  unfold mkSucc
  simp only [termSubstAll]
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): FV of `mkAdd` = union of FVs. -/
theorem formulaVars_mkAdd (t1 t2 t3 : Term exAddLang) (n : Nat) :
    (mkAdd t1 t2 t3).vars n ↔
      termVars t1 n ∨ termVars t2 n ∨ termVars t3 n := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact Or.inl hi
    | 1, _ => exact Or.inr (Or.inl hi)
    | 2, _ => exact Or.inr (Or.inr hi)
  · rintro (h | h | h)
    · exact ⟨⟨0, by decide⟩, h⟩
    · exact ⟨⟨1, by decide⟩, h⟩
    · exact ⟨⟨2, by decide⟩, h⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): FV of `mkSucc` = FV of argument. -/
theorem termVars_mkSucc (t : Term exAddLang) (n : Nat) :
    termVars (mkSucc t) n ↔ termVars t n := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact hi
  · intro h
    exact ⟨⟨0, by decide⟩, h⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): s(0) is ground. -/
theorem termVars_mkSuccZero (x : Nat) : ¬ termVars (mkSucc zeroTm) x := by
  -- BEGIN PROOF
  rw [termVars_mkSucc]; exact id

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): termVars on `Term.var n`. -/
theorem termVars_var (n x : Nat) :
    termVars (L := exAddLang) (Term.var n) x ↔ x = n := Iff.rfl

/-- Example 9.4.1 (companion): The fact clause C_1: add(X, 0, X).
    Variables: X = var 0. Encoded as
    FOHornClause.fact (hNoEq := by all_goals rfl) (add(var 0, const zero, var 0)). -/
@[blueprint "chap9__example_9_4_1"]
def exAddClause_C1 : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.fact (hNoEq := by all_goals rfl) (mkAdd (Term.var 0) zeroTm (Term.var 0))

/-- Example 9.4.1 (companion): The rule clause C_2:
    add(X, succ(Y), succ(Z)) :- add(X, Y, Z).
    Variables: X = var 0, Y = var 1, Z = var 2.
    Encoded as FOHornClause.rule (hNoEq := by all_goals rfl)
      (add(var 0, succ(var 1), succ(var 2)))
      [add(var 0, var 1, var 2)]. -/
@[blueprint "chap9__example_9_4_1"]
def exAddClause_C2 : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.rule (hNoEq := by all_goals rfl)
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2)))
    (LCS.Finset.singleton (mkAdd (Term.var 0) (Term.var 1) (Term.var 2)))

/-- Example 9.4.1 (companion): The goal clause
    :- add(succ(0), V, succ(succ(0))).
    Variable: V = var 3.
    Encoded as FOHornClause.goal (hNoEq := by all_goals rfl)
      [add(succ(zero), var 3, succ(succ(zero)))]. -/
@[blueprint "chap9__example_9_4_1"]
def exAddGoal : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.goal (hNoEq := by all_goals rfl)
    (LCS.Finset.singleton (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV exAddClause_C2.toFOClause` ⊆ {0, 1, 2}. -/
theorem exAddClause_C2_FV_subset (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) x →
      x = 0 ∨ x = 1 ∨ x = 2 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty] at hMem
  rcases hMem with rfl | rfl
  · -- .neg (mkAdd (var 0) (var 1) (var 2))
    change FOAtomCore.vars (mkAdd (Term.var 0) (Term.var 1) (Term.var 2)) x at hV
    rw [formulaVars_mkAdd] at hV
    rcases hV with h | h | h <;> simp [termVars_var] at h <;> omega
  · -- .pos (mkAdd (var 0) (s (var 1)) (s (var 2)))
    change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) x at hV
    rw [formulaVars_mkAdd, termVars_mkSucc, termVars_mkSucc] at hV
    rcases hV with h | h | h <;> simp [termVars_var] at h <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV exAddClause_C1.toFOClause` ⊆ {0}. -/
theorem exAddClause_C1_FV_subset (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C1.toFOClause (hNoEq := by all_goals rfl)) x → x = 0 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton] at hMem
  subst hMem
  change FOAtomCore.vars (mkAdd (Term.var 0) zeroTm (Term.var 0)) x at hV
  rw [formulaVars_mkAdd] at hV
  rcases hV with h | h | h
  · simp [termVars_var] at h; exact h
  · exact absurd h id
  · simp [termVars_var] at h; exact h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `0 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_0 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 0
    rw [formulaVars_mkAdd]; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `1 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_1 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 1
    rw [formulaVars_mkAdd]; right; left; rw [termVars_mkSucc]; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `2 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_2 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 2
    rw [formulaVars_mkAdd]; right; right; rw [termVars_mkSucc]; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `0 ∈ clauseFV exAddClause_C1.toFOClause`. -/
theorem exAddClause_C1_FV_0 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C1.toFOClause (hNoEq := by all_goals rfl)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (mkAdd (Term.var 0) zeroTm (Term.var 0)), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton]
  · change FOAtomCore.vars (mkAdd (Term.var 0) zeroTm (Term.var 0)) 0
    rw [formulaVars_mkAdd]; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV (exAddGoal.bodyFOAtoms.map FOLiteral.neg) x ↔ x = 3`.
    The initial goal's clause-form FV is exactly {3}. -/
theorem exAddGoal_body_FV_eq_3 (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
        ([mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))].map
           FOLiteralCore.neg) x ↔ x = 3 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    change FOAtomCore.vars
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))) x at hV
    rw [formulaVars_mkAdd, termVars_mkSucc, termVars_mkSucc,
        termVars_mkSucc] at hV
    rcases hV with h | h | h
    · exact absurd h id
    · simpa [termVars_var] using h
    · exact absurd h id
  · rintro rfl
    refine ⟨FOLiteralCore.neg
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))) 3
      rw [formulaVars_mkAdd]; right; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV ([mkAdd (s 0) (var 5) (s 0)].map FOLiteral.neg) x ↔ x = 5`.
    This is the current goal of `exAddSLDStep1` after all rho/sigma are
    applied, and is the `prev` goal feeding `exAddSLDStep2`. -/
theorem exAddStep1_goal_FV_eq_5 (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
        ([mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)].map
           FOLiteralCore.neg) x ↔ x = 5 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    change FOAtomCore.vars
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)) x at hV
    rw [formulaVars_mkAdd] at hV
    rcases hV with h | h | h
    · exact absurd h (termVars_mkSuccZero _)
    · simpa [termVars_var] using h
    · exact absurd h (termVars_mkSuccZero _)
  · rintro rfl
    refine ⟨FOLiteralCore.neg
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars
        (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)) 5
      rw [formulaVars_mkAdd]; right; left; rfl

/-- Example 9.4.1: The logic program [C_1, C_2] axiomatizing addition
    of natural numbers. -/
@[blueprint "chap9__example_9_4_1" (main := true)]
def exAdditionProgram : List (FOHornClause exAddLang (by all_goals rfl)) :=
  [exAddClause_C1, exAddClause_C2]

/-- Example 9.4.1 (companion): The goal list for the addition example,
    containing the single goal clause to be refuted. -/
@[blueprint "chap9__example_9_4_1"]
def exAddGoals : List (FOHornClause exAddLang (by all_goals rfl)) :=
  [exAddGoal]

/-- Example 9.4.1 (companion): The initial derivation node N_0 for the
    goal :- add(succ(0), V, succ(succ(0))). Indexed by the body atoms of
    exAddGoal (a singleton list containing the add atom). -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep0 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
    (LCS.Finset.ofList
      [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]) := by
  have h := FOSLDDerivation.init (D := fun c => c ∈ exAdditionProgram) (goals := exAddGoals)
    exAddGoal (List.Mem.head _)
  simpa [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] using h

/-- Example 9.4.1 (companion): rho_1 renames C_2's variables apart.
    X=0 -> 4, Y=1 -> 5, Z=2 -> 6; identity elsewhere. -/
@[blueprint "chap9__example_9_4_1"]
def exAddRho1 : Nat → Term exAddLang
  | 0 => Term.var 4
  | 1 => Term.var 5
  | 2 => Term.var 6
  | n => Term.var n

/-- Example 9.4.1 (companion): sigma_1 = MGU of
    add(succ(0),V,succ(succ(0))) and rho_1(add(X,succ(Y),succ(Z))) =
    add(var4,succ(var5),succ(var6)).
    var 3 -> succ(var 5), var 4 -> succ(0), var 6 -> succ(0). -/
@[blueprint "chap9__example_9_4_1"]
def exAddSigma1 (n : Nat) : Term exAddLang :=
  if n = 3 then mkSucc (Term.var 5)
  else if n = 4 then mkSucc zeroTm
  else if n = 6 then mkSucc zeroTm
  else Term.var n

-- ATTACH-BLOCKER: private declaration
def exAddPairs1 : List (Term exAddLang × Term exAddLang) :=
  List.ofFn fun i : Fin 3 =>
    (addVec3 (mkSucc zeroTm) (Term.var 3)
      (mkSucc (mkSucc zeroTm)) i,
     addVec3 (Term.var 4) (mkSucc (Term.var 5))
      (mkSucc (Term.var 6)) i)

-- ATTACH-BLOCKER: private declaration
theorem exAddPairs1_eq :
    exAddPairs1 =
      [(mkSucc zeroTm, Term.var 4),
        (Term.var 3, mkSucc (Term.var 5)),
        (mkSucc (mkSucc zeroTm), mkSucc (Term.var 6))] := by
  unfold exAddPairs1
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

-- ATTACH-BLOCKER: private declaration
theorem exAddSigma1_isPairwiseMGU :
    IsPairwiseMGU exAddSigma1 exAddPairs1 := by
  rw [exAddPairs1_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_zeroTm,
        termSubstAll_mkSucc]
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_mkSucc]
    rcases List.mem_singleton.mp hPair with rfl
    simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_zeroTm,
      termSubstAll_mkSucc]
  · intro x hx
    by_cases h3 : x = 3
    · subst x
      refine ⟨(Term.var 3, mkSucc (Term.var 5)), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inl rfl
    by_cases h4 : x = 4
    · subst x
      refine ⟨(mkSucc zeroTm, Term.var 4), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inr rfl
    by_cases h6 : x = 6
    · subst x
      refine ⟨(mkSucc (mkSucc zeroTm), mkSucc (Term.var 6)),
        by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inr ⟨⟨0, by decide⟩, rfl⟩
    exact (hx (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, h3, h4, h6])).elim
  · intro sigmaOther hOther
    refine ⟨sigmaOther, ?_⟩
    intro x
    have h1 := hOther (mkSucc zeroTm, Term.var 4)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    have h2 := hOther (Term.var 3, mkSucc (Term.var 5))
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    have h3 := hOther
      (mkSucc (mkSucc zeroTm), mkSucc (Term.var 6))
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    by_cases hx3 : x = 3
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_mkSucc] at h2
      simpa [SubstitutionCore.substCompose, exAddSigma1, termSubstAll,
        termSubstAll_mkSucc] using h2
    by_cases hx4 : x = 4
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h1
      simpa [SubstitutionCore.substCompose, exAddSigma1, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] using h1.symm
    by_cases hx6 : x = 6
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h3
      have hArgs := eq_of_heq (Term.func.inj h3).2
      have hArg := congrFun hArgs (0 : Fin 1)
      calc
        sigmaOther 6 = mkSucc zeroTm := by
          simpa [mkSucc, addVec1] using hArg.symm
        _ = termSubstAll (exAddSigma1 6) sigmaOther := by
          simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll_mkSucc,
            termSubstAll_zeroTm]
        _ = SubstitutionCore.substCompose sigmaOther exAddSigma1 6 := rfl
    simp [SubstitutionCore.substCompose, exAddSigma1, termSubstAll, hx3, hx4, hx6]

@[blueprint "chap9__example_9_4_1"]
theorem exAddSigma1_isAtomMGU :
    (IsAtomMGU (hNoEq := by all_goals rfl))
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))
      ((mkAdd (Term.var 0) (mkSucc (Term.var 1))
          (mkSucc (Term.var 2))).subst (hNoEq := by all_goals rfl) exAddRho1)
      exAddSigma1

/-- Example 9.4.1 (companion): First SLD step: resolve goal
    :- add(succ(0), V, succ(succ(0))) with C_2 using separating
    renaming rho_1 (renaming C_2 variables to fresh indices) and
    MGU sigma_1, yielding :- add(succ(0), Y_2, succ(0)).

    Built as a direct `FOSLDDerivation.step` onto `exAddSLDStep0`.
    The per-field side conditions are the MGU certificate and
    local separating-pair conditions for
    rho_1 (disjoint rename of 0..2 to 4..6). Each reduces by
    Fin-case decomposition / clauseFV enumeration and is left as a
    per-field `sorry`. The whole-value construction is NOT sorry —
    the derivation shape is a real `.step` term. -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep1 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
    (((
      (LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)) :=
  FOSLDDerivation.step
    (prev := exAddSLDStep0)
    (clause := exAddClause_C2)
    (hClause := by change exAddClause_C2 ∈ exAdditionProgram; simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAdditionProgram])
    (hDef := by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.isDefinite, FOHornClauseCore.isDefinite, FOHornClauseCore.body, finset_toList_empty])
    (rho := exAddRho1)
    (sigma := exAddSigma1)
    (Ak := mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))
    (headA := mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2)))
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by rfl)
    (hMGU := exAddSigma1_isAtomMGU)
    (hSep := by
      -- prev goal (as Finset) = {add(s(0), V 3, s(s 0))}, FV = {3}.
      -- Clause = C_2, FV = {0, 1, 2}. rho = exAddRho1 renames to {4, 5, 6}.
      -- Reduce clauseFV of (Finset.ofList [atom]).toList via membership congr.
      have hCongr : (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
          ((LCS.Finset.ofList
            [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).toList.map
              FOLiteralCore.neg) =
          (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
          ([mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))].map
              FOLiteralCore.neg) := by
        apply (clauseFV_map_neg_mem_congr (hNoEq := by all_goals rfl))
        intro a
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      change IsSeparatingPair (L := exAddLang) (hNoEq := rfl) Term.var exAddRho1 _ _
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- substIsVarOnSet Term.var (FV prev)
        intro x _; exact ⟨x, rfl⟩
      · -- substIsVarOnSet exAddRho1 (FV C_2)
        intro x _
        rcases x with _ | _ | _ | n
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨n + 3, rfl⟩
      · -- injective for Term.var on prev: trivial
        intro x y _ _ h; cases h; rfl
      · -- injective for exAddRho1 on FV(C_2) ⊆ {0, 1, 2}
        intro x y hx hy h
        have hxmem := exAddClause_C2_FV_subset x hx
        have hymem := exAddClause_C2_FV_subset y hy
        rcases hxmem with rfl | rfl | rfl <;>
          rcases hymem with rfl | rfl | rfl <;>
            first | rfl | simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho1] at h
      · -- Range disjointness.
        -- Range of Term.var on FV(prev) = {3}.
        -- Range of exAddRho1 on FV(C_2) ⊆ {0,1,2} = {4,5,6}.
        funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          rw [exAddGoal_body_FV_eq_3] at hPrev
          subst hPrev
          have hn3 : n = 3 :=
            (Term.var.injEq (L := exAddLang) _ _).mp hEq₁ |>.symm
          subst hn3
          have hx₂mem := exAddClause_C2_FV_subset x₂ hClause
          rcases hx₂mem with rfl | rfl | rfl <;> simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho1] at hEq₂
        · intro h; exact absurd h id
      · -- Support of Term.var: identity everywhere.
        intro _ _; rfl
      · -- Support of exAddRho1: identity outside {0, 1, 2}.
        intro x hx
        rcases x with _ | _ | _ | n
        · exfalso; exact hx exAddClause_C2_FV_0
        · exfalso; exact hx exAddClause_C2_FV_1
        · exfalso; exact hx exAddClause_C2_FV_2
        · rfl)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): The type index of `exAddSLDStep1`
    equals the Finset with the single atom
    `mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)` as its sole
    element. -/
theorem exAddStep1_currentGoal :
    (((
      (LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)) =
    LCS.Finset.ofList
      [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] := by
  -- BEGIN PROOF
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
      simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha'
      subst ha'
      unfold exAddRho1 exAddSigma1
      simp [formulaSubstAll_mkAdd, termSubstAll_mkSucc]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨(mkAdd (Term.var 0) (Term.var 1) (Term.var 2)).subst (hNoEq := by all_goals rfl)
      exAddRho1, ?_, ?_⟩
    · rw [LCS.Finset.mem_union]
      right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨mkAdd (Term.var 0) (Term.var 1) (Term.var 2), ?_, rfl⟩
      simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty]
    · unfold exAddRho1 exAddSigma1
      simp [formulaSubstAll_mkAdd, termSubstAll_mkSucc]
      rfl

/-- Example 9.4.1 (companion): rho_2 renames C_1's variable X apart. -/
@[blueprint "chap9__example_9_4_1"]
def exAddRho2 : Nat → Term exAddLang
  | 0 => Term.var 7
  | n => Term.var n

/-- Example 9.4.1 (companion): sigma_2 = MGU of
    add(succ(0),Y_2,succ(0)) and rho_2(add(X,0,X)) = add(var7,0,var7).
    var 5 -> 0, var 7 -> succ(0). -/
@[blueprint "chap9__example_9_4_1"]
def exAddSigma2 (n : Nat) : Term exAddLang :=
  if n = 5 then zeroTm
  else if n = 7 then mkSucc zeroTm
  else Term.var n

-- ATTACH-BLOCKER: private declaration
def exAddPairs2 : List (Term exAddLang × Term exAddLang) :=
  List.ofFn fun i : Fin 3 =>
    (addVec3 (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm) i,
     addVec3 (Term.var 7) zeroTm (Term.var 7) i)

-- ATTACH-BLOCKER: private declaration
theorem exAddPairs2_eq :
    exAddPairs2 =
      [(mkSucc zeroTm, Term.var 7),
        (Term.var 5, zeroTm),
        (mkSucc zeroTm, Term.var 7)] := by
  unfold exAddPairs2
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

-- ATTACH-BLOCKER: private declaration
theorem exAddSigma2_isPairwiseMGU :
    IsPairwiseMGU exAddSigma2 exAddPairs2 := by
  rw [exAddPairs2_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm,
        termSubstAll_mkSucc]
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm]
    rcases List.mem_singleton.mp hPair with rfl
    simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm,
      termSubstAll_mkSucc]
  · intro x hx
    by_cases h5 : x = 5
    · subst x
      refine ⟨(Term.var 5, zeroTm), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2], Or.inl rfl⟩
    by_cases h7 : x = 7
    · subst x
      refine ⟨(mkSucc zeroTm, Term.var 7),
        by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2], Or.inr rfl⟩
    exact (hx (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, h5, h7])).elim
  · intro sigmaOther hOther
    refine ⟨sigmaOther, ?_⟩
    intro x
    have h1 := hOther (mkSucc zeroTm, Term.var 7)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2])
    have h2 := hOther (Term.var 5, zeroTm)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2])
    by_cases hx5 : x = 5
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm] at h2
      simpa [SubstitutionCore.substCompose, exAddSigma2, termSubstAll,
        termSubstAll_zeroTm] using h2
    by_cases hx7 : x = 7
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h1
      simpa [SubstitutionCore.substCompose, exAddSigma2, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] using h1.symm
    simp [SubstitutionCore.substCompose, exAddSigma2, termSubstAll, hx5, hx7]

@[blueprint "chap9__example_9_4_1"]
theorem exAddSigma2_isAtomMGU :
    (IsAtomMGU (hNoEq := by all_goals rfl))
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))
      ((mkAdd (Term.var 0) zeroTm (Term.var 0)).subst (hNoEq := by all_goals rfl) exAddRho2)
      exAddSigma2

/-- Example 9.4.1 (companion): The full SLD-refutation for the goal
    :- add(succ(0), V, succ(succ(0))), completing via C_1 with
    MGU sigma_2 mapping X->succ(0), Y_2->0, yielding the empty clause.
    Built as `.step` onto `exAddSLDStep1` with the base clause C_1.
    `exAddClause_C1.bodyFOAtoms = []` and `exAddSLDStep1` has a
    singleton current goal, so the output index `(prev.take 0 ++ []
    ++ prev.drop 1).map σ = [].map σ = []` reduces definitionally.
    Per-field obligations (hMGU, hSep, hAk) are left as
    `sorry` — the whole derivation value is a real `.step` term,
    not an axiom-equivalent sorry-def. -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep2 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals ∅ := by
  -- The .step output index is
  --   ((step1.index.erase Ak).union (ofList (C_1.bodyFOAtoms.map rho_2))).image sigma_2
  -- which reduces to ∅ because step1.index = {atom_5}, erase atom_5 = ∅,
  -- C_1.bodyFOAtoms = [], and .image of ∅ = ∅.
  let step1Idx : LCS.Finset (FOAtom exAddLang rfl) :=
    (((LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)
  have step2raw :
      (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
        (((step1Idx.erase
            (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))).union
          (LCS.Finset.ofList
            (exAddClause_C1.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho2)))
          ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma2)) :=
    FOSLDDerivation.step
      (prev := exAddSLDStep1)
      (clause := exAddClause_C1)
      (hClause := by change exAddClause_C1 ∈ exAdditionProgram; simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAdditionProgram])
      (hDef := by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.isDefinite, FOHornClauseCore.isDefinite, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton])
      (rho := exAddRho2)
      (sigma := exAddSigma2)
      (Ak := mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))
      (headA := mkAdd (Term.var 0) zeroTm (Term.var 0))
      (hAk := by
        rw [exAddStep1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by rfl)
      (hMGU := exAddSigma2_isAtomMGU)
      (hSep := by
        -- prevGoal as Finset = {mkAdd (s 0) (var 5) (s 0)}; FV = {5}.
        -- FV(C_1) = {0}. rho = exAddRho2 renames 0 to 7.
        have hCongr : (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
            ([mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)].map
                FOLiteralCore.neg) := by
          apply (clauseFV_map_neg_mem_congr (hNoEq := by all_goals rfl))
          intro a
          rw [LCS.Finset.mem_toList]
          show a ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList
              [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] from
              exAddStep1_currentGoal, LCS.Finset.mem_ofList]
        change IsSeparatingPair (L := exAddLang) (hNoEq := rfl) Term.var exAddRho2 _ _
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | n
          · exact ⟨7, rfl⟩
          · exact ⟨n + 1, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy h
          have hxmem := exAddClause_C1_FV_subset x hx
          have hymem := exAddClause_C1_FV_subset y hy
          subst hxmem; subst hymem; rfl
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            rw [exAddStep1_goal_FV_eq_5] at hPrev
            subst hPrev
            have hn5 : n = 5 :=
              (Term.var.injEq (L := exAddLang) _ _).mp hEq₁ |>.symm
            subst hn5
            have hx₂0 := exAddClause_C1_FV_subset x₂ hClause
            subst hx₂0
            simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho2] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | n
          · exfalso; exact hx exAddClause_C1_FV_0
          · rfl)

  -- Cast step2raw's Finset index to ∅ via extensionality.
  have hIdx :
      (((step1Idx.erase
          (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))).union
        (LCS.Finset.ofList
          (exAddClause_C1.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho2)))
        ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma2)) =
      (∅ : LCS.Finset (FOAtom exAddLang rfl)) := by
    apply LCS.Finset.ext
    intro a
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step1Idx = LCS.Finset.ofList
                [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] from
                exAddStep1_currentGoal,
            LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  rw [hIdx] at step2raw
  exact step2raw

/-- Example 9.4.1 (companion): Proof that the two-step derivation
    terminates with the empty clause (is a refutation). Since
    `FOSLDDerivation.isRefutation d` reduces to `currentGoal = ∅`
    and exAddSLDStep2 has type `FOSLDDerivation D goals ∅`, this
    follows by `rfl`. -/
@[blueprint "chap9__example_9_4_1"]
theorem exAddRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := by all_goals rfl)) exAddSLDStep2 

/-- Example 9.4.1: The answer component: the value of V = succ(zero), meaning
    succ(0) + succ(0) = succ(succ(0)). -/
@[blueprint "chap9__example_9_4_1" (main := true)]
def exAddAnswerBinding : Term exAddLang :=
  mkSucc zeroTm

end LCS.SLD.FirstOrder
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm LCS.FOResolution.Unification
open LCS.FOResolution.Method.Soundness

/-- The positive two-successor query matrix of Example 9.4.1 (SQ28). -/
@[blueprint "chap9__example_9_4_1"]
def exAddQueryAtom : FOAtom exAddLang (by all_goals rfl) :=
  mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))

/-- The existential query asks for V in add(succ(0), V, succ(succ(0))) (SQ28). -/
@[blueprint "chap9__example_9_4_1"]
def exAddQuery : FormulaN exAddLang := .ex 3 exAddQueryAtom.toFormula

/-- The universal closures of the two actual addition clauses. -/
@[blueprint "chap9__example_9_4_1"]
def exAddProgramFormula : FormulaN exAddLang :=
  hornClauses_to_formulaN (by all_goals rfl) exAddQueryAtom.toFormula exAdditionProgram

/-- The universally closed negative goal B from Example 9.4.1. -/
@[blueprint "chap9__example_9_4_1"]
def exAddNegativeGoalFormula : FormulaN exAddLang :=
  FOClause.universalClosure (by all_goals rfl) exAddQueryAtom.toFormula exAddGoal.toFOClause
    (hornClauseVarsList (by all_goals rfl) exAddQueryAtom.toFormula exAddGoal)

/-- Unsatisfiability of the displayed program and negative goal is equivalent
    to validity of its negation, then to the existential query consequence.
    The original query variable V is observed through the full answer map
    (SQ26/SQ28). -/
@[attach_debt, blueprint "chap9__example_9_4_1"]
theorem exAddQuery_goalConsistent_iff :
    (∀ (M : Structure exAddLang) (s : Assignment M),
      formulaEvalN M exAddNegativeGoalFormula s ↔
        formulaEvalN M (.all 3 (.neg exAddQueryAtom.toFormula)) s) ∧
    (FOHornClauseSet.isUnsatisfiable (by all_goals rfl) exAddQueryAtom.toFormula
        (exAdditionProgram ++ [exAddGoal]) ↔
      universallyValidN (.neg (.conj exAddProgramFormula exAddNegativeGoalFormula))) ∧
    (universallyValidN (.neg (.conj exAddProgramFormula exAddNegativeGoalFormula)) ↔
      universallyValidN (.impl exAddProgramFormula exAddQuery)) ∧
    FOSLDDerivation.resultSubstitution (by all_goals rfl) exAddSLDStep2 3 = exAddAnswerBinding ∧
    exAddQueryAtom.mapTerms
        (fun t => termSubstAll t (FOSLDDerivation.resultSubstitution (by all_goals rfl) exAddSLDStep2)) =
      mkAdd (mkSucc zeroTm) exAddAnswerBinding (mkSucc (mkSucc zeroTm))

/-- Numeral terms in the language of Example 9.4.1. -/
@[blueprint "chap9__example_9_4_1"]
def exAddNumeral : Nat → Term exAddLang
  | 0 => zeroTm
  | n + 1 => mkSucc (exAddNumeral n)

/-- The least atom relation generated by substitution instances of the two
    actual program clauses. Premises use exactly the body of the chosen clause
    and the conclusion uses its head (SQ27). -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAdditionGenerated : FOAtom exAddLang (by all_goals rfl) → Prop where
  | clause (c : FOHornClause exAddLang (by all_goals rfl)) (hc : c ∈ exAdditionProgram)
      (sigma : Nat → Term exAddLang) (head : FOAtom exAddLang (by all_goals rfl))
      (hHead : c.headFOAtom = some head)
      (premises : ∀ a ∈ c.body,
        ExAdditionGenerated (a.mapTerms (fun t => termSubstAll t sigma))) :
      ExAdditionGenerated (head.mapTerms (fun t => termSubstAll t sigma))

/-- The computed value of V denotes the arithmetic difference 2 − 1, and its
    instantiated query belongs to the relation generated by the program (SQ27). -/
@[attach_debt, blueprint "chap9__example_9_4_1"]
theorem exAddAnswer_arithmeticDifference :
    FOSLDDerivation.resultSubstitution (by all_goals rfl) exAddSLDStep2 3 = exAddNumeral (2 - 1) ∧
    exAddAnswerBinding = exAddNumeral (2 - 1) ∧
    ExAdditionGenerated
      (mkAdd (exAddNumeral 1)
        (FOSLDDerivation.resultSubstitution (by all_goals rfl) exAddSLDStep2 3) (exAddNumeral 2)) ∧
    1 + (2 - 1) = (2 : Nat)

end LCS.SLD.FirstOrder
end
