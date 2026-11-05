import LCS.Item
import LCS.Util
import LCS.FirstOrder.SemanticsN
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Soundness
import LCS.SLD.FirstOrder
import LCS.SLD.PrologSyntax
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness

noncomputable section
set_option linter.unusedSimpArgs false
namespace LCS.Examples.PrologReverse
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.Unification
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.PrologSyntax
open LCS.SLD.LogicProgramming
open LCS.SLD.LogicProgramming.Correctness

/-- Constants of `L_rev`: elements `a`, `b`, and the empty list. -/
inductive RevConst : Type where
  | a    : RevConst
  | b    : RevConst
  | nilC : RevConst
  deriving DecidableEq, Repr

/-- Functions of `L_rev`: cons (./2). -/
inductive RevFunc : Type where
  | cons : RevFunc
  deriving DecidableEq, Repr

/-- Predicates of `L_rev`: append/3 and reverse/2. -/
inductive RevPred : Type where
  | append  : RevPred
  | reverse : RevPred
  deriving DecidableEq, Repr

/-- The first-order language for the `reverse` demo. -/
def revLang : Language where
  funSymbols   := RevFunc
  funArity     := fun | .cons => 2
  constSymbols := RevConst
  predSymbols  := RevPred
  predArity    := fun | .append => 3 | .reverse => 2
  hasEquality  := false

/-- The example language contains predicate atoms only. -/
theorem language_noEq : revLang.withoutEquality := rfl

-- ===================================================================
-- §2.  Prolog-style term constructors and smart atoms
-- ===================================================================
/-- Prolog empty list `[]`. -/
def nil : Term revLang := Term.const RevConst.nilC

/-- Prolog constants. -/
def a : Term revLang := Term.const RevConst.a
def b : Term revLang := Term.const RevConst.b

/-- Prolog cons: `[H | T]`. -/
def cons (h t : Term revLang) : Term revLang :=
  Term.func RevFunc.cons (pFin2 h t)

/-- Prolog list-literal notation (restricted subset). -/
notation "⟦" "⟧"                   => nil
notation "⟦" x "⟧"                 => cons x nil
notation "⟦" x ", " y "⟧"          => cons x (cons y nil)
notation "⟦" x ", " y ", " z "⟧"   => cons x (cons y (cons z nil))
notation "⟦" h " | " t "⟧"         => cons h t

/-- Prolog atom `append(L1, L2, L3)`. -/
def append (l1 l2 l3 : Term revLang) : FOAtom revLang language_noEq :=
  FOAtomCore.predN (L := revLang) RevPred.append (pFin3 l1 l2 l3)

/-- Prolog-style call syntax: `append(l1, l2, l3)`. -/
scoped notation:max "append(" l1 ", " l2 ", " l3 ")" => append l1 l2 l3

/-- Prolog atom `reverse(L, R)`. -/
def reverse (l r : Term revLang) : FOAtom revLang language_noEq :=
  FOAtomCore.predN (L := revLang) RevPred.reverse (pFin2 l r)

/-- Prolog-style call syntax: `reverse(l, r)`. -/
scoped notation:max "reverse(" l ", " r ")" => reverse l r

-- ===================================================================
-- §2b.  Substitution and free-variable helpers
--
-- `formulaSubstAll` and `termSubstAll` don't reduce definitionally
-- through the Fin-indexed `pFin3`/`pFin2` arguments. These helper
-- lemmas push the substitution through `append`, `reverse`, `cons`,
-- `nil`, `a`, `b` at the surface-syntax level. Parallel versions of
-- `formulaSubstAll_append` / `termVars_cons` / ... from `PrologAppend`
-- but on `revLang`.
-- ===================================================================
/-- Push structural atom substitution through `append l1 l2 l3`. -/
theorem formulaSubstAll_append (l1 l2 l3 : Term revLang)
    (σ : Nat → Term revLang) :
    (append l1 l2 l3).subst (hNoEq := language_noEq) σ =
      append (LCS.FOResolution.Unification.termSubstAll l1 σ)
             (LCS.FOResolution.Unification.termSubstAll l2 σ)
             (LCS.FOResolution.Unification.termSubstAll l3 σ) := by
  -- BEGIN PROOF
  unfold append FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := revLang) RevPred.append
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin3 l1 l2 l3 i) σ) =
    FOAtomCore.predN (L := revLang) RevPred.append
      (pFin3
        (LCS.FOResolution.Unification.termSubstAll l1 σ)
        (LCS.FOResolution.Unification.termSubstAll l2 σ)
        (LCS.FOResolution.Unification.termSubstAll l3 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- Push structural atom substitution through `reverse l r`. -/
theorem formulaSubstAll_reverse (l r : Term revLang)
    (σ : Nat → Term revLang) :
    (reverse l r).subst (hNoEq := language_noEq) σ =
      reverse (LCS.FOResolution.Unification.termSubstAll l σ)
              (LCS.FOResolution.Unification.termSubstAll r σ) := by
  -- BEGIN PROOF
  unfold reverse FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := revLang) RevPred.reverse
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin2 l r i) σ) =
    FOAtomCore.predN (L := revLang) RevPred.reverse
      (pFin2
        (LCS.FOResolution.Unification.termSubstAll l σ)
        (LCS.FOResolution.Unification.termSubstAll r σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Push `termSubstAll σ` through `cons h t`. -/
theorem termSubstAll_cons (h t : Term revLang) (σ : Nat → Term revLang) :
    LCS.FOResolution.Unification.termSubstAll (cons h t) σ =
      cons (LCS.FOResolution.Unification.termSubstAll h σ)
           (LCS.FOResolution.Unification.termSubstAll t σ) := by
  -- BEGIN PROOF
  unfold cons
  simp only [LCS.FOResolution.Unification.termSubstAll]
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

/-- `termSubstAll σ nil = nil`. -/
theorem termSubstAll_nil (σ : Nat → Term revLang) :
    LCS.FOResolution.Unification.termSubstAll nil σ = nil := rfl

/-- `termSubstAll σ a = a`. -/
theorem termSubstAll_a (σ : Nat → Term revLang) :
    LCS.FOResolution.Unification.termSubstAll a σ = a := rfl

/-- `termSubstAll σ b = b`. -/
theorem termSubstAll_b (σ : Nat → Term revLang) :
    LCS.FOResolution.Unification.termSubstAll b σ = b := rfl

/-- FV of `append l1 l2 l3`. -/
theorem formulaVars_append (l1 l2 l3 : Term revLang) (x : Nat) :
    (append l1 l2 l3).vars x ↔
      termVars l1 x ∨ termVars l2 x ∨ termVars l3 x := by
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

/-- FV of `reverse l r`. -/
theorem formulaVars_reverse (l r : Term revLang) (x : Nat) :
    (reverse l r).vars x ↔
      termVars l x ∨ termVars r x := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact Or.inl hi
    | 1, _ => exact Or.inr hi
  · rintro (h | h)
    · exact ⟨⟨0, by decide⟩, h⟩
    · exact ⟨⟨1, by decide⟩, h⟩

/-- FV of `cons h t`. -/
theorem termVars_cons (h t : Term revLang) (x : Nat) :
    termVars (cons h t) x ↔ termVars h x ∨ termVars t x := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact Or.inl hi
    | 1, _ => exact Or.inr hi
  · rintro (h | h)
    · exact ⟨⟨0, by decide⟩, h⟩
    · exact ⟨⟨1, by decide⟩, h⟩

theorem termVars_V (n x : Nat) : termVars (L := revLang) (V n) x ↔ x = n := Iff.rfl
theorem termVars_a_iff (x : Nat) : termVars a x ↔ False := Iff.rfl
theorem termVars_b_iff (x : Nat) : termVars b x ↔ False := Iff.rfl
theorem termVars_nil_iff (x : Nat) : termVars nil x ↔ False := Iff.rfl

-- ===================================================================
-- §3.  Variables (by Prolog convention, uppercase letters)
-- ===================================================================
-- append/3 clauses share the same variables as PrologAppend:
-- X=V 0, Xs=V 1, Y=V 2, Zs=V 3, and the "L" of the base fact = V 0.

-- reverse/2 clauses:
--   reverse([], []).
--   reverse([H|T], R) :- reverse(T, Rt), append(Rt, [H], R).
abbrev H  : Term revLang := V 4     -- head in reverse-rec
abbrev T  : Term revLang := V 5     -- tail in reverse-rec
abbrev R' : Term revLang := V 6     -- result in reverse-rec
abbrev Rt : Term revLang := V 7     -- intermediate reversed tail
-- Query output:
abbrev R  : Term revLang := V 100

-- ===================================================================
-- §4.  The program: append/3 ⨁ reverse/2
-- ===================================================================

/--
    ```prolog
    append([], L, L).
    ``` -/
def clauseAppBase : FOHornClause revLang language_noEq :=
  (fact (hNoEq := language_noEq)) append(⟦⟧, V 0, V 0)

/--
    ```prolog
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).
    ``` -/
def clauseAppRec : FOHornClause revLang language_noEq :=
  append(⟦V 0 | V 1⟧, V 2, ⟦V 0 | V 3⟧) :- append(V 1, V 2, V 3)

/--
    ```prolog
    reverse([], []).
    ``` -/
def clauseRevBase : FOHornClause revLang language_noEq :=
  (fact (hNoEq := language_noEq)) reverse(⟦⟧, ⟦⟧)

/--
    ```prolog
    reverse([H | T], R) :- reverse(T, Rt), append(Rt, [H], R).
    ```
    Variables: H = V 4, T = V 5, R = V 6, Rt = V 7. -/
def clauseRevRec : FOHornClause revLang language_noEq :=
  reverse(⟦H | T⟧, R') :- reverse(T, Rt), append(Rt, ⟦H⟧, R')

/-- The full program `P_rev`: 4 clauses — 2 for append, 2 for reverse. -/
def revProgram : List (FOHornClause revLang language_noEq) :=
  [clauseAppBase, clauseAppRec, clauseRevBase, clauseRevRec]

/--
    ```prolog
    ?- reverse([a, b], R).
    ``` -/
def queryGoal : FOHornClause revLang language_noEq :=
  (?- reverse(⟦a, b⟧, R)).toGoal

-- ===================================================================
-- §4b.  Free-variable enumeration lemmas for the program and query
--
-- These characterise `clauseFV` for each program clause and for the
-- query-goal literal set. They support the IsSeparatingPair and
-- standardization-apart proofs at each resolution step below.
-- ===================================================================

/-- `clauseFV clauseAppBase.toFOClause` ⊆ {0}. -/
theorem clauseAppBase_FV_subset (x : Nat) :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppBase.toFOClause (hNoEq := language_noEq)) x → x = 0 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseAppBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  subst hMem
  simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
             termVars_nil_iff, termVars_V,
             or_self, or_false, false_or] at hV
  exact hV

/-- `0 ∈ clauseFV clauseAppBase.toFOClause`. -/
theorem clauseAppBase_FV_0 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppBase.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append nil (V 0) (V 0)), ?_, ?_⟩
  · simp [clauseAppBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append nil (V 0) (V 0)) 0
    rw [formulaVars_append]; right; left; rfl

/-- `clauseFV clauseAppRec.toFOClause` ⊆ {0, 1, 2, 3}. -/
theorem clauseAppRec_FV_subset (x : Nat) :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppRec.toFOClause (hNoEq := language_noEq)) x → x ≤ 3 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseAppRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  rcases hMem with rfl | rfl
  · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, termVars_V] at hV
    omega
  · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, termVars_V] at hV
    omega

theorem clauseAppRec_FV_0 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppRec.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧), ?_, ?_⟩
  · simp [clauseAppRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧) 0
    rw [formulaVars_append]; left; rw [termVars_cons]; left; rfl

theorem clauseAppRec_FV_1 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppRec.toFOClause (hNoEq := language_noEq)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧), ?_, ?_⟩
  · simp [clauseAppRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧) 1
    rw [formulaVars_append]; left; rw [termVars_cons]; right; rfl

theorem clauseAppRec_FV_2 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppRec.toFOClause (hNoEq := language_noEq)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧), ?_, ?_⟩
  · simp [clauseAppRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧) 2
    rw [formulaVars_append]; right; left; rfl

theorem clauseAppRec_FV_3 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseAppRec.toFOClause (hNoEq := language_noEq)) 3 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧), ?_, ?_⟩
  · simp [clauseAppRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧) 3
    rw [formulaVars_append]; right; right; rw [termVars_cons]; right; rfl

/-- `clauseRevBase = fact (reverse nil nil)` has NO variables. -/
theorem clauseRevBase_FV_empty (x : Nat) :
    ¬ (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevBase.toFOClause (hNoEq := language_noEq)) x := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseRevBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  subst hMem
  simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_reverse,
             termVars_nil_iff, or_self] at hV

/-- `clauseFV clauseRevRec.toFOClause` ⊆ {4, 5, 6, 7}. -/
theorem clauseRevRec_FV_subset (x : Nat) :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevRec.toFOClause (hNoEq := language_noEq)) x → 4 ≤ x ∧ x ≤ 7 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseRevRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  rcases hMem with (rfl | rfl) | rfl
  · -- .neg (reverse T Rt)
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_reverse,
               T, Rt, termVars_V] at hV
    omega
  · -- .neg (append Rt ⟦H⟧ R')
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, termVars_nil_iff, H, Rt, R', termVars_V,
               or_self, or_false, false_or] at hV
    omega
  · -- .pos (reverse ⟦H | T⟧ R')
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_reverse,
               termVars_cons, H, T, R', termVars_V] at hV
    omega

theorem clauseRevRec_FV_4 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevRec.toFOClause (hNoEq := language_noEq)) 4 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (reverse ⟦H | T⟧ R'), ?_, ?_⟩
  · simp [clauseRevRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (reverse ⟦H | T⟧ R') 4
    rw [formulaVars_reverse]; left; rw [termVars_cons]; left
    change termVars (V 4) 4; rfl

theorem clauseRevRec_FV_5 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevRec.toFOClause (hNoEq := language_noEq)) 5 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (reverse ⟦H | T⟧ R'), ?_, ?_⟩
  · simp [clauseRevRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (reverse ⟦H | T⟧ R') 5
    rw [formulaVars_reverse]; left; rw [termVars_cons]; right
    change termVars (V 5) 5; rfl

theorem clauseRevRec_FV_6 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevRec.toFOClause (hNoEq := language_noEq)) 6 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (reverse ⟦H | T⟧ R'), ?_, ?_⟩
  · simp [clauseRevRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (reverse ⟦H | T⟧ R') 6
    rw [formulaVars_reverse]; right
    change termVars (V 6) 6; rfl

theorem clauseRevRec_FV_7 :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) (clauseRevRec.toFOClause (hNoEq := language_noEq)) 7 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.neg (reverse T Rt), ?_, ?_⟩
  · simp [clauseRevRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (reverse T Rt) 7
    rw [formulaVars_reverse]; right
    change termVars (V 7) 7; rfl

/-- `clauseFV queryGoal = {100}`. -/
theorem queryGoal_FV_eq_100 (x : Nat) :
    (clauseFV (L := revLang) (hNoEq := language_noEq)) ([reverse ⟦a, b⟧ R].map FOLiteralCore.neg) x
      ↔ x = 100 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_reverse,
               termVars_cons, termVars_a_iff, termVars_b_iff,
               termVars_nil_iff, R, termVars_V,
               or_self, or_false, false_or] at hV
    exact hV
  · rintro rfl
    refine ⟨FOLiteralCore.neg (reverse ⟦a, b⟧ R), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars (reverse ⟦a, b⟧ R) 100
      rw [formulaVars_reverse]; right
      change termVars (V 100) 100; rfl

-- ===================================================================
-- §5.  Well-formedness against (revProgram, [queryGoal])
-- ===================================================================

/-- The single query goal is a `.goal`-shaped Horn clause. -/
theorem goalsAreGoals :
    ∀ g ∈ [queryGoal], ∃ body, g = (FOHornClause.goal (hNoEq := language_noEq)) body := by
  -- BEGIN PROOF
  intro g hg
  simp at hg
  subst hg
  exact ⟨_, rfl⟩

/-- Every clause in `revProgram ++ [queryGoal]` is quantifier-free. -/
theorem allQF :
    ∀ c ∈ revProgram ++ [queryGoal],
      (FOHornClause.allAtomsQF (hNoEq := language_noEq)) c := by
  -- BEGIN PROOF
  intro c _
  exact (FOHornClause.allAtomsQF_derived (hNoEq := language_noEq)) c

-- ===================================================================
-- §6.  The initial SLD-derivation node
-- ===================================================================

/-- Type-index reduction: `.init`'s natural output equals the concrete
    singleton `[reverse([a, b], R)]`. -/
theorem initNode_idx_eq :
    LCS.Finset.ofList queryGoal.bodyFOAtoms
      = LCS.Finset.ofList [reverse ⟦a, b⟧ R] := by
  simp [queryGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal, goal, atomSubst_id]

/-- The initial derivation `N_0 = ?- reverse([a, b], R)`. Built as a
    `▸` transport so cast-invariance simp lemmas can peel it. -/
noncomputable def initNode :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      (LCS.Finset.ofList [reverse ⟦a, b⟧ R]) :=
  initNode_idx_eq ▸
    FOSLDDerivation.init (D := fun c => c ∈ revProgram) (goals := [queryGoal])
      queryGoal (List.Mem.head _)

/-- Machine-checked: the initial node's current goal is the singleton
    `[reverse [a, b] R]`. This is the bodyAtoms of `queryGoal`, which
    by definition of `FOHornClause.goal` reduces to the body list. -/
example : (queryGoal.bodyFOAtoms (hNoEq := language_noEq)) = [reverse ⟦a, b⟧ R] :=
  -- BEGIN PROOF
  by simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

-- ===================================================================
-- §7.  The Prolog answer: R = [b, a]
-- ===================================================================

/-- The expected Prolog answer: `R = [b, a]`. -/
def revAnswerValue : Term revLang := ⟦b, a⟧

/-- Sanity: the answer is the reverse of the input list. -/
example : revAnswerValue = ⟦b, a⟧ := rfl

-- ===================================================================
-- §8.  The concrete 6-step SLD-refutation
--
-- Each step is built as a chained `FOSLDDerivation.step`.  The prior
-- goal's current-goal type index is a nested Finset expression
-- `(erase Ak).union (bodyAtoms.map rho).ofList .image (formulaSubstAll · sigma)`.
-- We add a `stepN_currentGoal` lemma per step to reduce that Finset
-- expression to a concrete `LCS.Finset.ofList [...]` literal, so
-- that subsequent steps' `hAk`/`hSep`/`hStdApart` proofs can
-- pattern-match on its free-variable set via
-- `clauseFV_neg_congr_of_mem_iff`.
-- ===================================================================

/-- **Step 1** — resolve `?- reverse([a,b], R)` against `clauseRevRec`.

    * ρ₁: H,T,R',Rt → V 8..V 11.
    * σ₁: V 8 ↦ a, V 9 ↦ ⟦b⟧, V 10 ↦ V 100.
    * New current goal: `[reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)]`. -/
noncomputable def revSLDStep1 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      ((((LCS.Finset.ofList [reverse ⟦a, b⟧ R]).erase (reverse ⟦a, b⟧ R)).union
        (LCS.Finset.ofList
          (clauseRevRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 4 ↦ V 8 | 5 ↦ V 9 | 6 ↦ V 10 | 7 ↦ V 11 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 8 ↦ a | 9 ↦ ⟦b⟧ | 10 ↦ V 100 ⟧)) :=
  FOSLDDerivation.step
    (prev := initNode)
    (clause := clauseRevRec)
    (hClause := by change _ ∈ revProgram; simp [revProgram])
    (hDef := by simp [clauseRevRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := reverse ⟦a, b⟧ R)
    (headA := reverse ⟦H | T⟧ R')
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by simp [clauseRevRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 4 ↦ V 8 | 5 ↦ V 9 | 6 ↦ V 10 | 7 ↦ V 11 ⟧)
    (sigma := ⟦ 8 ↦ a | 9 ↦ ⟦b⟧ | 10 ↦ V 100 ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the first recursive reverse step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- FV(queryGoal) = {100}; FV(clauseRevRec) ⊆ {4,5,6,7}.
      have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
          ((LCS.Finset.ofList [reverse ⟦a, b⟧ R]).toList.map FOLiteralCore.neg) =
          (clauseFV (L := revLang) (hNoEq := language_noEq))
            ([reverse ⟦a, b⟧ R].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x hx
        have hxmem := clauseRevRec_FV_subset x hx
        obtain ⟨hlo, hhi⟩ := hxmem
        match x, hlo, hhi with
        | 4, _, _ => exact ⟨8, rfl⟩
        | 5, _, _ => exact ⟨9, rfl⟩
        | 6, _, _ => exact ⟨10, rfl⟩
        | 7, _, _ => exact ⟨11, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy h
        have hxmem := clauseRevRec_FV_subset x hx
        have hymem := clauseRevRec_FV_subset y hy
        obtain ⟨hxlo, hxhi⟩ := hxmem
        obtain ⟨hylo, hyhi⟩ := hymem
        match x, hxlo, hxhi, y, hylo, hyhi with
        | 4, _, _, 4, _, _ => rfl
        | 4, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 4, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 4, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 5, _, _ => rfl
        | 5, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 6, _, _ => rfl
        | 6, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 7, _, _ => rfl
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          rw [queryGoal_FV_eq_100] at hPrev
          subst hPrev
          have hn100 : n = 100 :=
            (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
          subst hn100
          have hx₂mem := clauseRevRec_FV_subset x₂ hClause
          obtain ⟨hx₂lo, hx₂hi⟩ := hx₂mem
          match x₂, hx₂lo, hx₂hi with
          | 4, _, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 5, _, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 6, _, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 7, _, _ => simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | n
        · rfl
        · rfl
        · rfl
        · rfl
        · exfalso; exact hx clauseRevRec_FV_4
        · exfalso; exact hx clauseRevRec_FV_5
        · exfalso; exact hx clauseRevRec_FV_6
        · exfalso; exact hx clauseRevRec_FV_7
        · rfl)


/-- The `revSLDStep1` currentGoal Finset collapses to
    `{reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)}`. -/
theorem revSLDStep1_currentGoal :
    ((((LCS.Finset.ofList [reverse ⟦a, b⟧ R]).erase (reverse ⟦a, b⟧ R)).union
      (LCS.Finset.ofList
        (clauseRevRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 4 ↦ V 8 | 5 ↦ V 9 | 6 ↦ V 10 | 7 ↦ V 11 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 8 ↦ a | 9 ↦ ⟦b⟧ | 10 ↦ V 100 ⟧)) =
    LCS.Finset.ofList [reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)] := by
  -- BEGIN PROOF
  apply LCS.Finset.ext
  intro A
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [LCS.Finset.mem_union] at hB
    rcases hB with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨A', hA', rfl⟩ := himg
      simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      rcases hA' with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        left
        simp [formulaSubstAll_reverse, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, T, Rt, V, ovr, overrideSubst]
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        right
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, H, Rt, R', V, ovr, overrideSubst]
        rfl
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine ⟨reverse (V 9) (V 11), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; right
        rw [LCS.Finset.mem_ofList, List.mem_map]
        refine ⟨reverse T Rt, ?_, ?_⟩
        · simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
        · show _ = reverse (V 9) (V 11)
          simp [formulaSubstAll_reverse, T, Rt, V, ovr, overrideSubst]
          rfl
      · simp [formulaSubstAll_reverse, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, V, ovr, overrideSubst]
        rfl
    · refine ⟨append (V 11) ⟦V 8⟧ (V 10), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; right
        rw [LCS.Finset.mem_ofList, List.mem_map]
        refine ⟨append Rt ⟦H⟧ R', ?_, ?_⟩
        · simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
        · show _ = append (V 11) ⟦V 8⟧ (V 10)
          simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
                H, Rt, R', V, ovr, overrideSubst]
          rfl
      · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, V, ovr, overrideSubst]
        rfl


/-- Abbreviation: the current-goal Finset after step 1. -/
noncomputable abbrev step1Idx : LCS.Finset (FOAtom revLang language_noEq) :=
  ((((LCS.Finset.ofList [reverse ⟦a, b⟧ R]).erase (reverse ⟦a, b⟧ R)).union
    (LCS.Finset.ofList
      (clauseRevRec.bodyFOAtoms.map (fun A =>
        (A.subst (hNoEq := language_noEq)) ⟦ 4 ↦ V 8 | 5 ↦ V 9 | 6 ↦ V 10 | 7 ↦ V 11 ⟧)))
    ).image (fun A => (A.subst (hNoEq := language_noEq))
      ⟦ 8 ↦ a | 9 ↦ ⟦b⟧ | 10 ↦ V 100 ⟧))

theorem step1Idx_eq :
    step1Idx = LCS.Finset.ofList [reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)] :=
  revSLDStep1_currentGoal

/-- **Step 2** — resolve `reverse ⟦b⟧ (V 11)` against `clauseRevRec`.

    * ρ₂: H,T,R',Rt → V 12..V 15.
    * σ₂: V 12 ↦ b, V 13 ↦ nil, V 14 ↦ V 11.
    * New current goal: `[reverse nil (V 15), append (V 15) ⟦b⟧ (V 11),
      append (V 11) ⟦a⟧ (V 100)]`. -/
noncomputable def revSLDStep2 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      (((step1Idx.erase (reverse ⟦b⟧ (V 11))).union
        (LCS.Finset.ofList
          (clauseRevRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 4 ↦ V 12 | 5 ↦ V 13 | 6 ↦ V 14 | 7 ↦ V 15 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 12 ↦ b | 13 ↦ nil | 14 ↦ V 11 ⟧)) :=
  FOSLDDerivation.step
    (prev := revSLDStep1)
    (clause := clauseRevRec)
    (hClause := by change _ ∈ revProgram; simp [revProgram])
    (hDef := by simp [clauseRevRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := reverse ⟦b⟧ (V 11))
    (headA := reverse ⟦H | T⟧ R')
    (hAk := by
      show reverse ⟦b⟧ (V 11) ∈ step1Idx
      rw [step1Idx_eq, LCS.Finset.mem_ofList]; simp)
    (hHead := by simp [clauseRevRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 4 ↦ V 12 | 5 ↦ V 13 | 6 ↦ V 14 | 7 ↦ V 15 ⟧)
    (sigma := ⟦ 12 ↦ b | 13 ↦ nil | 14 ↦ V 11 ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the second recursive reverse step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- prevGoal = step1Idx reduces to {reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)}
      -- FV ⊆ {11, 100}; FV(clauseRevRec) ⊆ {4,5,6,7}
      have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
          (step1Idx.toList.map FOLiteralCore.neg) =
          (clauseFV (L := revLang) (hNoEq := language_noEq))
            ([reverse ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList]
        show f ∈ step1Idx ↔ _
        rw [step1Idx_eq, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x hx
        have hxmem := clauseRevRec_FV_subset x hx
        obtain ⟨hlo, hhi⟩ := hxmem
        match x, hlo, hhi with
        | 4, _, _ => exact ⟨12, rfl⟩
        | 5, _, _ => exact ⟨13, rfl⟩
        | 6, _, _ => exact ⟨14, rfl⟩
        | 7, _, _ => exact ⟨15, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy h
        have hxmem := clauseRevRec_FV_subset x hx
        have hymem := clauseRevRec_FV_subset y hy
        obtain ⟨hxlo, hxhi⟩ := hxmem
        obtain ⟨hylo, hyhi⟩ := hymem
        match x, hxlo, hxhi, y, hylo, hyhi with
        | 4, _, _, 4, _, _ => rfl
        | 4, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 4, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 4, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 5, _, _ => rfl
        | 5, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 5, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 6, _, _, 6, _, _ => rfl
        | 6, _, _, 7, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 4, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 5, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 6, _, _ => simp [V, ovr, overrideSubst] at h
        | 7, _, _, 7, _, _ => rfl
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          have hx₁ : x₁ = 11 ∨ x₁ = 100 := by
            obtain ⟨lit, hMem, hV⟩ := hPrev
            simp at hMem
            rcases hMem with rfl | rfl
            · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_reverse,
                         termVars_cons, termVars_b_iff, termVars_nil_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              exact Or.inl hV
            · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_a_iff, termVars_nil_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              rcases hV with h | h
              · exact Or.inl h
              · exact Or.inr h
          have hx₂mem := clauseRevRec_FV_subset x₂ hClause
          obtain ⟨hx₂lo, hx₂hi⟩ := hx₂mem
          rcases hx₁ with rfl | rfl
          · have hn : n = 11 :=
              (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
            subst hn
            match x₂, hx₂lo, hx₂hi with
            | 4, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 5, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 6, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 7, _, _ => simp [V, ovr, overrideSubst] at hEq₂
          · have hn : n = 100 :=
              (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
            subst hn
            match x₂, hx₂lo, hx₂hi with
            | 4, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 5, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 6, _, _ => simp [V, ovr, overrideSubst] at hEq₂
            | 7, _, _ => simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
        · rfl
        · rfl
        · rfl
        · rfl
        · exfalso; exact hx clauseRevRec_FV_4
        · exfalso; exact hx clauseRevRec_FV_5
        · exfalso; exact hx clauseRevRec_FV_6
        · exfalso; exact hx clauseRevRec_FV_7
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl)


/-- Abbreviation: the current-goal Finset after step 2. -/
noncomputable abbrev step2Idx : LCS.Finset (FOAtom revLang language_noEq) :=
  (((step1Idx.erase (reverse ⟦b⟧ (V 11))).union
    (LCS.Finset.ofList
      (clauseRevRec.bodyFOAtoms.map (fun A =>
        (A.subst (hNoEq := language_noEq)) ⟦ 4 ↦ V 12 | 5 ↦ V 13 | 6 ↦ V 14 | 7 ↦ V 15 ⟧)))
    ).image (fun A => (A.subst (hNoEq := language_noEq))
      ⟦ 12 ↦ b | 13 ↦ nil | 14 ↦ V 11 ⟧))

end LCS.Examples.PrologReverse
end

