import LCS.Item
import LCS.Util
import LCS.FirstOrder.SemanticsN
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Soundness
import LCS.SLD.FirstOrder
import LCS.SLD.PrologSyntax
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness

set_option linter.unusedSimpArgs false

/-! # Examples.PrologMember — verified Prolog `member/2`

    A classic Prolog demonstration: list membership with two rules
    (one per case: head-match vs tail-recurse).  The program shows
    off Prolog's core strength — **alternative matching clauses**
    (non-determinism / implicit disjunction) — which in our
    SLD-resolution formalism corresponds to *two* different input
    clauses at `hClause`.

    ```prolog
    % Program:
    member(X, [X | _]).                        % base case
    member(X, [_ | Ys]) :- member(X, Ys).      % recursive case

    % Query:
    ?- member(b, [a, b, c]).

    % Expected answer:
    yes.  (i.e. the query succeeds; there is an SLD-refutation.)
    ```

    The interesting feature here vs `PrologAppend`:
    * The program has a **recursive rule** AND a **base fact that
      shares its head predicate with the rule's head**.  A Prolog
      system can try either at each step, and the SLD-refutation
      picks the correct branch (tail-recurse once, then match head).
    * The query has a **ground answer** (no output variable), so the
      semantic payload is a satisfiability/truth claim, not a
      witness-extraction claim.

    The concrete 2-step SLD-derivation is built as a direct chain of
    `FOSLDDerivation.init` / `FOSLDDerivation.step` applications at
    the indexed type. Constructor side conditions (hSep, hStdApart, hAk) use helper lemmas of
    §2b / §3b — the `formulaSubstAll_*`, `termSubstAll_*`,
    `formulaVars_member`, `termVars_cons`, `clauseRec_FV_*`,
    `clauseBase_FV_*`, and `queryGoal_FV_empty` family. The final
    `memberQuery_semanticallyValid` cites Lemma 9.5.3 to lift the
    syntactic refutation to semantic unsatisfiability of the
    substituted clause set. -/

noncomputable section
namespace LCS.Examples.PrologMember

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

-- ===================================================================
-- §1.  The language L_member = { constants a, b, c, []; function ./2;
--                                predicate member/2 }
-- ===================================================================

/-- Constants of `L_member`: three list elements `a`, `b`, `c`, and
    the empty list `[]` (spelled `nilC` to avoid clashing with the
    term-level `nil` below). -/
inductive MemberConst : Type where
  | a    : MemberConst
  | b    : MemberConst
  | c    : MemberConst
  | nilC : MemberConst
  deriving DecidableEq, Repr

/-- Functions of `L_member`: cons (./2). -/
inductive MemberFunc : Type where
  | cons : MemberFunc
  deriving DecidableEq, Repr

/-- Predicates of `L_member`: member/2. -/
inductive MemberPred : Type where
  | member : MemberPred
  deriving DecidableEq, Repr

/-- The first-order language for the `member` demo. -/
def memberLang : Language where
  funSymbols   := MemberFunc
  funArity     := fun | .cons => 2
  constSymbols := MemberConst
  predSymbols  := MemberPred
  predArity    := fun | .member => 2
  hasEquality  := false

/-- The example language contains predicate atoms only. -/
theorem language_noEq : memberLang.withoutEquality := rfl

-- ===================================================================
-- §2.  Prolog-style term constructors, variables, and smart atoms
-- ===================================================================

/-- Prolog empty list `[]`. -/
def nil : Term memberLang := Term.const MemberConst.nilC

/-- Prolog constants `a`, `b`, `c`. -/
def a : Term memberLang := Term.const MemberConst.a
def b : Term memberLang := Term.const MemberConst.b
def c : Term memberLang := Term.const MemberConst.c

/-- Prolog cons: `[H | T]` is `cons H T`. -/
def cons (h t : Term memberLang) : Term memberLang :=
  Term.func MemberFunc.cons (pFin2 h t)

/-- Prolog list-literal notation (restricted to what we need here). -/
notation "⟦" "⟧"                   => nil
notation "⟦" x "⟧"                 => cons x nil
notation "⟦" x ", " y "⟧"          => cons x (cons y nil)
notation "⟦" x ", " y ", " z "⟧"   => cons x (cons y (cons z nil))
notation "⟦" h " | " t "⟧"         => cons h t

/-- Prolog atom `member(X, L)`. -/
def member (x l : Term memberLang) : FOAtom memberLang language_noEq :=
  FOAtomCore.predN (L := memberLang) MemberPred.member (pFin2 x l)

/-- Prolog-style call syntax: `member(x, l)`. -/
scoped notation:max "member(" x ", " l ")" => member x l

-- Prolog-style variable aliases.  By convention, identifiers
-- starting with a capital letter are logic variables.  Indices
-- 0..1 are used by the base fact; 2..3 by the recursive rule.
abbrev X  : Term memberLang := V 0   -- (shared)
abbrev Any : Term memberLang := V 1  -- wildcard "_" in the base fact
abbrev Anyhead : Term memberLang := V 2  -- wildcard head in recursive rule
abbrev Ys : Term memberLang := V 3   -- tail in recursive rule

-- ===================================================================
-- §2b.  Substitution and variable helpers for `member/2`
-- ===================================================================

/-- Push structural atom substitution through `member x l`. -/
theorem formulaSubstAll_member (x l : Term memberLang)
    (σ : Nat → Term memberLang) :
    (member x l).subst (hNoEq := language_noEq) σ =
      member (LCS.FOResolution.Unification.termSubstAll x σ)
             (LCS.FOResolution.Unification.termSubstAll l σ) := by
  -- BEGIN PROOF
  unfold member FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := memberLang) MemberPred.member
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin2 x l i) σ) =
    FOAtomCore.predN (L := memberLang) MemberPred.member
      (pFin2
        (LCS.FOResolution.Unification.termSubstAll x σ)
        (LCS.FOResolution.Unification.termSubstAll l σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Push `termSubstAll σ` through `cons h t`. -/
theorem termSubstAll_cons (h t : Term memberLang) (σ : Nat → Term memberLang) :
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

theorem termSubstAll_nil (σ : Nat → Term memberLang) :
    LCS.FOResolution.Unification.termSubstAll nil σ = nil := rfl
theorem termSubstAll_a (σ : Nat → Term memberLang) :
    LCS.FOResolution.Unification.termSubstAll a σ = a := rfl
theorem termSubstAll_b (σ : Nat → Term memberLang) :
    LCS.FOResolution.Unification.termSubstAll b σ = b := rfl
theorem termSubstAll_c (σ : Nat → Term memberLang) :
    LCS.FOResolution.Unification.termSubstAll c σ = c := rfl

/-- FV of `member x l` = FV(x) ∪ FV(l). -/
theorem formulaVars_member (x l : Term memberLang) (n : Nat) :
    (member x l).vars n ↔ termVars x n ∨ termVars l n := by
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

/-- FV of `cons h t` = FV(h) ∪ FV(t). -/
theorem termVars_cons (h t : Term memberLang) (n : Nat) :
    termVars (cons h t) n ↔ termVars h n ∨ termVars t n := by
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

theorem termVars_V (n x : Nat) : termVars (L := memberLang) (V n) x ↔ x = n := Iff.rfl
theorem termVars_a_iff (x : Nat) : termVars a x ↔ False := Iff.rfl
theorem termVars_b_iff (x : Nat) : termVars b x ↔ False := Iff.rfl
theorem termVars_c_iff (x : Nat) : termVars c x ↔ False := Iff.rfl
theorem termVars_nil_iff (x : Nat) : termVars nil x ↔ False := Iff.rfl

-- ===================================================================
-- §3.  The `member/2` program + query, in Prolog syntax
-- ===================================================================

/--
    ```prolog
    member(X, [X | _]).
    ```
    Base case: if `X` is the head, we've found it.
    Variables: `X = V 0`, `_ = V 1`. -/
def clauseBase : FOHornClause memberLang language_noEq :=
  (fact (hNoEq := language_noEq)) member(X, ⟦X | Any⟧)

/--
    ```prolog
    member(X, [_ | Ys]) :- member(X, Ys).
    ```
    Recursive case: skip the head, look in the tail.
    Variables: `X = V 0` (shared with base), `_ = V 2`, `Ys = V 3`. -/
def clauseRec : FOHornClause memberLang language_noEq :=
  member(X, ⟦Anyhead | Ys⟧) :- member(X, Ys)

/-- The full logic program: `{ base, recursive }`. -/
def memberProgram : List (FOHornClause memberLang language_noEq) :=
  [ clauseBase, clauseRec ]

/--
    ```prolog
    ?- member(b, [a, b, c]).
    ```
    Query: is `b` a member of the list `[a, b, c]` ?
    This is a **ground** query (no output variable), so the answer
    is just "yes, there is a refutation." -/
def queryGoal : FOHornClause memberLang language_noEq :=
  (?- member(b, ⟦a, b, c⟧)).toGoal

-- ===================================================================
-- §3b.  FV-enumeration lemmas
-- ===================================================================

/-- `clauseFV clauseRec.toFOClause` ⊆ {0, 2, 3} — the rule's
    free variables are X (V 0), Anyhead (V 2), Ys (V 3). -/
theorem clauseRec_FV_subset (x : Nat) :
    (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) x →
    x = 0 ∨ x = 2 ∨ x = 3 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  rcases hMem with rfl | rfl
  · -- .neg (member X Ys)
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
               X, Ys, termVars_V] at hV
    omega
  · -- .pos (member X ⟦Anyhead | Ys⟧)
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
               termVars_cons, X, Anyhead, Ys, termVars_V] at hV
    omega

/-- `clauseFV clauseBase.toFOClause` ⊆ {0, 1} — the base fact's
    free variables are X (V 0) and Any (V 1). -/
theorem clauseBase_FV_subset (x : Nat) :
    (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseBase.toFOClause (hNoEq := language_noEq)) x →
    x = 0 ∨ x = 1 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  subst hMem
  simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
             termVars_cons, X, Any, termVars_V] at hV
  omega

/-- The query is ground: `clauseFV queryGoal` is empty. -/
theorem queryGoal_FV_empty (x : Nat) :
    ¬ (clauseFV (L := memberLang) (hNoEq := language_noEq))
        ([member b ⟦a, b, c⟧].map FOLiteralCore.neg) x := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp at hMem
  subst hMem
  simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
             termVars_cons, termVars_a_iff, termVars_b_iff,
             termVars_c_iff, termVars_nil_iff, termVars_V,
             or_self, or_false, false_or] at hV

/-- `0 ∈ clauseFV clauseRec` — X appears in the head. -/
theorem clauseRec_FV_0 : (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (member X ⟦Anyhead | Ys⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (member X ⟦Anyhead | Ys⟧) 0
    rw [formulaVars_member]; left; rfl

/-- `2 ∈ clauseFV clauseRec` — Anyhead appears in the head. -/
theorem clauseRec_FV_2 : (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (member X ⟦Anyhead | Ys⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (member X ⟦Anyhead | Ys⟧) 2
    rw [formulaVars_member]; right; rw [termVars_cons]; left; rfl

/-- `3 ∈ clauseFV clauseRec` — Ys appears in the head. -/
theorem clauseRec_FV_3 : (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 3 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (member X ⟦Anyhead | Ys⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (member X ⟦Anyhead | Ys⟧) 3
    rw [formulaVars_member]; right; rw [termVars_cons]; right; rfl

/-- `0 ∈ clauseFV clauseBase` — X appears in the head. -/
theorem clauseBase_FV_0 : (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseBase.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (member X ⟦X | Any⟧), ?_, ?_⟩
  · simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (member X ⟦X | Any⟧) 0
    rw [formulaVars_member]; left; rfl

/-- `1 ∈ clauseFV clauseBase` — Any appears in the tail. -/
theorem clauseBase_FV_1 : (clauseFV (L := memberLang) (hNoEq := language_noEq)) (clauseBase.toFOClause (hNoEq := language_noEq)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (member X ⟦X | Any⟧), ?_, ?_⟩
  · simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (member X ⟦X | Any⟧) 1
    rw [formulaVars_member]; right; rw [termVars_cons]; right; rfl

-- ===================================================================
-- §4.  Concrete two-step SLD-derivation
--
-- The refutation proceeds by:
--   N₀ = ?- member(b, [a, b, c])
--       apply the recursive rule (skip head 'a'):
--   N₁ = ?- member(b, [b, c])
--       apply the base fact (head 'b' matches target 'b'):
--   N₂ = ∅   (empty Finset — refutation)
-- ===================================================================

/-- Type-index reduction: `.init`'s natural output equals the concrete
    singleton `[member(b, [a, b, c])]`. -/
theorem memberSLDStep0_idx_eq :
    LCS.Finset.ofList queryGoal.bodyFOAtoms
      = LCS.Finset.ofList [member b ⟦a, b, c⟧] := by
  simp [queryGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal, goal, atomSubst_id]

/-- Initial derivation node `N_0 = ?- member(b, [a, b, c])`. Built as
    a `▸` transport (not `simp only ... at ...; exact`) so cast-invariance
    simp lemmas can peel it cleanly. -/
noncomputable def memberSLDStep0 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ memberProgram) [queryGoal]
      (LCS.Finset.ofList [member b ⟦a, b, c⟧]) :=
  memberSLDStep0_idx_eq ▸
    FOSLDDerivation.init (D := fun c => c ∈ memberProgram) (goals := [queryGoal])
      queryGoal (List.Mem.head _)

/-- **Step 1** — resolve the initial goal `?- member(b, [a, b, c])`
    with the recursive clause `clauseRec`.

    * ρ₁ renames the rule's three variables apart to fresh names 4..6
      (X → V 4, _ → V 5, Ys → V 6).
    * σ₁ unifies the goal atom `member(b, [a, b, c])` with the
      renamed rule head `member(V 4, [V 5 | V 6])`: so
      V 4 ↦ b, V 5 ↦ a, V 6 ↦ [b, c].
    * The resolvent adds the instantiated rule body
      `member(b, [b, c])`. -/
noncomputable def memberSLDStep1 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ memberProgram) [queryGoal]
      ((((LCS.Finset.ofList [member b ⟦a, b, c⟧]).erase (member b ⟦a, b, c⟧)).union
        (LCS.Finset.ofList
          (clauseRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 2 ↦ V 5 | 3 ↦ V 6 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 4 ↦ b | 5 ↦ a | 6 ↦ ⟦b, c⟧ ⟧)) :=
  FOSLDDerivation.step
    (prev := memberSLDStep0)
    (clause := clauseRec)
    (hClause := by change _ ∈ memberProgram; simp [memberProgram])
    (hDef := by simp [clauseRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := member b ⟦a, b, c⟧)
    (headA := member X ⟦Anyhead | Ys⟧)
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by simp [clauseRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 4 | 2 ↦ V 5 | 3 ↦ V 6 ⟧)
    (sigma := ⟦ 4 ↦ b | 5 ↦ a | 6 ↦ ⟦b, c⟧ ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the recursive member step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- Bridge prev Finset to list form via clauseFV congruence.
      have hCongr : (clauseFV (L := memberLang) (hNoEq := language_noEq))
          ((LCS.Finset.ofList [member b ⟦a, b, c⟧]).toList.map FOLiteralCore.neg) =
          (clauseFV (L := memberLang) (hNoEq := language_noEq)) ([member b ⟦a, b, c⟧].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _
        rcases x with _ | _ | _ | _ | n
        · exact ⟨4, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨n + 4, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy h
        have hxmem := clauseRec_FV_subset x hx
        have hymem := clauseRec_FV_subset y hy
        rcases hxmem with rfl | rfl | rfl <;>
          rcases hymem with rfl | rfl | rfl <;>
            first | rfl | simp [V, ovr, overrideSubst] at h
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, _⟩, _⟩
          -- prev reduces to [member b ⟦a,b,c⟧], FV = ∅ (ground)
          obtain ⟨lit, hMem, hV⟩ := hPrev
          simp at hMem
          subst hMem
          simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
                     termVars_cons, termVars_b_iff, termVars_a_iff,
                     termVars_c_iff, termVars_nil_iff,
                     or_self, or_false, false_or] at hV
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | _ | n
        · exfalso; exact hx clauseRec_FV_0
        · rfl
        · exfalso; exact hx clauseRec_FV_2
        · exfalso; exact hx clauseRec_FV_3
        · rfl)


/-- `memberSLDStep1`'s currentGoal Finset collapses to the singleton
    `{member b [b, c]}`. -/
theorem memberSLDStep1_currentGoal :
    ((((LCS.Finset.ofList [member b ⟦a, b, c⟧]).erase (member b ⟦a, b, c⟧)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 2 ↦ V 5 | 3 ↦ V 6 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ b | 5 ↦ a | 6 ↦ ⟦b, c⟧ ⟧)) =
    LCS.Finset.ofList [member b ⟦b, c⟧] := by
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
      simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      subst hA'
      simp [formulaSubstAll_member, termSubstAll_cons, termSubstAll_nil,
            termSubstAll_a, termSubstAll_b, termSubstAll_c,
            V, ovr, overrideSubst]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨member (V 4) (V 6), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨member X Ys, ?_, ?_⟩
      · simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · show _ = member (V 4) (V 6)
        simp [formulaSubstAll_member, X, Ys, V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_member, termSubstAll_cons, termSubstAll_b,
            termSubstAll_a, termSubstAll_c, V, ovr, overrideSubst]
      rfl

/-- **Step 2** (closing step) — resolve the intermediate goal
    `?- member(b, [b, c])` with the **base fact** `clauseBase`:
    `member(X, [X | _]).`. The head literally matches once we set
    `X ↦ b`, so this step closes the derivation.

    * ρ₂ renames rule-side vars 0, 1 to fresh 7, 8 (X → V 7, _ → V 8).
    * σ₂ unifies `member(b, [b, c])` with `member(V 7, [V 7 | V 8])`:
      V 7 ↦ b, V 8 ↦ [c].
    * Because `clauseBase` is a fact (empty body), the new current
      goal is `∅.image σ₂ = ∅` — an SLD-refutation. -/
noncomputable def memberSLDRefutation :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ memberProgram) [queryGoal] (∅ : LCS.Finset (FOAtom memberLang language_noEq)) := by
  let step1Idx : LCS.Finset (FOAtom memberLang language_noEq) :=
    ((((LCS.Finset.ofList [member b ⟦a, b, c⟧]).erase (member b ⟦a, b, c⟧)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 2 ↦ V 5 | 3 ↦ V 6 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ b | 5 ↦ a | 6 ↦ ⟦b, c⟧ ⟧))
  have step2raw :
      (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ memberProgram) [queryGoal]
        (((step1Idx.erase (member b ⟦b, c⟧)).union
          (LCS.Finset.ofList
            (clauseBase.bodyFOAtoms.map (fun A =>
              (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 ⟧)))
          ).image (fun A => (A.subst (hNoEq := language_noEq))
            ⟦ 7 ↦ b | 8 ↦ ⟦c⟧ ⟧)) :=
    FOSLDDerivation.step
      (prev := memberSLDStep1)
      (clause := clauseBase)
      (hClause := by change _ ∈ memberProgram; simp [memberProgram])
      (hDef := by simp [clauseBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := member b ⟦b, c⟧)
      (headA := member X ⟦X | Any⟧)
      (hAk := by
        rw [memberSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by simp [clauseBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := ⟦ 0 ↦ V 7 | 1 ↦ V 8 ⟧)
      (sigma := ⟦ 7 ↦ b | 8 ↦ ⟦c⟧ ⟧)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the base member step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        have hCongr : (clauseFV (L := memberLang) (hNoEq := language_noEq))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := memberLang) (hNoEq := language_noEq)) ([member b ⟦b, c⟧].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList [member b ⟦b, c⟧] from
              memberSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | _ | n
          · exact ⟨7, rfl⟩
          · exact ⟨8, rfl⟩
          · exact ⟨n + 2, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy h
          have hxmem := clauseBase_FV_subset x hx
          have hymem := clauseBase_FV_subset y hy
          rcases hxmem with rfl | rfl <;>
            rcases hymem with rfl | rfl <;>
              first | rfl | simp [V, ovr, overrideSubst] at h
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, _⟩, _⟩
            obtain ⟨lit, hMem, hV⟩ := hPrev
            simp at hMem
            subst hMem
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_member,
                       termVars_cons, termVars_b_iff, termVars_c_iff,
                       termVars_nil_iff,
                       or_self, or_false, false_or] at hV
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | _ | n
          · exfalso; exact hx clauseBase_FV_0
          · exfalso; exact hx clauseBase_FV_1
          · rfl)

  have hIdx :
      (((step1Idx.erase (member b ⟦b, c⟧)).union
        (LCS.Finset.ofList
          (clauseBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 7 ↦ b | 8 ↦ ⟦c⟧ ⟧)) =
      (∅ : LCS.Finset (FOAtom memberLang language_noEq)) := by
    apply LCS.Finset.ext
    intro A
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨B, hB, _⟩
      rw [LCS.Finset.mem_union] at hB
      rcases hB with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step1Idx = LCS.Finset.ofList [member b ⟦b, c⟧] from
                memberSLDStep1_currentGoal,
            LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [clauseBase, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  exact hIdx ▸ step2raw

/-- `isRefutation memberSLDRefutation` — by definition, since the
    derivation's type index is `∅`. -/
theorem memberSLDRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) memberSLDRefutation :=
  -- BEGIN PROOF
  rfl

-- ===================================================================
-- §5.  Semantic payload — the query is valid in every model of the
--      program
-- ===================================================================

/-- A placeholder falsum formula over `memberLang`.  Any ground atom
    works; its only role is to stand in for `⊥` in `clauseToFormula`. -/
def memberFalsum : FormulaN memberLang :=
  (member nil nil).toFormula

/-- Every clause in `memberProgram ++ [queryGoal]` has only
    quantifier-free atoms. -/
theorem memberAllQF :
    ∀ c ∈ memberProgram ++ [queryGoal], (FOHornClause.allAtomsQF (hNoEq := language_noEq)) c := by
  intro c _
  exact (FOHornClause.allAtomsQF_derived (hNoEq := language_noEq)) c

/-- **Showcase theorem** — the Prolog-level claim, stated with
    program and query inlined as Prolog syntax.

    Given the program
    ```prolog
    member(X, [X | _]).
    member(X, [_ | Ys]) :- member(X, Ys).
    ```
    and the **ground** query
    ```prolog
    ?- member(b, [a, b, c]).
    ```
    there exists an SLD-refutation. Since the query has no output
    variable, the Prolog answer is simply `yes`. This is witnessed
    semantically (Theorem 9.5.1 corollary): every first-order
    structure that models the program satisfies `member(b, [a, b, c])`
    at every assignment. -/
example :
    -- Program:  member(X, [X|_]).  member(X, [_|Ys]) :- member(X, Ys).
    let program : List (FOHornClause memberLang language_noEq) :=
      [ (fact (hNoEq := language_noEq)) member(X, ⟦X | Any⟧),
        (member(X, ⟦Anyhead | Ys⟧) :- member(X, Ys)) ]
    -- Query:  ?- member(b, [a, b, c]).
    let query : FOHornClause memberLang language_noEq :=
      (?- member(b, ⟦a, b, c⟧)).toGoal
    -- Answer:  yes (ground query — no output variable).
    ∃ R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ program) [query] ∅,
      -- (1) Prolog answer "yes":  R is an SLD-refutation (ends in □).
      (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) R ∧
      -- (2) Semantic entailment:  ∀ M ⊨ program, M ⊨ member(b, [a, b, c]).
      (∀ (M : Structure memberLang),
        (∀ c ∈ program,
          ∀ (s : Assignment M),
            formulaEvalN M ((clauseToFormula (hNoEq := language_noEq)) memberFalsum (c.toFOClause (hNoEq := language_noEq))) s) →
        ∀ (s : Assignment M),
          formulaEvalN M (member(b, ⟦a, b, c⟧)).toFormula s) := by
  refine ⟨memberSLDRefutation, memberSLDRefutation_isRefutation, ?_⟩
  intro M hProgSat s
  have hInitVar : substitutedClauseSet.getInitSigma language_noEq memberSLDRefutation = Term.var := by
    exact getInitSigma_eq_id language_noEq memberSLDRefutation
  have h := (sldAnswer_entails (Afalsum := memberFalsum) (hNoEq := language_noEq)) (P := memberProgram)
    (queryAtom := member(b, ⟦a, b, c⟧)) (R := memberSLDRefutation)
    (hRef := memberSLDRefutation_isRefutation)
    (hInitVar := hInitVar)
    M hProgSat s
  -- Query is ground: `formulaSubstAll` on member(b, ⟦a,b,c⟧) is identity.
  rw [← atomSubst_toFormula_formulaSubstAll] at h
  simp only [formulaSubstAll_member, termSubstAll_cons, termSubstAll_nil,
             termSubstAll_a, termSubstAll_b, termSubstAll_c] at h
  exact h

-- ===================================================================
-- Sanity-check smoke tests (pure Lean, no sorry)
-- ===================================================================

/-- Program size is 2 clauses — one fact + one rule. -/
example : memberProgram.length = 2 := rfl

/-- Query is a single-atom goal. -/
example : queryGoal.bodyFOAtoms.length = 1 := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

/-- The goal atom is literally `member(b, [a, b, c])`. -/
example : queryGoal.bodyFOAtoms.head? = some (member b ⟦a, b, c⟧) := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

end LCS.Examples.PrologMember

end
