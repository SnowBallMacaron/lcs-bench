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

/-! # Examples.PrologAppend — end-to-end verified Prolog `append`

    A single-file demonstration of the proposal's **Verified Logic
    Programming** deliverable, written in Prolog-flavoured syntax so
    that anyone who has seen Prolog can read the program directly.

    ```prolog
    % Program:
    append([],       L, L).
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).

    % Query:
    ?- append([a], [b], Z).

    % Expected answer:
    Z = [a, b].
    ```

    The program, query, and full concrete two-step SLD-refutation
    are given at the indexed `FOSLDDerivation` type. All constructor
    side conditions (hMGU, hSep, hAk) are discharged via
    helper lemmas that push substitutions through `append`/`cons`
    and enumerate `clauseFV` for the program clauses. The final
    `appendQuery_has_answer` bundles (1) the syntactic Prolog answer
    `Z = [a, b]` (via `appendAnswer_eq`) with (2) the semantic
    entailment `∀ M ⊨ program, M ⊨ append([a], [b], [a, b])` (via
    `sldAnswer_entails`, the single-atom corollary of Theorem 9.5.1). -/

noncomputable section
namespace LCS.Examples.PrologAppend

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
-- §1.  The language L_append = { constants a, b, []; function ./2;
--                                predicate append/3 }
-- ===================================================================

/-- Constants of `L_append`: the two list elements `a`, `b`, and the
    empty list `[]` (spelled `nilC` here to avoid clashing with the
    term-level `nil` below). -/
inductive AppendConst : Type where
  | a   : AppendConst
  | b   : AppendConst
  | nilC : AppendConst
  deriving DecidableEq, Repr

/-- Functions of `L_append`: just cons (./2 in Prolog). -/
inductive AppendFunc : Type where
  | cons : AppendFunc
  deriving DecidableEq, Repr

/-- Predicates of `L_append`: just `append/3`. -/
inductive AppendPred : Type where
  | append : AppendPred
  deriving DecidableEq, Repr

/-- The first-order language for the `append` demo. -/
def appendLang : Language where
  funSymbols   := AppendFunc
  funArity     := fun | .cons => 2
  constSymbols := AppendConst
  predSymbols  := AppendPred
  predArity    := fun | .append => 3
  hasEquality  := false

/-- The example language contains predicate atoms only. -/
theorem language_noEq : appendLang.withoutEquality := rfl

-- ===================================================================
-- §2.  Prolog-style smart constructors
--
-- After this block a reader can write, for instance,
--     `append ⟦a⟧ ⟦b⟧ Z`
-- and it reads exactly like the corresponding Prolog atom.
-- ===================================================================

/-- Prolog empty list `[]`. -/
def nil : Term appendLang := Term.const AppendConst.nilC

/-- Prolog constant `a`. -/
def a : Term appendLang := Term.const AppendConst.a

/-- Prolog constant `b`. -/
def b : Term appendLang := Term.const AppendConst.b

/-- Prolog cons: `[H | T]` is `cons H T`. -/
def cons (h t : Term appendLang) : Term appendLang :=
  Term.func AppendFunc.cons (pFin2 h t)

/-- Prolog list-literal notation.
    * `⟦⟧`            ⇒ `[]`
    * `⟦x⟧`           ⇒ `[x]`
    * `⟦x, y⟧`        ⇒ `[x, y]`
    * `⟦h , ... | t⟧` ⇒ `[h , ... | t]` -/
notation "⟦" "⟧"                  => nil
notation "⟦" x "⟧"                => cons x nil
notation "⟦" x ", " y "⟧"         => cons x (cons y nil)
notation "⟦" x ", " y ", " z "⟧"  => cons x (cons y (cons z nil))
notation "⟦" h " | " t "⟧"        => cons h t

/-- Prolog atom `append(L1, L2, L3)`. -/
def append (l1 l2 l3 : Term appendLang) : FOAtom appendLang language_noEq :=
  FOAtomCore.predN (L := appendLang) AppendPred.append (pFin3 l1 l2 l3)

/-- Prolog-style call syntax: `append(l1, l2, l3)`. -/
scoped notation:max "append(" l1 ", " l2 ", " l3 ")" => append l1 l2 l3

-- Prolog-style variable aliases. By Prolog convention, identifiers
-- starting with a capital letter are logic variables. The indices
-- 0..3 are used by the recursive clause; 10 is the query output.
abbrev X  : Term appendLang := V 0
abbrev Xs : Term appendLang := V 1
abbrev Y  : Term appendLang := V 2
abbrev Zs : Term appendLang := V 3
/-- Query-output variable `Z` — the one Prolog will bind for us. -/
abbrev Z  : Term appendLang := V 10

-- ===================================================================
-- §2b.  Substitution helpers for the `append/3` smart constructors
--
-- `formulaSubstAll` and `termSubstAll` don't reduce definitionally
-- through the Fin-indexed `pFin3`/`pFin2` arguments. These helper
-- lemmas push the substitution through `append`, `cons`, `nil`,
-- `a`, `b` at the surface-syntax level, yielding forms where the
-- substitution only touches `Term.var` at the leaves — allowing
-- subsequent goals to close by `rfl`.
-- ===================================================================

/-- Push structural atom substitution through `append l1 l2 l3`. -/
theorem formulaSubstAll_append (l1 l2 l3 : Term appendLang)
    (σ : Nat → Term appendLang) :
    (append l1 l2 l3).subst (hNoEq := language_noEq) σ =
      append (LCS.FOResolution.Unification.termSubstAll l1 σ)
             (LCS.FOResolution.Unification.termSubstAll l2 σ)
             (LCS.FOResolution.Unification.termSubstAll l3 σ) := by
  -- BEGIN PROOF
  unfold append FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := appendLang) AppendPred.append
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin3 l1 l2 l3 i) σ) =
    FOAtomCore.predN (L := appendLang) AppendPred.append
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

/-- Push `termSubstAll σ` through `cons h t`. -/
theorem termSubstAll_cons (h t : Term appendLang) (σ : Nat → Term appendLang) :
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
theorem termSubstAll_nil (σ : Nat → Term appendLang) :
    LCS.FOResolution.Unification.termSubstAll nil σ = nil := rfl

/-- `termSubstAll σ a = a`. -/
theorem termSubstAll_a (σ : Nat → Term appendLang) :
    LCS.FOResolution.Unification.termSubstAll a σ = a := rfl

/-- `termSubstAll σ b = b`. -/
theorem termSubstAll_b (σ : Nat → Term appendLang) :
    LCS.FOResolution.Unification.termSubstAll b σ = b := rfl

/-- FV of `append l1 l2 l3` is the union of FVs of `l1`, `l2`, `l3`. -/
theorem formulaVars_append (l1 l2 l3 : Term appendLang) (x : Nat) :
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

/-- FV of `cons h t` is the union of FVs of `h` and `t`. -/
theorem termVars_cons (h t : Term appendLang) (x : Nat) :
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

/-- Variable-set characterisations of the individual smart constructors. -/
theorem termVars_V (n x : Nat) : termVars (L := appendLang) (V n) x ↔ x = n := Iff.rfl
theorem termVars_a_iff (x : Nat) : termVars a x ↔ False := Iff.rfl
theorem termVars_b_iff (x : Nat) : termVars b x ↔ False := Iff.rfl
theorem termVars_nil_iff (x : Nat) : termVars nil x ↔ False := Iff.rfl

-- ===================================================================
-- §3.  The `append/3` program + query, in Prolog syntax
-- ===================================================================

-- Forward declarations of the program and query (defined below) are
-- not possible in Lean; the clauseRec-FV lemmas therefore appear
-- after §3 in §3b.

/--
    ```prolog
    append([], L, L).
    ```
    (Base case.  Variable: `L = V 0`.) -/
def clauseBase : FOHornClause appendLang language_noEq :=
  (fact (hNoEq := language_noEq)) append(⟦⟧, V 0, V 0)

/--
    ```prolog
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).
    ```
    (Recursive case.  Variables: `X, Xs, Y, Zs = V 0..V 3`.) -/
def clauseRec : FOHornClause appendLang language_noEq :=
  append(⟦X | Xs⟧, Y, ⟦X | Zs⟧) :- append(Xs, Y, Zs)

/-- The full program `P_append` — the two clauses above. -/
def appendProgram : List (FOHornClause appendLang language_noEq) :=
  [clauseBase, clauseRec]

/--
    ```prolog
    ?- append([a], [b], Z).
    ``` -/
def queryGoal : FOHornClause appendLang language_noEq :=
  (?- append(⟦a⟧, ⟦b⟧, Z)).toGoal

-- ===================================================================
-- §3b.  FV-enumeration lemmas for clauseRec and queryGoal
--
-- These lemmas characterise `clauseFV clauseRec.toFOClause` as
-- exactly `{0, 1, 2, 3}` (from X, Xs, Y, Zs) and
-- `clauseFV queryGoal` as exactly `{10}` (from Z). They support
-- the IsSeparatingPair and standardization-apart proofs below.
-- ===================================================================

/-- `clauseFV` of `clauseRec.toFOClause` is bounded by {0,1,2,3}. -/
theorem clauseRec_FV_subset (x : Nat) :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) x → x ≤ 3 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  rcases hMem with rfl | rfl
  · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, Xs, Y, Zs, termVars_V] at hV
    omega
  · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, X, Xs, Y, Zs, termVars_V] at hV
    omega

/-- `clauseFV` of the negated query-goal literal set is exactly `{10}`. -/
theorem queryGoal_FV_eq_10 (x : Nat) :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) ([append ⟦a⟧ ⟦b⟧ Z].map FOLiteralCore.neg) x
      ↔ x = 10 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
               termVars_cons, termVars_a_iff, termVars_b_iff,
               termVars_nil_iff, Z, termVars_V,
               or_self, or_false, false_or] at hV
    exact hV
  · rintro rfl
    refine ⟨FOLiteralCore.neg (append ⟦a⟧ ⟦b⟧ Z), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars (append ⟦a⟧ ⟦b⟧ Z) 10
      rw [formulaVars_append]; right; right; exact rfl

/-- `0 ∈ clauseFV clauseRec` — X appears in the head. -/
theorem clauseRec_FV_0 :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦X | Xs⟧ Y ⟦X | Zs⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦X | Xs⟧ Y ⟦X | Zs⟧) 0
    rw [formulaVars_append]; left; rw [termVars_cons]; left; rfl

/-- `1 ∈ clauseFV clauseRec` — Xs appears in the head. -/
theorem clauseRec_FV_1 :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦X | Xs⟧ Y ⟦X | Zs⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦X | Xs⟧ Y ⟦X | Zs⟧) 1
    rw [formulaVars_append]; left; rw [termVars_cons]; right; rfl

/-- `2 ∈ clauseFV clauseRec` — Y appears in the head. -/
theorem clauseRec_FV_2 :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦X | Xs⟧ Y ⟦X | Zs⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦X | Xs⟧ Y ⟦X | Zs⟧) 2
    rw [formulaVars_append]; right; left; rfl

/-- `3 ∈ clauseFV clauseRec` — Zs appears in the head. -/
theorem clauseRec_FV_3 :
    (clauseFV (L := appendLang) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 3 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (append ⟦X | Xs⟧ Y ⟦X | Zs⟧), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (append ⟦X | Xs⟧ Y ⟦X | Zs⟧) 3
    rw [formulaVars_append]; right; right; rw [termVars_cons]; right; rfl

-- ===================================================================
-- §4.  The SLD derivation
-- ===================================================================

/-- Type-index reduction for the initial node — the natural `.init`
    output (a list of substituted body atoms) equals the concrete
    singleton `[append ⟦a⟧ ⟦b⟧ Z]`. -/
theorem appendSLDStep0_idx_eq :
    LCS.Finset.ofList queryGoal.bodyFOAtoms
      = LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z] := by
  simp [queryGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal, goal, atomSubst_id]

/-- Initial derivation node `N_0 = ?- append([a], [b], Z)`. Built as
    an explicit `▸` transport of `.init` so that `resultSubstitution`
    can be computed via `appendResultSubstitution_cast`. -/
noncomputable def appendSLDStep0 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal]
      (LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z]) :=
  appendSLDStep0_idx_eq ▸
    FOSLDDerivation.init (D := fun c => c ∈ appendProgram) (goals := [queryGoal])
      queryGoal (List.Mem.head _)

/-- **Step 1** — resolve `?- append([a], [b], Z)` against the
    recursive clause.

    * ρ₁: `X, Xs, Y, Zs` → `V 4..7`.
    * σ₁: `V 4 ↦ a`, `V 5 ↦ []`, `V 6 ↦ [b]`, `V 10 ↦ [a | V 7]`.
    * New current goal: `?- append([], [b], V 7)`. -/
noncomputable def appendSLDStep1 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal]
      ((((LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z]).erase (append ⟦a⟧ ⟦b⟧ Z)).union
        (LCS.Finset.ofList
          (clauseRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧)) :=
  FOSLDDerivation.step
    (prev := appendSLDStep0)
    (clause := clauseRec)
    (hClause := by change _ ∈ appendProgram; simp [appendProgram])
    (hDef := by simp [clauseRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := append ⟦a⟧ ⟦b⟧ Z)
    (headA := append ⟦X | Xs⟧ Y ⟦X | Zs⟧)
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by simp [clauseRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)
    (sigma := ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the recursive append step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      have hCongr : (clauseFV (L := appendLang) (hNoEq := language_noEq))
          ((LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z]).toList.map FOLiteralCore.neg) =
          (clauseFV (L := appendLang) (hNoEq := language_noEq))
            ([append ⟦a⟧ ⟦b⟧ Z].map FOLiteralCore.neg) := by
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
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨7, rfl⟩
        · exact ⟨n + 4, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy h
        have hx3 := clauseRec_FV_subset x hx
        have hy3 := clauseRec_FV_subset y hy
        match x, hx3, y, hy3 with
        | 0, _, 0, _ => rfl
        | 0, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 0, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 0, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 1, _ => rfl
        | 1, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 2, _ => rfl
        | 2, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 3, _ => rfl
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          rw [queryGoal_FV_eq_10] at hPrev
          subst hPrev
          have hn10 : n = 10 :=
            (Term.var.injEq (L := appendLang) _ _).mp hEq₁ |>.symm
          subst hn10
          have hx₂3 := clauseRec_FV_subset x₂ hClause
          match x₂, hx₂3 with
          | 0, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 1, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 2, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 3, _ => simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | _ | n
        · exfalso; exact hx clauseRec_FV_0
        · exfalso; exact hx clauseRec_FV_1
        · exfalso; exact hx clauseRec_FV_2
        · exfalso; exact hx clauseRec_FV_3
        · rfl)


/-- The current-goal type index of `appendSLDStep1` reduces to the
    concrete singleton `{append nil ⟦b⟧ (V 7)}`. -/
theorem appendSLDStep1_currentGoal :
    ((((LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z]).erase (append ⟦a⟧ ⟦b⟧ Z)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧)) =
    LCS.Finset.ofList [append nil ⟦b⟧ (V 7)] := by
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
      simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
            termSubstAll_a, termSubstAll_b, X, Xs, Y, Zs,
            V, ovr, overrideSubst]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨append (V 5) (V 6) (V 7), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨append Xs Y Zs, ?_, ?_⟩
      · simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · show _ = append (V 5) (V 6) (V 7)
        simp [formulaSubstAll_append, Xs, Y, Zs, V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_append, termSubstAll_nil, termSubstAll_b,
            V, ovr, overrideSubst]
      rfl

/-- **Step 2** — close the intermediate goal `?- append([], [b], V 7)`
    with the base fact.

    * ρ₂: `L = V 0 ↦ V 8`.
    * σ₂: `V 7 ↦ [b]`, `V 8 ↦ [b]`.
    * New current goal: `∅` — an SLD-refutation. -/
noncomputable def appendSLDRefutation :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal]
      (∅ : LCS.Finset (FOAtom appendLang language_noEq)) := by
  let step1Idx : LCS.Finset (FOAtom appendLang language_noEq) :=
    ((((LCS.Finset.ofList [append ⟦a⟧ ⟦b⟧ Z]).erase (append ⟦a⟧ ⟦b⟧ Z)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧))
  have step2raw :
      (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal]
        (((step1Idx.erase (append nil ⟦b⟧ (V 7))).union
          (LCS.Finset.ofList
            (clauseBase.bodyFOAtoms.map (fun A =>
              (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 8 ⟧)))
          ).image (fun A => (A.subst (hNoEq := language_noEq))
            ⟦ 7 ↦ ⟦b⟧ | 8 ↦ ⟦b⟧ ⟧)) :=
    FOSLDDerivation.step
      (prev := appendSLDStep1)
      (clause := clauseBase)
      (hClause := by change _ ∈ appendProgram; simp [appendProgram])
      (hDef := by simp [clauseBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := append nil ⟦b⟧ (V 7))
      (headA := append nil (V 0) (V 0))
      (hAk := by
        rw [appendSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by simp [clauseBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := ⟦ 0 ↦ V 8 ⟧)
      (sigma := ⟦ 7 ↦ ⟦b⟧ | 8 ↦ ⟦b⟧ ⟧)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the base append step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        have hCongr : (clauseFV (L := appendLang) (hNoEq := language_noEq))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := appendLang) (hNoEq := language_noEq))
              ([append nil ⟦b⟧ (V 7)].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList [append nil ⟦b⟧ (V 7)] from
              appendSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | n
          · exact ⟨8, rfl⟩
          · exact ⟨n + 1, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy _
          have hx0 : x = 0 := by
            obtain ⟨lit, hMem, hV⟩ := hx
            simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
            subst hMem
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                       termVars_cons, termVars_nil_iff, termVars_V,
                       or_self, or_false, false_or] at hV
            omega
          have hy0 : y = 0 := by
            obtain ⟨lit, hMem, hV⟩ := hy
            simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
            subst hMem
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                       termVars_cons, termVars_nil_iff, termVars_V,
                       or_self, or_false, false_or] at hV
            omega
          rw [hx0, hy0]
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            have hx₁7 : x₁ = 7 := by
              obtain ⟨lit, hMem, hV⟩ := hPrev
              simp at hMem
              subst hMem
              simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_nil_iff, termVars_b_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              exact hV
            subst hx₁7
            have hn7 : n = 7 :=
              (Term.var.injEq (L := appendLang) _ _).mp hEq₁ |>.symm
            subst hn7
            have hx₂0 : x₂ = 0 := by
              obtain ⟨lit, hMem, hV⟩ := hClause
              simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
              subst hMem
              simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_nil_iff, termVars_V,
                         or_self, or_false, false_or] at hV
              omega
            subst hx₂0
            simp [V, ovr, overrideSubst] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | n
          · exfalso; apply hx
            refine ⟨FOLiteralCore.pos (append nil (V 0) (V 0)), ?_, ?_⟩
            · simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
            · change FOAtomCore.vars (append nil (V 0) (V 0)) 0
              rw [formulaVars_append]; right; left; rfl
          · rfl)

  have hIdx :
      (((step1Idx.erase (append nil ⟦b⟧ (V 7))).union
        (LCS.Finset.ofList
          (clauseBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 8 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 7 ↦ ⟦b⟧ | 8 ↦ ⟦b⟧ ⟧)) =
      (∅ : LCS.Finset (FOAtom appendLang language_noEq)) := by
    apply LCS.Finset.ext
    intro A
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨B, hB, _⟩
      rw [LCS.Finset.mem_union] at hB
      rcases hB with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step1Idx = LCS.Finset.ofList [append nil ⟦b⟧ (V 7)] from
                appendSLDStep1_currentGoal,
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

-- ===================================================================
-- §5.  Verification: this IS a refutation
-- ===================================================================

/-- Machine-checked: `appendSLDRefutation` is an SLD-refutation — its
    final current-goal is the empty Finset `∅`. -/
theorem appendSLDRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) appendSLDRefutation :=
  -- BEGIN PROOF
  rfl

-- ===================================================================
-- §6.  Extracting the Prolog answer  Z = [a, b]
-- ===================================================================

/-- The Prolog answer substitution, composing σ₂ ∘ ρ₂ ∘ σ₁ ∘ ρ₁. -/
noncomputable def appendAnswerSubst : Nat → Term appendLang :=
  (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDRefutation

/-- The recovered answer: `Z = [a, b]`. -/
def appendAnswerValue : Term appendLang := ⟦a, b⟧

/-- Transport lemma: `resultSubstitution` is invariant under the Finset
    type-index rewrite used to wrap `.step` outputs. -/
theorem appendResultSubstitution_cast
    {idx1 idx2 : LCS.Finset (FOAtom appendLang language_noEq)} (hIdx : idx1 = idx2)
    (d : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal] idx1) :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) (hIdx ▸ d) =
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) d := by
  subst hIdx; rfl

/-- Helper: composing resultSubstitution-cast-stripping with SubstitutionCore.substCompose
    evaluation on the inner subterm. -/
theorem appendResultSubstitution_cast_inner {idx1 idx2 : LCS.Finset (FOAtom appendLang language_noEq)}
    (hIdx : idx1 = idx2)
    (d : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ appendProgram) [queryGoal] idx1)
    (f : (Nat → Term appendLang) → Nat → Term appendLang) (n : Nat) :
    f ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) (hIdx ▸ d)) n =
    f ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) d) n := by
  subst hIdx; rfl

/-- Helper: `resultSubstitution` of the initial node is `Term.var`,
    and the step0 `▸`-transport doesn't change that. -/
theorem appendSLDStep0_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDStep0 = Term.var := by
  unfold appendSLDStep0
  erw [appendResultSubstitution_cast]
  rfl

/-- Helper: `resultSubstitution` of step1, computed symbolically. -/
theorem appendSLDStep1_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDStep1 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧
        ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)
        Term.var := by
  unfold appendSLDStep1
  show (SubstitutionCore.substCompose (SubstitutionCore.substCompose
    ⟦ 4 ↦ a | 5 ↦ nil | 6 ↦ ⟦b⟧ | 10 ↦ ⟦a | V 7⟧ ⟧
    ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 | 3 ↦ V 7 ⟧)
    ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDStep0)) = _
  rw [appendSLDStep0_resultSubstitution]

/-- Machine-checked: the derivation's composed substitution sends
    `Z = V 10` to `[a, b]`. The syntactic refutation's composed ρ/σ
    chain correctly threads `V 10 ↦ [a, b]`.

    The proof uses `appendResultSubstitution_cast` to strip the
    type-index `▸` transports introduced by the Finset refactor
    (`appendSLDStep0_idx_eq` on the initial node and the final
    Finset-collapse `hIdx` in `appendSLDRefutation`), reducing the
    problem to a direct computation over the chain
    σ₂ ∘ ρ₂ ∘ σ₁ ∘ ρ₁. -/
theorem appendAnswer_eq :
    appendAnswerSubst 10 = appendAnswerValue := by
  -- BEGIN PROOF
  unfold appendAnswerSubst appendAnswerValue appendSLDRefutation
  -- Strip the outer `▸` from `exact hIdx ▸ step2raw`.
  erw [appendResultSubstitution_cast]
  -- step2raw is a .step: resultSubstitution reduces by definition
  show SubstitutionCore.substCompose (SubstitutionCore.substCompose ⟦ 7 ↦ ⟦b⟧ | 8 ↦ ⟦b⟧ ⟧ ⟦ 0 ↦ V 8 ⟧)
      ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDStep1) 10 = ⟦a, b⟧
  rw [appendSLDStep1_resultSubstitution]
  -- All casts stripped; compute.
  simp [SubstitutionCore.substCompose, LCS.FOResolution.Unification.termSubstAll,
        ovr, overrideSubst, idSubst, V, cons, nil, a, b]
  congr 1
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

-- ===================================================================
-- §7.  Semantic lift: from syntactic refutation to unsatisfiability
-- ===================================================================

/-- A placeholder falsum formula over `appendLang` — the clause-form
    API only needs a fixed formula to stand in for `⊥`. -/
def appendFalsum : FormulaN appendLang :=
  (append nil nil nil).toFormula

/-- Every clause in `appendProgram ++ [queryGoal]` has only
    quantifier-free atoms. -/
theorem appendAllQF :
    ∀ c ∈ appendProgram ++ [queryGoal], (FOHornClause.allAtomsQF (hNoEq := language_noEq)) c := by
  -- BEGIN PROOF
  intro c _
  exact (FOHornClause.allAtomsQF_derived (hNoEq := language_noEq)) c

/-- **Showcase theorem** — the full Prolog-level claim, stated with
    program and query inlined as Prolog syntax.

    Given the program
    ```prolog
    append([], L, L).
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).
    ```
    and the query
    ```prolog
    ?- append([a], [b], Z).
    ```
    there exists an SLD-refutation `R` such that:

    **(1) Syntactic — Prolog's answer.** The composed substitution
    sends the query variable `Z` to `[a, b]`.

    **(2) Semantic — Theorem 9.5.1.** Every first-order structure
    that models the program satisfies `append([a], [b], [a, b])` at
    every assignment. I.e. the computed answer `Z = [a, b]` is
    logically entailed by the program. -/
example :
    -- Program:  append([], L, L).  append([X|Xs], Y, [X|Zs]) :- append(Xs, Y, Zs).
    let program : List (FOHornClause appendLang language_noEq) :=
      [ (fact (hNoEq := language_noEq)) append(⟦⟧, V 0, V 0),
        (append(⟦X | Xs⟧, Y, ⟦X | Zs⟧) :- append(Xs, Y, Zs)) ]
    -- Query:  ?- append([a], [b], Z).
    let query : FOHornClause appendLang language_noEq :=
      (?- append(⟦a⟧, ⟦b⟧, Z)).toGoal
    -- Answer: Z ↦ [a, b].
    let answer : Term appendLang := ⟦a, b⟧
    ∃ R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ program) [query] ∅,
      -- (1) Prolog answer:  the derivation's composed substitution sends Z → answer.
      (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) R 10 = answer ∧
      -- (2) Semantic entailment:  ∀ M ⊨ program, M ⊨ append([a], [b], answer).
      (∀ (M : Structure appendLang),
        (∀ c ∈ program,
          ∀ (s : Assignment M),
            formulaEvalN M ((clauseToFormula (hNoEq := language_noEq)) appendFalsum (c.toFOClause (hNoEq := language_noEq))) s) →
        ∀ (s : Assignment M),
          formulaEvalN M (append(⟦a⟧, ⟦b⟧, answer)).toFormula s) := by
  refine ⟨appendSLDRefutation, appendAnswer_eq, ?_⟩
  intro M hProgSat s
  -- The refutation's initial sigma is `Term.var` (appendSLDStep0 built with
  -- sigmaInit = Term.var). Cast-invariance simp lemmas peel the `▸`s.
  have hInitVar : substitutedClauseSet.getInitSigma language_noEq appendSLDRefutation = Term.var := by
    exact getInitSigma_eq_id language_noEq appendSLDRefutation
  have h := (sldAnswer_entails (Afalsum := appendFalsum) (hNoEq := language_noEq)) (P := appendProgram)
    (queryAtom := append(⟦a⟧, ⟦b⟧, Z)) (R := appendSLDRefutation)
    (hRef := appendSLDRefutation_isRefutation)
    (hInitVar := hInitVar)
    M hProgSat s
  -- Push formulaSubstAll through the `append` smart constructor; the only
  -- non-ground term is Z = V 10, so σ Z = σ 10 = ⟦a, b⟧ by `appendAnswer_eq`.
  rw [← atomSubst_toFormula_formulaSubstAll] at h
  simp only [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
             termSubstAll_a, termSubstAll_b] at h
  change formulaEvalN M (append(⟦a⟧, ⟦b⟧,
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) appendSLDRefutation 10)).toFormula s at h
  rw [show FOSLDDerivation.resultSubstitution language_noEq appendSLDRefutation 10 = ⟦a, b⟧
      from appendAnswer_eq] at h
  exact h

-- ===================================================================
-- Sanity-check smoke tests
-- ===================================================================

example : appendAnswerValue = ⟦a, b⟧ := rfl

end LCS.Examples.PrologAppend

end
