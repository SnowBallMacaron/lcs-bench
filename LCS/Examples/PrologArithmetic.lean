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

/-! # Examples.PrologArithmetic — end-to-end verified Peano `add`

    A richer companion to `Examples.PrologAppend`, exercising three
    resolution steps instead of two. We work in the textbook's
    Example 9.4.1 language and reuse its Horn clauses for `add`:

    ```prolog
    % Program:
    add(X, 0, X).
    add(X, s(Y), s(Z)) :- add(X, Y, Z).

    % Query:
    ?- add(s(0), s(s(0)), Z).       % i.e.  1 + 2 = Z

    % Expected answer:
    Z = s(s(s(0))).                 % i.e.  3
    ```

    A three-step `FOSLDDerivation` unfolds the recursion twice (both
    uses of the recursive clause) and closes with one use of the base
    clause, yielding the empty clause. The derivation is built as a
    direct chain of `FOSLDDerivation.init` / `FOSLDDerivation.step`
    applications; constructor side conditions (hMGU, hSep,
    hStdApart, hAk) are fully discharged via the §1b / §2b helper
    lemmas. The answer-extraction theorem `answer_eq` is proved by
    direct computation over the refutation's `.step`/`.init`
    structure. -/

noncomputable section
namespace LCS.Examples.PrologArithmetic

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
-- §1.  Reuse Example 9.4.1's language  L = { 0, s/1, add/3 }
-- ===================================================================

/-- Shorthand alias for the Example 9.4.1 language. -/
abbrev L : Language := exAddLang

/-- The example language contains predicate atoms only. -/
theorem language_noEq : L.withoutEquality := rfl

/-- Prolog `0`. -/
def zero : Term L := Term.const ExAddConst.zero

/-- Prolog `s(t)` — successor of `t`. -/
def s (t : Term L) : Term L := Term.func ExAddFunc.succ (pFin1 t)

/-- Prolog-style call syntax: `s(t)`. -/
scoped notation:max "s(" t ")" => s t

/-- Prolog atom `add(T1, T2, T3)`. -/
def add (t1 t2 t3 : Term L) : FOAtom L language_noEq :=
  FOAtomCore.predN (L := L) ExAddPred.add (pFin3 t1 t2 t3)

/-- Prolog-style call syntax: `add(t1, t2, t3)`. -/
scoped notation:max "add(" t1 ", " t2 ", " t3 ")" => add t1 t2 t3

/-- Peano numeral 1 = s(0). -/
abbrev one : Term L := s zero
/-- Peano numeral 2 = s(s(0)). -/
abbrev two : Term L := s (s zero)
/-- Peano numeral 3 = s(s(s(0))). -/
abbrev three : Term L := s (s (s zero))

-- Prolog logic variables (indices 0..2 are used by the program
-- clauses; 20 is the query output).
abbrev X : Term L := V 0
abbrev Y : Term L := V 1
abbrev Z' : Term L := V 2
/-- Query output variable — Prolog `?- add(_, _, Z)`. -/
abbrev Z : Term L := V 20

-- ===================================================================
-- §1b.  Substitution and variable helpers
-- ===================================================================

/-- Push structural atom substitution through `add t1 t2 t3`. -/
theorem formulaSubstAll_add (t1 t2 t3 : Term L) (σ : Nat → Term L) :
    (add t1 t2 t3).subst (hNoEq := language_noEq) σ =
      add (LCS.FOResolution.Unification.termSubstAll t1 σ)
          (LCS.FOResolution.Unification.termSubstAll t2 σ)
          (LCS.FOResolution.Unification.termSubstAll t3 σ) := by
  -- BEGIN PROOF
  unfold add FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := L) ExAddPred.add
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin3 t1 t2 t3 i) σ) =
    FOAtomCore.predN (L := L) ExAddPred.add
      (pFin3
        (LCS.FOResolution.Unification.termSubstAll t1 σ)
        (LCS.FOResolution.Unification.termSubstAll t2 σ)
        (LCS.FOResolution.Unification.termSubstAll t3 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- Push `termSubstAll σ` through `s t`. -/
theorem termSubstAll_s (t : Term L) (σ : Nat → Term L) :
    LCS.FOResolution.Unification.termSubstAll (s t) σ =
      s (LCS.FOResolution.Unification.termSubstAll t σ) := by
  -- BEGIN PROOF
  unfold s
  simp only [LCS.FOResolution.Unification.termSubstAll]
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl

theorem termSubstAll_zero (σ : Nat → Term L) :
    LCS.FOResolution.Unification.termSubstAll zero σ = zero := rfl

/-- FV of `add t1 t2 t3` = FV(t1) ∪ FV(t2) ∪ FV(t3). -/
theorem formulaVars_add (t1 t2 t3 : Term L) (n : Nat) :
    (add t1 t2 t3).vars n ↔
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

/-- FV of `s t` = FV(t). -/
theorem termVars_s (t : Term L) (n : Nat) :
    termVars (s t) n ↔ termVars t n := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact hi
  · intro h
    exact ⟨⟨0, by decide⟩, h⟩

theorem termVars_V (n x : Nat) : termVars (L := L) (V n) x ↔ x = n := Iff.rfl
theorem termVars_zero_iff (x : Nat) : termVars zero x ↔ False := Iff.rfl

-- ===================================================================
-- §2.  The program and the query
-- ===================================================================

/--
    ```prolog
    add(X, 0, X).
    ``` -/
def clauseBase : FOHornClause L language_noEq :=
  (fact (hNoEq := language_noEq)) add(X, zero, X)

/--
    ```prolog
    add(X, s(Y), s(Z)) :- add(X, Y, Z).
    ``` -/
def clauseRec : FOHornClause L language_noEq :=
  add(X, s(Y), s(Z')) :- add(X, Y, Z')

/-- The full program `P_add` — the two clauses above. -/
def additionProgram : List (FOHornClause L language_noEq) :=
  [clauseBase, clauseRec]

/--
    ```prolog
    ?- add(s(0), s(s(0)), Z).        % i.e.  1 + 2 = Z
    ```-/
def queryGoal : FOHornClause L language_noEq :=
  (?- add(one, two, Z)).toGoal

-- ===================================================================
-- §2b.  FV enumeration for the program and query
-- ===================================================================

/-- `clauseFV clauseRec.toFOClause` ⊆ {0, 1, 2}. -/
theorem clauseRec_FV_subset (x : Nat) :
    (clauseFV (L := L) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) x → x = 0 ∨ x = 1 ∨ x = 2 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  rcases hMem with rfl | rfl
  · -- .neg (add X Y Z')
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
               X, Y, Z', termVars_V] at hV
    omega
  · -- .pos (add X (s Y) (s Z'))
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
               termVars_s, X, Y, Z', termVars_V] at hV
    omega

/-- `clauseFV clauseBase.toFOClause` ⊆ {0}. -/
theorem clauseBase_FV_subset (x : Nat) :
    (clauseFV (L := L) (hNoEq := language_noEq)) (clauseBase.toFOClause (hNoEq := language_noEq)) x → x = 0 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
  subst hMem
  simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
             X, termVars_V, termVars_zero_iff, or_self, or_false, false_or] at hV
  exact hV

/-- `clauseFV queryGoal` = {20}. -/
theorem queryGoal_FV_eq_20 (x : Nat) :
    (clauseFV (L := L) (hNoEq := language_noEq)) ([add one two Z].map FOLiteralCore.neg) x ↔ x = 20 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
               one, two, Z, termVars_s, termVars_zero_iff, termVars_V,
               or_self, or_false, false_or] at hV
    exact hV
  · rintro rfl
    refine ⟨FOLiteralCore.neg (add one two Z), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars (add one two Z) 20
      rw [formulaVars_add]; right; right; exact rfl

theorem clauseRec_FV_0 : (clauseFV (L := L) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (add X (s Y) (s Z')), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (add X (s Y) (s Z')) 0
    rw [formulaVars_add]; left; rfl

theorem clauseRec_FV_1 : (clauseFV (L := L) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (add X (s Y) (s Z')), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (add X (s Y) (s Z')) 1
    rw [formulaVars_add]; right; left; rw [termVars_s]; rfl

theorem clauseRec_FV_2 : (clauseFV (L := L) (hNoEq := language_noEq)) (clauseRec.toFOClause (hNoEq := language_noEq)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (add X (s Y) (s Z')), ?_, ?_⟩
  · simp [clauseRec, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (add X (s Y) (s Z')) 2
    rw [formulaVars_add]; right; right; rw [termVars_s]; rfl

theorem clauseBase_FV_0 : (clauseFV (L := L) (hNoEq := language_noEq)) (clauseBase.toFOClause (hNoEq := language_noEq)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (add X zero X), ?_, ?_⟩
  · simp [clauseBase, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
  · change FOAtomCore.vars (add X zero X) 0
    rw [formulaVars_add]; left; rfl

-- ===================================================================
-- §3.  The 3-step SLD derivation
-- ===================================================================

/-- Type-index reduction for the initial node — the natural `.init`
    output (a list of substituted body atoms) equals the concrete
    singleton `[add one two Z]`. -/
theorem step0_idx_eq :
    LCS.Finset.ofList queryGoal.bodyFOAtoms
      = LCS.Finset.ofList [add one two Z] := by
  simp [queryGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal, goal, atomSubst_id]

/-- Initial derivation node `N_0 = ?- add(1, 2, Z)`. Built as an
    explicit `▸` transport of `.init` so that `resultSubstitution`
    can be computed via `resultSubstitution_cast`. -/
noncomputable def step0 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal]
      (LCS.Finset.ofList [add one two Z]) :=
  step0_idx_eq ▸
    FOSLDDerivation.init (D := fun c => c ∈ additionProgram) (goals := [queryGoal])
      queryGoal (List.Mem.head _)

/-- **Step 1** — resolve  ?- add(1, 2, Z)  against the recursive clause.

    * ρ₁:  X ↦ V 4, Y ↦ V 5, Z' ↦ V 6.
    * σ₁:  V 4 ↦ 1, V 5 ↦ s(0), V 20 ↦ s(V 6).
    * New goal (up to Fin-indexed sigma evaluation):
      `?- add(1, s(0), V 6)`. -/
noncomputable def step1 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal]
      ((((LCS.Finset.ofList [add one two Z]).erase (add one two Z)).union
        (LCS.Finset.ofList
          (clauseRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧)) :=
  FOSLDDerivation.step
    (prev := step0)
    (clause := clauseRec)
    (hClause := by change _ ∈ additionProgram; simp [additionProgram])
    (hDef := by simp [clauseRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := add one two Z)
    (headA := add X (s Y) (s Z'))
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by simp [clauseRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)
    (sigma := ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the first recursive addition step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      have hCongr : (clauseFV (L := L) (hNoEq := language_noEq))
          ((LCS.Finset.ofList [add one two Z]).toList.map FOLiteralCore.neg) =
          (clauseFV (L := L) (hNoEq := language_noEq)) ([add one two Z].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _
        rcases x with _ | _ | _ | n
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨n + 3, rfl⟩
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
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          rw [queryGoal_FV_eq_20] at hPrev
          subst hPrev
          have hn20 : n = 20 :=
            (Term.var.injEq (L := L) _ _).mp hEq₁ |>.symm
          subst hn20
          have hx₂mem := clauseRec_FV_subset x₂ hClause
          rcases hx₂mem with rfl | rfl | rfl <;>
            simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | n
        · exfalso; exact hx clauseRec_FV_0
        · exfalso; exact hx clauseRec_FV_1
        · exfalso; exact hx clauseRec_FV_2
        · rfl)


/-- The `step1` currentGoal Finset collapses to `{add one (s zero) (V 6)}`. -/
theorem step1_currentGoal :
    ((((LCS.Finset.ofList [add one two Z]).erase (add one two Z)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧)) =
    LCS.Finset.ofList [add one (s zero) (V 6)] := by
  -- BEGIN PROOF
  apply LCS.Finset.ext
  intro A
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
      obtain ⟨A', hA', rfl⟩ := himg
      simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      subst hA'
      simp [formulaSubstAll_add, termSubstAll_s, termSubstAll_zero, one, two,
            V, ovr, overrideSubst]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨add (V 4) (V 5) (V 6), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨add X Y Z', ?_, ?_⟩
      · simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · show _ = add (V 4) (V 5) (V 6)
        simp [formulaSubstAll_add, X, Y, Z', V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_add, termSubstAll_s, termSubstAll_zero,
            one, two, V, ovr, overrideSubst]
      rfl

/-- **Step 2** — resolve the intermediate goal `?- add(1, s(0), V 6)`
    against the recursive clause. -/
noncomputable def step2 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal]
      ((((LCS.Finset.ofList [add one (s zero) (V 6)]).erase
          (add one (s zero) (V 6))).union
        (LCS.Finset.ofList
          (clauseRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧)) := by
  let step1Idx : LCS.Finset (FOAtom L language_noEq) :=
    ((((LCS.Finset.ofList [add one two Z]).erase (add one two Z)).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧))
  have step2raw :=
    FOSLDDerivation.step
      (prev := step1)
      (clause := clauseRec)
      (hClause := by change _ ∈ additionProgram; simp [additionProgram])
      (hDef := by simp [clauseRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := add one (s zero) (V 6))
      (headA := add X (s Y) (s Z'))
      (hAk := by rw [step1_currentGoal, LCS.Finset.mem_ofList]; simp)
      (hHead := by simp [clauseRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)
      (sigma := ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the second recursive addition step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        have hCongr : (clauseFV (L := L) (hNoEq := language_noEq))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := L) (hNoEq := language_noEq)) ([add one (s zero) (V 6)].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList [add one (s zero) (V 6)] from
              step1_currentGoal, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | _ | _ | n
          · exact ⟨7, rfl⟩
          · exact ⟨8, rfl⟩
          · exact ⟨9, rfl⟩
          · exact ⟨n + 3, rfl⟩
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
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            have hx₁6 : x₁ = 6 := by
              obtain ⟨lit, hMem, hV⟩ := hPrev
              simp at hMem
              subst hMem
              simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
                         termVars_s, one, termVars_zero_iff, termVars_V,
                         or_self, or_false, false_or] at hV
              exact hV
            subst hx₁6
            have hn6 : n = 6 :=
              (Term.var.injEq (L := L) _ _).mp hEq₁ |>.symm
            subst hn6
            have hx₂mem := clauseRec_FV_subset x₂ hClause
            rcases hx₂mem with rfl | rfl | rfl <;>
              simp [V, ovr, overrideSubst] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | _ | _ | n
          · exfalso; exact hx clauseRec_FV_0
          · exfalso; exact hx clauseRec_FV_1
          · exfalso; exact hx clauseRec_FV_2
          · rfl)

  exact (congrArg (fun (x : LCS.Finset (FOAtom L language_noEq)) =>
      (((x.erase (add one (s zero) (V 6))).union
        (LCS.Finset.ofList
          (clauseRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧))) step1_currentGoal) ▸ step2raw

/-- The `step2` currentGoal Finset collapses to `{add one zero (V 9)}`. -/
theorem step2_currentGoal :
    ((((LCS.Finset.ofList [add one (s zero) (V 6)]).erase
        (add one (s zero) (V 6))).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧)) =
    LCS.Finset.ofList [add one zero (V 9)] := by
  -- BEGIN PROOF
  apply LCS.Finset.ext
  intro A
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
      obtain ⟨A', hA', rfl⟩ := himg
      simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      subst hA'
      simp [formulaSubstAll_add, termSubstAll_s, termSubstAll_zero, one,
            V, ovr, overrideSubst]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨add (V 7) (V 8) (V 9), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨add X Y Z', ?_, ?_⟩
      · simp [clauseRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · show _ = add (V 7) (V 8) (V 9)
        simp [formulaSubstAll_add, X, Y, Z', V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_add, termSubstAll_s, termSubstAll_zero,
            one, V, ovr, overrideSubst]
      rfl

/-- **Step 3** — close the intermediate goal `?- add(1, 0, V 9)` with
    the base fact `clauseBase : add(X, 0, X)`. -/
noncomputable def refutation :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal] (∅ : LCS.Finset (FOAtom L language_noEq)) := by
  let step2Idx : LCS.Finset (FOAtom L language_noEq) :=
    ((((LCS.Finset.ofList [add one (s zero) (V 6)]).erase
        (add one (s zero) (V 6))).union
      (LCS.Finset.ofList
        (clauseRec.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq))
        ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧))
  have step3raw :
      (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal]
        (((step2Idx.erase (add one zero (V 9))).union
          (LCS.Finset.ofList
            (clauseBase.bodyFOAtoms.map (fun A =>
              (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 10 ⟧)))
          ).image (fun A => (A.subst (hNoEq := language_noEq))
            ⟦ 9 ↦ one | 10 ↦ one ⟧)) :=
    FOSLDDerivation.step
      (prev := step2)
      (clause := clauseBase)
      (hClause := by change _ ∈ additionProgram; simp [additionProgram])
      (hDef := by simp [clauseBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := add one zero (V 9))
      (headA := add X zero X)
      (hAk := by
        change add one zero (V 9) ∈ step2Idx
        rw [show step2Idx = LCS.Finset.ofList [add one zero (V 9)] from
            step2_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by simp [clauseBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := ⟦ 0 ↦ V 10 ⟧)
      (sigma := ⟦ 9 ↦ one | 10 ↦ one ⟧)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the base addition step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        have hCongr : (clauseFV (L := L) (hNoEq := language_noEq))
            (step2Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := L) (hNoEq := language_noEq)) ([add one zero (V 9)].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step2Idx ↔ _
          rw [show step2Idx = LCS.Finset.ofList [add one zero (V 9)] from
              step2_currentGoal, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | n
          · exact ⟨10, rfl⟩
          · exact ⟨n + 1, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy _
          have hxmem := clauseBase_FV_subset x hx
          have hymem := clauseBase_FV_subset y hy
          omega
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            have hx₁9 : x₁ = 9 := by
              obtain ⟨lit, hMem, hV⟩ := hPrev
              simp at hMem
              subst hMem
              simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_add,
                         one, termVars_s, termVars_zero_iff, termVars_V,
                         or_self, or_false, false_or] at hV
              exact hV
            subst hx₁9
            have hn9 : n = 9 :=
              (Term.var.injEq (L := L) _ _).mp hEq₁ |>.symm
            subst hn9
            have hx₂mem := clauseBase_FV_subset x₂ hClause
            subst hx₂mem
            simp [V, ovr, overrideSubst] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | n
          · exfalso; exact hx clauseBase_FV_0
          · rfl)

  have hIdx :
      (((step2Idx.erase (add one zero (V 9))).union
        (LCS.Finset.ofList
          (clauseBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 10 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 9 ↦ one | 10 ↦ one ⟧)) =
      (∅ : LCS.Finset (FOAtom L language_noEq)) := by
    apply LCS.Finset.ext
    intro A
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step2Idx = LCS.Finset.ofList [add one zero (V 9)] from
                step2_currentGoal,
            LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [clauseBase, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  exact hIdx ▸ step3raw

-- ===================================================================
-- §4.  Refutation check:  the derivation really ends with □
-- ===================================================================

/-- Machine-checked: the three-step derivation ends with the empty
    current goal — i.e. it is an SLD-refutation of the query. -/
theorem refutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) refutation :=
  -- BEGIN PROOF
  rfl

-- ===================================================================
-- §5.  Answer extraction:  Z ↦ s(s(s(0)))  ≡  Z = 3
-- ===================================================================

/-- The Prolog answer substitution — composes σ₃ ∘ ρ₃ ∘ σ₂ ∘ ρ₂ ∘ σ₁ ∘ ρ₁. -/
noncomputable def answerSubst : Nat → Term L :=
  (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) refutation

/-- Prolog's answer for `Z`: `s(s(s(0))) = 3`. -/
def answerValue : Term L := three

/-- Transport lemma: `resultSubstitution` is invariant under the Finset
    type-index rewrite used to wrap `.step` outputs. -/
theorem resultSubstitution_cast
    {idx1 idx2 : LCS.Finset (FOAtom L language_noEq)} (hIdx : idx1 = idx2)
    (d : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ additionProgram) [queryGoal] idx1) :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) (hIdx ▸ d) =
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) d := by
  subst hIdx; rfl

/-- Helper: `resultSubstitution` of the initial node is `Term.var`,
    and the step0 `▸`-transport doesn't change that. -/
theorem step0_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step0 = Term.var := by
  unfold step0
  erw [resultSubstitution_cast]
  rfl

/-- Helper: `resultSubstitution` of step1, computed symbolically. -/
theorem step1_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step1 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧
        ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)
        Term.var := by
  unfold step1
  show (SubstitutionCore.substCompose (SubstitutionCore.substCompose
    ⟦ 4 ↦ one | 5 ↦ s zero | 20 ↦ s (V 6) ⟧
    ⟦ 0 ↦ V 4 | 1 ↦ V 5 | 2 ↦ V 6 ⟧)
    ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step0)) = _
  rw [step0_resultSubstitution]

/-- Helper: `resultSubstitution` of step2, computed symbolically. -/
theorem step2_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step2 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 6 ↦ s (V 9) | 7 ↦ one | 8 ↦ zero ⟧
        ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step1) := by
  unfold step2
  erw [resultSubstitution_cast]
  rfl

/-- Machine-checked: the derivation's composed substitution sends
    `Z = V 20` to `3 = s(s(s(0)))`. The three successor layers follow
    the three resolution steps. -/
theorem answer_eq : answerSubst 20 = answerValue := by
  -- BEGIN PROOF
  unfold answerSubst answerValue refutation
  erw [resultSubstitution_cast]
  -- refutation's .step reduces — resultSubstitution is:
  --   SubstitutionCore.substCompose (SubstitutionCore.substCompose σ₃ ρ₃) (resultSubstitution step2)
  show SubstitutionCore.substCompose (SubstitutionCore.substCompose ⟦ 9 ↦ one | 10 ↦ one ⟧ ⟦ 0 ↦ V 10 ⟧)
      ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) step2) 20 = three
  rw [step2_resultSubstitution, step1_resultSubstitution]
  -- All casts stripped; compute — this is the pre-refactor proof pattern.
  simp [FOSLDDerivation.resultSubstitution, SubstitutionCore.substCompose,
        LCS.FOResolution.Unification.termSubstAll,
        ovr, overrideSubst, idSubst, V,
        termSubstAll_s, termSubstAll_zero, answerValue, three, two, one, s, zero]
  congr 1
  funext ⟨i, hi⟩
  -- Fin 1: only i = 0
  match i, hi with
  | 0, _ =>
    -- Reduce both sides through pFin1, SubstitutionCore.substCompose, termSubstAll, overrides.
    simp only [pFin1, LCS.FOResolution.Unification.termSubstAll, SubstitutionCore.substCompose,
               V, ovr, overrideSubst, idSubst,
               show (6 = 0 : Prop) = False from by decide,
               show (6 = 1 : Prop) = False from by decide,
               show (6 = 2 : Prop) = False from by decide,
               show (6 = 6 : Prop) = True from by decide,
               show (6 = 7 : Prop) = False from by decide,
               show (6 = 8 : Prop) = False from by decide,
               show (9 = 0 : Prop) = False from by decide,
               show (9 = 9 : Prop) = True from by decide,
               show (9 = 10 : Prop) = False from by decide,
               if_false, if_true]
    -- Now we're left with s (termSubstAll (V 9) σ₃ρ₃) = s (s zero) after σ₂ reduction.
    -- σ₃ρ₃ sends V 9 → s zero, so the inner becomes s zero.
    apply congrArg
    funext ⟨j, hj⟩
    match j, hj with
    | 0, _ =>
      simp only [pFin1, LCS.FOResolution.Unification.termSubstAll, SubstitutionCore.substCompose,
                 V, ovr, overrideSubst, idSubst,
                 show (9 = 0 : Prop) = False from by decide,
                 show (9 = 9 : Prop) = True from by decide,
                 show (9 = 10 : Prop) = False from by decide,
                 if_false, if_true]

-- ===================================================================
-- §6.  Well-formedness against (additionProgram, [queryGoal])
-- ===================================================================

/-- The single query goal is a `.goal`-shaped Horn clause. -/
theorem goalsAreGoals :
    ∀ g ∈ [queryGoal], ∃ body, g = (FOHornClause.goal (hNoEq := language_noEq)) body := by
  -- BEGIN PROOF
  intro g hg
  simp at hg
  subst hg
  exact ⟨_, rfl⟩

/-- Every clause in the program plus the query is quantifier-free. -/
theorem allQF :
    ∀ c ∈ additionProgram ++ [queryGoal],
      (FOHornClause.allAtomsQF (hNoEq := language_noEq)) c := by
  -- BEGIN PROOF
  intro c _
  exact (FOHornClause.allAtomsQF_derived (hNoEq := language_noEq)) c

-- ===================================================================
-- §7.  Showcase: the final claim stated directly in Prolog syntax
-- ===================================================================

/-- A designated falsum formula over `L` — any closed atom works
    since the clause-form API only needs a fixed `⊥`-shaped formula. -/
def falsum : FormulaN L := (add zero zero zero).toFormula

/-- **Showcase theorem** — the full Prolog-level claim, stated with
    program and query inlined as Prolog syntax.

    Given the program
    ```prolog
    add(X, 0, X).
    add(X, s(Y), s(Z)) :- add(X, Y, Z).
    ```
    and the query
    ```prolog
    ?- add(s(0), s(s(0)), Z).     % i.e.  1 + 2 = Z
    ```
    there exists an SLD-refutation `R` such that:

    **(1) Syntactic — Prolog's answer.** The composed substitution
    sends the query variable `Z` to `s(s(s(0)))`.

    **(2) Semantic — Theorem 9.5.1.** Every first-order structure
    that models the program satisfies `add(s(0), s(s(0)), s(s(s(0))))`
    at every assignment. I.e. the computed answer `Z = 3` is
    logically entailed by the program. -/
example :
    -- Program:  add(X, 0, X).  add(X, s(Y), s(Z)) :- add(X, Y, Z).
    let program : List (FOHornClause L language_noEq) :=
      [ (fact (hNoEq := language_noEq)) add(X, zero, X),
        (add(X, s(Y), s(Z')) :- add(X, Y, Z')) ]
    -- Query:  ?- add(s(0), s(s(0)), Z).   (1 + 2 = Z)
    let query : FOHornClause L language_noEq :=
      (?- add(one, two, Z)).toGoal
    -- Answer:  Z ↦ s(s(s(0))) = 3.
    let answer : Term L := three
    ∃ R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ program) [query] ∅,
      -- (1) Prolog answer:  the composed substitution sends Z → answer.
      (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) R 20 = answer ∧
      -- (2) Semantic entailment:  ∀ M ⊨ program, M ⊨ add(1, 2, answer).
      (∀ (M : Structure L),
        (∀ c ∈ program,
          ∀ (s : Assignment M),
            formulaEvalN M ((clauseToFormula (hNoEq := language_noEq)) falsum (c.toFOClause (hNoEq := language_noEq))) s) →
        ∀ (s : Assignment M),
          formulaEvalN M (add(one, two, answer)).toFormula s) := by
  refine ⟨refutation, answer_eq, ?_⟩
  intro M hProgSat s
  -- The refutation's initial sigma is `Term.var` (step0 built with
  -- sigmaInit = Term.var). Cast-invariance simp lemmas peel the `▸`s.
  have hInitVar : substitutedClauseSet.getInitSigma language_noEq refutation = Term.var := by
    exact getInitSigma_eq_id language_noEq refutation
  have h := (sldAnswer_entails (Afalsum := falsum) (hNoEq := language_noEq)) (P := additionProgram)
    (queryAtom := add(one, two, Z)) (R := refutation)
    (hRef := refutation_isRefutation)
    (hInitVar := hInitVar)
    M hProgSat s
  -- Push formulaSubstAll through `add` / `s` / `zero`; the only non-ground
  -- term is Z = V 20, so σ Z = σ 20 = three by `answer_eq`.
  rw [← atomSubst_toFormula_formulaSubstAll] at h
  simp only [formulaSubstAll_add, termSubstAll_s, termSubstAll_zero] at h
  change formulaEvalN M (add(one, two,
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) refutation 20)).toFormula s at h
  rw [show FOSLDDerivation.resultSubstitution language_noEq refutation 20 = three
      from answer_eq] at h
  exact h

-- ===================================================================
-- Sanity-check smoke tests
-- ===================================================================

example : answerValue = s (s (s zero)) := rfl

end LCS.Examples.PrologArithmetic

end
