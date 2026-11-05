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

/-! # Examples.PrologPath — verified Prolog graph reachability

    A deductive-database style Prolog program: graph reachability
    given edges as facts.

    ```prolog
    % Program — edges of a small DAG  a → b → c  with a → c shortcut:
    edge(a, b).
    edge(b, c).
    edge(a, c).

    % Path closure:
    path(X, Y) :- edge(X, Y).                  % direct edge
    path(X, Y) :- edge(X, Z), path(Z, Y).      % transitive

    % Queries:
    ?- path(a, c).                             % yes (via a→b→c or a→c)
    ?- path(a, X).                             % X = b, X = c, X = c, …
    ```

    This example highlights **two Prolog features** that don't appear
    in `PrologAppend` / `PrologArithmetic`:

    * **Non-recursive facts**: a database of `edge/2` facts with no
      recursive structure — Prolog matches them directly by MGU.
    * **Disjunctive rules**: the path predicate has TWO rules with
      the same head, modelling logical disjunction at the clause
      level. A Prolog system tries each in turn; the SLD-refutation
      we exhibit picks the branch that leads to □.
    * **Intermediate variables** in the recursive rule (`Z` in
      `path(X, Y) :- edge(X, Z), path(Z, Y)`). These variables are
      introduced into the goal by the resolution step, and their
      final bindings follow from the later steps that close them.

    We formalise the program and query concretely. For the ground
    query `?- path(a, c)`, we construct the initial derivation node
    and state the refutation's existence via Lemma 9.5.3. -/

noncomputable section
namespace LCS.Examples.PrologPath

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
-- §1.  Language L_path = { constants a, b, c; predicates edge/2, path/2 }
-- ===================================================================

/-- Graph vertices: three distinct constants `a`, `b`, `c`. -/
inductive PathConst : Type where
  | a : PathConst
  | b : PathConst
  | c : PathConst
  deriving DecidableEq, Repr

/-- No function symbols — graph predicates operate on constants. -/
inductive PathFunc : Type where
  deriving DecidableEq, Repr

/-- Predicates: `edge/2` and `path/2`. -/
inductive PathPred : Type where
  | edge : PathPred
  | path : PathPred
  deriving DecidableEq, Repr

/-- The language for the graph-reachability example. -/
def pathLang : Language where
  funSymbols   := PathFunc
  funArity     := fun f => nomatch f
  constSymbols := PathConst
  predSymbols  := PathPred
  predArity    := fun | .edge => 2 | .path => 2
  hasEquality  := false

/-- The example language contains predicate atoms only. -/
theorem language_noEq : pathLang.withoutEquality := rfl

-- ===================================================================
-- §2.  Prolog constants and smart atoms
-- ===================================================================

/-- Prolog constants `a`, `b`, `c`. -/
def a : Term pathLang := Term.const PathConst.a
def b : Term pathLang := Term.const PathConst.b
def c : Term pathLang := Term.const PathConst.c

/-- Prolog atom `edge(X, Y)`. -/
def edge (x y : Term pathLang) : FOAtom pathLang language_noEq :=
  FOAtomCore.predN (L := pathLang) PathPred.edge (pFin2 x y)

/-- Prolog-style call syntax: `edge(x, y)`. -/
scoped notation:max "edge(" x ", " y ")" => edge x y

/-- Prolog atom `path(X, Y)`. -/
def path (x y : Term pathLang) : FOAtom pathLang language_noEq :=
  FOAtomCore.predN (L := pathLang) PathPred.path (pFin2 x y)

/-- Prolog-style call syntax: `path(x, y)`. -/
scoped notation:max "path(" x ", " y ")" => path x y

-- Variables: X = V 0, Y = V 1, Z = V 2.
abbrev X : Term pathLang := V 0
abbrev Y : Term pathLang := V 1
abbrev Z : Term pathLang := V 2

-- ===================================================================
-- §2b.  Substitution and variable helpers
-- ===================================================================

/-- Push structural atom substitution through `edge t1 t2`. -/
theorem formulaSubstAll_edge (t1 t2 : Term pathLang)
    (σ : Nat → Term pathLang) :
    (edge t1 t2).subst (hNoEq := language_noEq) σ =
      edge (LCS.FOResolution.Unification.termSubstAll t1 σ)
           (LCS.FOResolution.Unification.termSubstAll t2 σ) := by
  -- BEGIN PROOF
  unfold edge FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := pathLang) PathPred.edge
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin2 t1 t2 i) σ) =
    FOAtomCore.predN (L := pathLang) PathPred.edge
      (pFin2
        (LCS.FOResolution.Unification.termSubstAll t1 σ)
        (LCS.FOResolution.Unification.termSubstAll t2 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Push structural atom substitution through `path t1 t2`. -/
theorem formulaSubstAll_path (t1 t2 : Term pathLang)
    (σ : Nat → Term pathLang) :
    (path t1 t2).subst (hNoEq := language_noEq) σ =
      path (LCS.FOResolution.Unification.termSubstAll t1 σ)
           (LCS.FOResolution.Unification.termSubstAll t2 σ) := by
  -- BEGIN PROOF
  unfold path FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN (L := pathLang) PathPred.path
      (fun i => LCS.FOResolution.Unification.termSubstAll
        (pFin2 t1 t2 i) σ) =
    FOAtomCore.predN (L := pathLang) PathPred.path
      (pFin2
        (LCS.FOResolution.Unification.termSubstAll t1 σ)
        (LCS.FOResolution.Unification.termSubstAll t2 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

theorem termSubstAll_a (σ : Nat → Term pathLang) :
    LCS.FOResolution.Unification.termSubstAll a σ = a := rfl
theorem termSubstAll_b (σ : Nat → Term pathLang) :
    LCS.FOResolution.Unification.termSubstAll b σ = b := rfl
theorem termSubstAll_c (σ : Nat → Term pathLang) :
    LCS.FOResolution.Unification.termSubstAll c σ = c := rfl

/-- FV of `edge t1 t2`. -/
theorem formulaVars_edge (t1 t2 : Term pathLang) (n : Nat) :
    (edge t1 t2).vars n ↔ termVars t1 n ∨ termVars t2 n := by
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

/-- FV of `path t1 t2`. -/
theorem formulaVars_path (t1 t2 : Term pathLang) (n : Nat) :
    (path t1 t2).vars n ↔ termVars t1 n ∨ termVars t2 n := by
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

theorem termVars_V (n x : Nat) : termVars (L := pathLang) (V n) x ↔ x = n := Iff.rfl
theorem termVars_a_iff (x : Nat) : termVars a x ↔ False := Iff.rfl
theorem termVars_b_iff (x : Nat) : termVars b x ↔ False := Iff.rfl
theorem termVars_c_iff (x : Nat) : termVars c x ↔ False := Iff.rfl

-- ===================================================================
-- §3.  The program: 3 edge facts + 2 path rules
-- ===================================================================

/-- `edge(a, b).` -/
def edgeAB : FOHornClause pathLang language_noEq := (fact (hNoEq := language_noEq)) edge(a, b)

/-- `edge(b, c).` -/
def edgeBC : FOHornClause pathLang language_noEq := (fact (hNoEq := language_noEq)) edge(b, c)

/-- `edge(a, c).` — shortcut. -/
def edgeAC : FOHornClause pathLang language_noEq := (fact (hNoEq := language_noEq)) edge(a, c)

/-- `path(X, Y) :- edge(X, Y).` — direct edge rule. -/
def pathDirect : FOHornClause pathLang language_noEq :=
  path(X, Y) :- edge(X, Y)

/-- `path(X, Y) :- edge(X, Z), path(Z, Y).` — transitive rule. -/
def pathTrans : FOHornClause pathLang language_noEq :=
  path(X, Y) :- edge(X, Z), path(Z, Y)

/-- The full Prolog program `P_path`. -/
def pathProgram : List (FOHornClause pathLang language_noEq) :=
  [edgeAB, edgeBC, edgeAC, pathDirect, pathTrans]

-- ===================================================================
-- §4.  Query:  ?- path(a, c).
-- ===================================================================

/--
    ```prolog
    ?- path(a, c).
    ```
    Ground query — asking whether `a` reaches `c`. -/
def queryGoal : FOHornClause pathLang language_noEq :=
  (?- path(a, c)).toGoal

-- ===================================================================
-- §5.  Well-formedness against (pathProgram, [queryGoal])
-- ===================================================================

/-- The single query goal is a `.goal`-shaped Horn clause. -/
theorem goalsAreGoals :
    ∀ g ∈ [queryGoal], ∃ body, g = (FOHornClause.goal (hNoEq := language_noEq)) body := by
  -- BEGIN PROOF
  intro g hg
  simp at hg
  subst hg
  exact ⟨_, rfl⟩

/-- Every clause in `pathProgram ++ [queryGoal]` is quantifier-free. -/
theorem allQF :
    ∀ c ∈ pathProgram ++ [queryGoal],
      (FOHornClause.allAtomsQF (hNoEq := language_noEq)) c := by
  -- BEGIN PROOF
  intro c _
  exact (FOHornClause.allAtomsQF_derived (hNoEq := language_noEq)) c

-- ===================================================================
-- §6.  Initial derivation node — a real FOSLDDerivation value
-- ===================================================================

/-- Type-index reduction: `.init`'s natural output equals the concrete
    singleton `[path(a, c)]`. -/
theorem initNode_idx_eq :
    LCS.Finset.ofList queryGoal.bodyFOAtoms
      = LCS.Finset.ofList [path a c] := by
  simp [queryGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal, goal, atomSubst_id]

/-- `N_0 = ?- path(a, c)` — the initial derivation node. Built as a
    `▸` transport so cast-invariance simp lemmas can peel it. -/
noncomputable def initNode :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ pathProgram) [queryGoal]
      (LCS.Finset.ofList [path a c]) :=
  initNode_idx_eq ▸
    FOSLDDerivation.init (D := fun c => c ∈ pathProgram) (goals := [queryGoal])
      queryGoal (List.Mem.head _)

-- ===================================================================
-- §7.  The 1-step refutation via the direct shortcut edge
-- ===================================================================

/-- **Step 1** — resolve `?- path(a, c)` against `pathDirect`.
    ρ₁: X ↦ V 3, Y ↦ V 4.  σ₁: V 3 ↦ a, V 4 ↦ c.
    New goal: `?- edge(a, c)`. -/
noncomputable def pathSLDStep1 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ pathProgram) [queryGoal]
      ((((LCS.Finset.ofList [path a c]).erase (path a c)).union
        (LCS.Finset.ofList
          (pathDirect.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 3 | 1 ↦ V 4 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq)) ⟦ 3 ↦ a | 4 ↦ c ⟧)) :=
  FOSLDDerivation.step
    (prev := initNode)
    (clause := pathDirect)
    (hClause := by change _ ∈ pathProgram; simp [pathProgram])
    (hDef := by simp [pathDirect, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := path a c)
    (headA := path X Y)
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by simp [pathDirect, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 3 | 1 ↦ V 4 ⟧)
    (sigma := ⟦ 3 ↦ a | 4 ↦ c ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the direct path rule step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- Reduce prev's Finset.toList.map neg to the list-based [path a c] neg.
      have hCongr : (clauseFV (L := pathLang) (hNoEq := language_noEq))
          ((LCS.Finset.ofList [path a c]).toList.map FOLiteralCore.neg) =
          (clauseFV (L := pathLang) (hNoEq := language_noEq)) ([path a c].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro a
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _
        rcases x with _ | _ | n
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨n + 2, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · -- FV(pathDirect) = {0, 1}
        intro x y hx hy h
        have hxmem : x = 0 ∨ x = 1 := by
          obtain ⟨lit, hMem, hV⟩ := hx
          simp [pathDirect, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
          rcases hMem with rfl | rfl <;>
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_edge,
                       formulaVars_path, X, Y, termVars_V] at hV <;> omega
        have hymem : y = 0 ∨ y = 1 := by
          obtain ⟨lit, hMem, hV⟩ := hy
          simp [pathDirect, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
          rcases hMem with rfl | rfl <;>
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_edge,
                       formulaVars_path, X, Y, termVars_V] at hV <;> omega
        rcases hxmem with rfl | rfl <;>
          rcases hymem with rfl | rfl <;>
            first | rfl | simp [V, ovr, overrideSubst] at h
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, _⟩, _⟩
          -- prev = queryGoal body = [path a c], which is ground
          obtain ⟨lit, hMem, hV⟩ := hPrev
          simp at hMem
          subst hMem
          simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_path,
                     termVars_a_iff, termVars_c_iff, or_self] at hV
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | n
        · exfalso; apply hx
          refine ⟨FOLiteralCore.pos (path X Y), ?_, ?_⟩
          · simp [pathDirect, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
          · change FOAtomCore.vars (path X Y) 0
            rw [formulaVars_path]; left; rfl
        · exfalso; apply hx
          refine ⟨FOLiteralCore.pos (path X Y), ?_, ?_⟩
          · simp [pathDirect, rule, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal]
          · change FOAtomCore.vars (path X Y) 1
            rw [formulaVars_path]; right; rfl
        · rfl)


/-- The `pathSLDStep1` currentGoal Finset collapses to `{edge a c}`. -/
theorem pathSLDStep1_currentGoal :
    ((((LCS.Finset.ofList [path a c]).erase (path a c)).union
      (LCS.Finset.ofList
        (pathDirect.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 3 | 1 ↦ V 4 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq)) ⟦ 3 ↦ a | 4 ↦ c ⟧)) =
    LCS.Finset.ofList [edge a c] := by
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
      simp [pathDirect, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      subst hA'
      simp [formulaSubstAll_edge, termSubstAll_a, termSubstAll_c,
            V, ovr, overrideSubst]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨edge (V 3) (V 4), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨edge X Y, ?_, ?_⟩
      · simp [pathDirect, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · simp [formulaSubstAll_edge, X, Y, V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_edge, V, ovr, overrideSubst]
      rfl

/-- **Refutation via the shortcut edge `a → c`** — a 2-step chain
    using `pathDirect` and `edgeAC`.

    Step 2 (edgeAC on `edge(a, c)`):
      ρ₂: identity (edgeAC has no variables).
      σ₂: identity (everything is already ground).
      New goal: `∅` (empty — refutation!). -/
noncomputable def pathSLDRefutation :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ pathProgram) [queryGoal]
      (∅ : LCS.Finset (FOAtom pathLang language_noEq)) := by
  let step1Idx : LCS.Finset (FOAtom pathLang language_noEq) :=
    ((((LCS.Finset.ofList [path a c]).erase (path a c)).union
      (LCS.Finset.ofList
        (pathDirect.bodyFOAtoms.map (fun A =>
          (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 3 | 1 ↦ V 4 ⟧)))
      ).image (fun A => (A.subst (hNoEq := language_noEq)) ⟦ 3 ↦ a | 4 ↦ c ⟧))
  have step2raw :
      (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ pathProgram) [queryGoal]
        (((step1Idx.erase (edge a c)).union
          (LCS.Finset.ofList
            (edgeAC.bodyFOAtoms.map (fun A => (A.subst (hNoEq := language_noEq)) Term.var)))
          ).image (fun A => (A.subst (hNoEq := language_noEq)) Term.var)) :=
    FOSLDDerivation.step
      (prev := pathSLDStep1)
      (clause := edgeAC)
      (hClause := by change _ ∈ pathProgram; simp [pathProgram])
      (hDef := by simp [edgeAC, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := edge a c)
      (headA := edge a c)
      (hAk := by
        rw [pathSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by simp [edgeAC, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := Term.var)
      (sigma := Term.var)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the edge fact step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        -- Reduce step1Idx.toList.map neg to [edge a c].map neg.
        have hCongr : (clauseFV (L := pathLang) (hNoEq := language_noEq))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := pathLang) (hNoEq := language_noEq)) ([edge a c].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList [edge a c] from
              pathSLDStep1_currentGoal, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y _ _ h; cases h; rfl
        · -- edgeAC = fact (edge a c) has empty FV
          funext n
          apply propext
          constructor
          · rintro ⟨_, ⟨x₂, hClause, _⟩⟩
            obtain ⟨lit, hMem, hV⟩ := hClause
            simp [edgeAC, fact, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, AtomicQuery.toGoal] at hMem
            subst hMem
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_edge,
                       termVars_a_iff, termVars_c_iff, or_self] at hV
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro _ _; rfl)

  have hIdx :
      (((step1Idx.erase (edge a c)).union
        (LCS.Finset.ofList
          (edgeAC.bodyFOAtoms.map (fun A => (A.subst (hNoEq := language_noEq)) Term.var)))
        ).image (fun A => (A.subst (hNoEq := language_noEq)) Term.var)) =
      (∅ : LCS.Finset (FOAtom pathLang language_noEq)) := by
    apply LCS.Finset.ext
    intro A
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step1Idx = LCS.Finset.ofList [edge a c] from
                pathSLDStep1_currentGoal,
            LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [edgeAC, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  exact hIdx ▸ step2raw

/-- `pathSLDRefutation`'s final current goal is `∅` — by definition. -/
theorem pathSLDRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) pathSLDRefutation :=
  rfl

/-- **Refutation exists** — witnessed by `pathSLDRefutation`. -/
theorem pathRefutation_exists :
    ∃ (cg : LCS.Finset (FOAtom pathLang language_noEq))
      (R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ pathProgram) [queryGoal] cg),
      (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) R :=
  -- BEGIN PROOF
  ⟨(∅ : LCS.Finset (FOAtom pathLang language_noEq)), pathSLDRefutation, rfl⟩

-- ===================================================================
-- §8.  Showcase: the final claim stated directly in Prolog syntax
-- ===================================================================

/-- A placeholder falsum formula — any closed atom. -/
def pathFalsum : FormulaN pathLang := (path a a).toFormula

/-- **Showcase theorem** — the Prolog-level claim, stated with
    program and query inlined as Prolog syntax.

    Given the program
    ```prolog
    edge(a, b).
    edge(b, c).
    edge(a, c).
    path(X, Y) :- edge(X, Y).
    path(X, Y) :- edge(X, Z), path(Z, Y).
    ```
    and the **ground** query
    ```prolog
    ?- path(a, c).
    ```
    there exists an SLD-refutation. Since the query has no output
    variable, **the Prolog answer is simply `yes`** — the query
    succeeds (a reaches c). This is witnessed semantically (Theorem
    9.5.1 corollary): every first-order structure that models the
    program satisfies `path(a, c)` at every assignment. -/
example :
    -- Program:  3 edge facts + 2 path rules (direct edge, transitive).
    let program : List (FOHornClause pathLang language_noEq) :=
      [ (fact (hNoEq := language_noEq)) edge(a, b), (fact (hNoEq := language_noEq)) edge(b, c), (fact (hNoEq := language_noEq)) edge(a, c),
        (path(X, Y) :- edge(X, Y)),
        (path(X, Y) :- edge(X, Z), path(Z, Y)) ]
    -- Query:  ?- path(a, c).
    let query : FOHornClause pathLang language_noEq :=
      (?- path(a, c)).toGoal
    -- Answer:  yes (ground query — no output variable; a reaches c).
    ∃ R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ program) [query] ∅,
      -- (1) Prolog answer "yes":  R is an SLD-refutation (ends in □).
      (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) R ∧
      -- (2) Semantic entailment:  ∀ M ⊨ program, M ⊨ path(a, c).
      (∀ (M : Structure pathLang),
        (∀ c ∈ program,
          ∀ (s : Assignment M),
            formulaEvalN M ((clauseToFormula (hNoEq := language_noEq)) pathFalsum (c.toFOClause (hNoEq := language_noEq))) s) →
        ∀ (s : Assignment M),
          formulaEvalN M (path(a, c)).toFormula s) := by
  refine ⟨pathSLDRefutation, pathSLDRefutation_isRefutation, ?_⟩
  intro M hProgSat s
  have hInitVar : substitutedClauseSet.getInitSigma language_noEq pathSLDRefutation = Term.var := by
    exact getInitSigma_eq_id language_noEq pathSLDRefutation
  have h := (sldAnswer_entails (Afalsum := pathFalsum) (hNoEq := language_noEq)) (P := pathProgram)
    (queryAtom := path(a, c)) (R := pathSLDRefutation)
    (hRef := pathSLDRefutation_isRefutation)
    (hInitVar := hInitVar)
    M hProgSat s
  -- Query is ground: formulaSubstAll is identity.
  rw [← atomSubst_toFormula_formulaSubstAll] at h
  simp only [formulaSubstAll_path, termSubstAll_a, termSubstAll_c] at h
  exact h

-- ===================================================================
-- Sanity-check smoke tests
-- ===================================================================

/-- Program size: 3 edge facts + 2 path rules = 5 clauses. -/
example : pathProgram.length = 5 := rfl

/-- Query is a single-atom goal. -/
example : queryGoal.bodyFOAtoms.length = 1 := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

/-- The goal atom is literally `path(a, c)`. -/
example : queryGoal.bodyFOAtoms.head? = some (path a c) := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

/-- Predicate arities. -/
example : (pathLang.predArity PathPred.edge, pathLang.predArity PathPred.path)
        = (2, 2) := rfl

end LCS.Examples.PrologPath

end
