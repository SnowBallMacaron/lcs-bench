import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import LCS.FOResolution.GroundResolution.GroundClauses
import LCS.FOResolution.GroundResolution.PropositionalTranslation
import LCS.FOResolution.Unification.Part1
import LCS.FOResolution.Graph
import LCS.Herbrand.PrimRecursive
import LCS.FirstOrder.Equality.Search.Part2
import LCS.CutElim.LKe.Equivalence.Validity
import Attach
import LCS.FOResolution.GroundResolution.ProofsStamp

/-! # FOResolution.GroundResolution
    Formalization of Chapter 8, Section 8.3.
    Ground resolution method and its completeness for ground clauses.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.GroundResolution

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm

-- ===================================================================
-- Example 8.3.1 (companion): FOResolutionTree
-- ===================================================================

-- ===================================================================
-- Example 8.3.1 (companion): FOResolutionTree.label
-- ===================================================================
namespace FOResolutionTree


end FOResolutionTree

-- ===================================================================
-- Lemma 8.3.1 (companion): FOClause.isSatisfied
-- ===================================================================
open LCS.FirstOrder.SemanticsN

namespace FOLiteral


end FOLiteral

namespace FOClause


end FOClause

namespace FOResolutionTree


end FOResolutionTree

-- ===================================================================
-- Lemma 8.3.1 (companion): GroundClauseSet.isUnsatisfiable
-- ===================================================================
namespace GroundClauseSet


end GroundClauseSet

-- ===================================================================
-- Lemma 8.3.1 (companion): groundInstantiate
-- ===================================================================

-- ===================================================================
-- Ground-to-Propositional Translation Infrastructure
-- ===================================================================
-- Bridge between first-order ground clauses (FOClause L) and
-- propositional clauses (Clause = Finset Literal from GCNF).
-- For ground clauses (no variables), each first-order literal
-- pos/neg(P(c1,...,cn)) can be mapped to a propositional literal
-- pos/neg(k) by encoding the atomic formula as a natural number.
-- The proof of ground resolution completeness chains through the
-- propositional resolution completeness theorem (Theorem 4.3.2).

open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical

-- ===================================================================
-- Translation functions (parametric in an encoding)
-- ===================================================================



/-! The equality caveat concerns the ordinary propositional resolution route.
    Equality atoms can be encoded for that route using the general atom carrier;
    the public equality-free ground-resolution calculus remains unchanged. -/

/-- Lemma 8.3.1 (equality caveat): the ground unit clause `¬(a = a)` is
    unsatisfiable under identity equality, but its ordinary propositional
    abstraction has no resolution refutation. The encoding is applied to the
    very same reflexive equality atom; no injectivity assumption is needed on
    a one-atom clause set. This counterexample concerns ordinary resolution. -/
@[blueprint "chap8__lemma_8_3_1"]
theorem ordinaryGroundResolution_equality_counterexample
    {L : Language} (hEq : L.hasEquality = true) (a : L.constSymbols)
    (encode : FOAtomCore L → Nat) :
    (∀ (M : Structure L) (s : Assignment M),
      ¬ formulaEvalN M (.neg (.eq_ hEq (.const a) (.const a))) s) ∧
    ¬ ∃ D : ResolutionDAG,
      D.isResolutionRefutation
        (ClauseSequent.single
          (Clause.single (.neg (encode (.eq_ hEq (.const a) (.const a))))))

open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence

/-- Lemma 8.3.1 (equality caveat): the equality-aware sequent route admits
    the equality axioms and permits atomic cuts, while retaining completeness
    for quantifier-free sequents under identity equality. These are permissions
    in the existing LK_e system: individual proofs may contain no cuts.
    The three clauses exhibit its equality-axiom leaves, closure under atomic
    cut, and quantifier-free completeness with only inessential cuts. -/
@[blueprint "chap8__lemma_8_3_1"]
theorem equalityGroundRules_requirements
    {L : Language} (hEq : L.hasEquality = true) :
    (∀ ax : LKeEqualityAxiom L,
      lkeProvableWithoutEssentialCuts (ax.toSequent hEq)) ∧
    (∀ (A : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L)),
      LKeCut.isAtomic A →
      lkeProvableWithoutEssentialCuts (Sequent.mk Γ (Δ ++ [A])) →
      lkeProvableWithoutEssentialCuts (Sequent.mk (A :: Λ) Θ) →
      lkeProvableWithoutEssentialCuts (Sequent.mk (Γ ++ Λ) (Δ ++ Θ))) ∧
    (∀ seq : Sequent L,
      (∀ A ∈ seq.antecedent ++ seq.succedent, isQuantifierFree A) →
      sequentValid seq → lkeProvableWithoutEssentialCuts seq)

open LCS.FOResolution.Unification

/-- Example 8.3.1: (a/z1, a/x), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G1 (n : Nat) : Term exClauseFormLang :=
  if n = 1 ∨ n = 4 then exSkolemConst_a else .var n

/-- Example 8.3.1: (a/z2), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G2 (n : Nat) : Term exClauseFormLang :=
  if n = 2 then exSkolemConst_a else .var n

/-- Example 8.3.1: (a/z3), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G3 (n : Nat) : Term exClauseFormLang :=
  if n = 3 then exSkolemConst_a else .var n

/-- Example 8.3.1: (f(a)/z1, a/x), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G4 (n : Nat) : Term exClauseFormLang :=
  if n = 1 then exGroundTerm_fa
  else if n = 4 then exSkolemConst_a else .var n

/-- The motivating example in §8.4.1 uses one simultaneous substitution
    (a/x, a/z1, a/z2). All other variables are fixed. -/
@[blueprint "chap8__example_8_3_1"]
def exUnificationSubst (n : Nat) : Term exClauseFormLang :=
  if n = 1 ∨ n = 2 ∨ n = 4 then exSkolemConst_a else .var n

/-- Apply a simultaneous substitution to an example literal, preserving
    its sign and extending the variable map homomorphically to terms. -/
@[blueprint "chap8__example_8_3_1"]
def exLiteralSubst (sigma : Nat → Term exClauseFormLang) :
    FOLiteral exClauseFormLang rfl → FOLiteral exClauseFormLang rfl
  | .pos A => .pos (A.mapTerms (fun t => termSubstAll t sigma))
  | .neg A => .neg (A.mapTerms (fun t => termSubstAll t sigma))

/-- The displayed substitutions have exactly the stated finite supports.
    Variables are numbered z1=1, z2=2, z3=3 and x=4. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundSubstitutions_support :
    (∀ n, exGroundSubst_G1 n ≠ .var n ↔ n = 1 ∨ n = 4) ∧
    (∀ n, exGroundSubst_G2 n ≠ .var n ↔ n = 2) ∧
    (∀ n, exGroundSubst_G3 n ≠ .var n ↔ n = 3) ∧
    (∀ n, exGroundSubst_G4 n ≠ .var n ↔ n = 1 ∨ n = 4) ∧
    (∀ n, exUnificationSubst n ≠ .var n ↔ n = 1 ∨ n = 2 ∨ n = 4)

/-- G1 is the literal-set image of C1 under (a/z1,a/x).
    Its three negative literals collapse to the single literal not P(a,a). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G1_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C1.map (exLiteralSubst exGroundSubst_G1) ↔
      lit ∈ exGroundClause_G1

/-- G2 is the literal-set image of C2 under (a/z2). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G2_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C2.map (exLiteralSubst exGroundSubst_G2) ↔
      lit ∈ exGroundClause_G2

/-- G3 is the literal-set image of C3 under (a/z3). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G3_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C3.map (exLiteralSubst exGroundSubst_G3) ↔
      lit ∈ exGroundClause_G3

/-- G4 is the literal-set image of C1 under (f(a)/z1,a/x).
    The first two substituted literals coincide. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G4_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C1.map (exLiteralSubst exGroundSubst_G4) ↔
      lit ∈ exGroundClause_G4

/-- The selected negative subset of C1 in the motivating example is all C1. -/
@[blueprint "chap8__example_8_3_1"]
def exUnificationLeft : FOClause exClauseFormLang rfl := exClause_C1

/-- The selected positive subset of C2 is the singleton {P(z2,a)}. -/
@[blueprint "chap8__example_8_3_1"]
def exUnificationRight : FOClause exClauseFormLang rfl :=
  [.pos (exPred_P (.var 2) exSkolemConst_a)]

/-- The chosen sets belong to their respective clauses. Conjugating the
    negative C1 subset gives exactly the three displayed positive literals;
    the C2 singleton already has positive sign. -/
@[blueprint "chap8__example_8_3_1"]
theorem exUnificationSubsets :
    (∀ lit ∈ exUnificationLeft, lit ∈ exClause_C1) ∧
    (∀ lit ∈ exUnificationRight, lit ∈ exClause_C2) ∧
    exUnificationLeft.map (FOLiteral.conjugate (L := exClauseFormLang) rfl) =
      [.pos (exPred_P (.var 1) exSkolemConst_a),
       .pos (exPred_P (.var 1) (.var 4)),
       .pos (exPred_P (.var 4) (.var 1))]

/-- The same substitution simultaneously takes C1 to G1 and C2 to G2,
    the two ground premises of the motivating resolution step. -/
@[blueprint "chap8__example_8_3_1"]
theorem exUnificationGroundImages :
    (∀ lit, lit ∈ exClause_C1.map (exLiteralSubst exUnificationSubst) ↔
      lit ∈ exGroundClause_G1) ∧
    (∀ lit, lit ∈ exClause_C2.map (exLiteralSubst exUnificationSubst) ↔
      lit ∈ exGroundClause_G2)

/-- Every literal in the union of the conjugated C1 subset and the selected
    C2 singleton has the common image P(a,a) under that same substitution. -/
@[blueprint "chap8__example_8_3_1"]
theorem exUnificationCommonImage
    (lit : FOLiteral exClauseFormLang rfl)
    (h : lit ∈ exUnificationLeft.map
      (FOLiteral.conjugate (L := exClauseFormLang) rfl) ++
      exUnificationRight) :
    exLiteralSubst exUnificationSubst lit =
      .pos (exPred_P exSkolemConst_a exSkolemConst_a)

/-- Unfold a finite ground graph at a vertex. Each recursive call follows
    a premise occurrence and decreases the stored rank; sharing becomes
    repeated occurrences in the resulting finite tree. -/
def groundGraphUnfold {L : Language} (hNoEq : L.withoutEquality)
    (g : ResolutionGraphCore (FOClause L hNoEq) (FOLiteral L hNoEq))
    (v : Fin g.size) : FOResolutionTree L hNoEq :=
  match hs : g.step v with
  | none => .axiom_ (g.label v)
  | some (left, right, pivot) =>
    .resolve (groundGraphUnfold hNoEq g left)
      (groundGraphUnfold hNoEq g right) pivot
termination_by g.rank v
decreasing_by
  · exact (g.rankDecreases v left right pivot hs).1
  · exact (g.rankDecreases v left right pivot hs).2

/-- The eight displayed vertices: G1–G4, the three intermediate
    resolvents, and the empty root. Vertex identity is independent of labels. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundGraphLabel (v : Fin 8) : FOClause exClauseFormLang rfl :=
  match v.val with
  | 0 => exGroundClause_G1
  | 1 => exGroundClause_G2
  | 2 => exGroundClause_G3
  | 3 => exGroundClause_G4
  | 4 => [.pos (exPred_P exSkolemConst_a exGroundTerm_fa)]
  | 5 => [.pos (exPred_P exGroundTerm_fa exSkolemConst_a)]
  | 6 => [.neg (exPred_P exSkolemConst_a exGroundTerm_fa)]
  | _ => []

/-- The four ordered inference steps. Both steps 4 and 5 use vertex 0,
    the single G1 leaf; the final root is vertex 7. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundGraphStep (v : Fin 8) :
    Option (Fin 8 × Fin 8 × FOLiteral exClauseFormLang rfl) :=
  match v.val with
  | 4 => some (1, 0, .pos (exPred_P exSkolemConst_a exSkolemConst_a))
  | 5 => some (2, 0, .pos (exPred_P exSkolemConst_a exSkolemConst_a))
  | 6 => some (5, 3, .pos (exPred_P exGroundTerm_fa exSkolemConst_a))
  | 7 => some (4, 6, .pos (exPred_P exSkolemConst_a exGroundTerm_fa))
  | _ => none

/-- Example 8.3.1's actual finite shared graph, with root 7.
    Numerical vertex rank certifies acyclicity. -/
@[blueprint "chap8__example_8_3_1"]
abbrev exGroundGraph :
    ResolutionGraphCore (FOClause exClauseFormLang rfl)
      (FOLiteral exClauseFormLang rfl) where
  size := 8
  root := 7
  label := exGroundGraphLabel
  step := exGroundGraphStep
  rank := Fin.val
  rankDecreases := by simp [exGroundGraphStep, Fin.forall_fin_succ]
  rooted := by simp [exGroundGraphStep, Fin.forall_fin_succ, Fin.exists_fin_succ]

/-- The displayed graph has exactly four inference vertices. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundGraph_inferenceVertices :
    (List.finRange exGroundGraph.size).filter
      (fun v => (exGroundGraph.step v).isSome) = [4, 5, 6, 7]

/-- G1 is one vertex, referenced by the two distinct first resolution steps. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundGraph_shared_G1 :
    exGroundGraph.label 0 = exGroundClause_G1 ∧
    exGroundGraph.step 4 =
      some (1, 0, .pos (exPred_P exSkolemConst_a exSkolemConst_a)) ∧
    exGroundGraph.step 5 =
      some (2, 0, .pos (exPred_P exSkolemConst_a exSkolemConst_a))

/-- The tree of premise occurrences below a displayed graph vertex. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundGraphUnfoldAt (v : Fin 8) : FOResolutionTree exClauseFormLang rfl :=
  groundGraphUnfold (L := exClauseFormLang) rfl exGroundGraph v

/-- Every stored graph label is certified by the corresponding ground
    resolution subtree, including all four inference vertices. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundGraph_labels :
    ∀ v : Fin 8, (exGroundGraphUnfoldAt v).labelSpec
      (L := exClauseFormLang) rfl (exGroundGraph.label v)

/-- Unfolding the displayed shared graph at its empty-clause root. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundGraphUnfold : FOResolutionTree exClauseFormLang rfl :=
  exGroundGraphUnfoldAt exGroundGraph.root

/-- The actual graph unfolding recovers the existing four-step refutation
    tree, duplicating the shared G1 occurrence only in the tree presentation. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundGraph_unfold :
    exGroundGraphUnfold = exGroundResolution_refutation

/-- The displayed graph's unfolding is a certified refutation from G1–G4. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundGraph_refutation :
    exGroundGraphUnfold.isRefutation (L := exClauseFormLang) rfl
      (fun c => c ∈ [exGroundClause_G1, exGroundClause_G2,
        exGroundClause_G3, exGroundClause_G4])

/-- The four displayed ground instances form an unsatisfiable finite set. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundInstances_unsatisfiable :
    GroundClauseSet.isUnsatisfiable (L := exClauseFormLang) rfl
      [exGroundClause_G1, exGroundClause_G2, exGroundClause_G3, exGroundClause_G4]

/-- The original sentence A of Example 8.2.1 is valid. Its concrete
    negation-to-clause conversion, the four instance equations, and the
    displayed empty-root refutation supply the ground-instance witness. -/
@[attach_debt, blueprint "chap8__example_8_2_1"]
theorem exClauseOriginal_valid :
    Formula.isValid exClauseOriginal

/-- Every admissible fair ground run on an unsatisfiable sentence B reaches
    a finite prefix with a positive test and a certified ground refutation.
    Normalization, the input-plus-Skolem ground universe, and the reached
    prefixes are those of this same run on B. No successful prefix or
    refutation is assumed. This is the eventual-success specification;
    executable normalization, enumeration and testing remain deferred. -/
@[attach_debt, blueprint "chap8__lemma_8_3_1"]
theorem ThreeStepProcedure.eventualSuccess
    {L : Language} {hNoEq : L.withoutEquality} {B : FormulaN L}
    (run : ThreeStepProcedure L hNoEq B) (hUnsat : Formula.isUnsatisfiable B) :
    ∃ (n : Nat) (T : FOResolutionTree (GroundRunLanguage run.normalization.skolem) hNoEq),
      run.reached n ∧ run.test n = true ∧
        T.isRefutation (L := GroundRunLanguage run.normalization.skolem) hNoEq
          (fun C => C ∈ groundRunPrefix run.enumeration n)

/-- A compound instance of this input's actual fresh Skolem form, with all
    instantiating terms in its input-plus-Skolem ground universe. -/
@[blueprint "chap8__definition_8_2_1"]
def CompoundInstanceAdmissible {L : Language} (B : FormulaN L)
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (ci : LCS.Herbrand.SHGTheorem.CInstance (GroundRunLanguage S)) : Prop :=
  ci.source = groundRunLiftFormula (LCS.Herbrand.SHGTheorem.skolemForm S) ∧
    ci.WellFormed ∧
    (∀ t ∈ ci.closedTerms, GroundRunTerm B S t) ∧
    LCS.FirstOrder.SemanticsN.isQuantifierFree ci.toFormula ∧
    FormulaN.isClosed ci.toFormula

/-- Relational sequential testing of compound instances of the same sentence.
    `test C k b` means that the validity test of ¬C returns b after k local
    steps. Only a finite negative result advances to the next instance.
    Equality-free QF tests terminate; no such law is imposed with equality.
    The enumerator and tests are supplied data, not implemented algorithms. -/
@[blueprint "chap8__definition_8_2_1"]
structure CompoundInstanceSequentialRun (L : Language) (B : FormulaN L) where
  inputClosed : FormulaN.isClosed B
  skolem : LCS.Herbrand.SHGTheorem.SkolemSpec L
  sameInput : skolem.source = groundRunNormalizedInput B
  normalizationCorrect : Formula.isUnsatisfiable B ↔
    Formula.isUnsatisfiable (groundRunLiftFormula (LCS.Herbrand.SHGTheorem.skolemForm skolem))
  enumeration : Nat → Option (LCS.Herbrand.SHGTheorem.CInstance (GroundRunLanguage skolem))
  origin : ∀ n ci, enumeration n = some ci → CompoundInstanceAdmissible B skolem ci
  fair : ∀ ci, CompoundInstanceAdmissible B skolem ci →
    ∃ n other, enumeration n = some other ∧ other.toFormula = ci.toFormula
  exhausted : ∀ n, enumeration n = none → enumeration (n + 1) = none
  test : FormulaN (GroundRunLanguage skolem) → Nat → Bool → Prop
  testSound : ∀ ci, CompoundInstanceAdmissible B skolem ci → ∀ k b,
    test ci.toFormula k b →
      (b = true ↔ Formula.isValid (.neg ci.toFormula))
  equalityFreeTotal : L.withoutEquality → ∀ ci,
    CompoundInstanceAdmissible B skolem ci → ∃ k b, test ci.toFormula k b
  reached : Nat → Nat → Prop
  initial : ∀ time, reached 0 time ↔ time = 0
  next : ∀ n time, reached (n + 1) time ↔
    ∃ start ci steps, reached n start ∧ enumeration n = some ci ∧
      test ci.toFormula steps false ∧ time = start + steps + 1

/-- The exact validity-search input for the negation of a compound instance. -/
@[blueprint "chap8__definition_8_2_1"]
def compoundNegationInput {L : Language} (C : FormulaN L) :
    LCS.FirstOrder.Gentzen.InfSequentN L :=
  LCS.FirstOrder.Gentzen.InfSequentN.ofSequent ⟨[], [.neg C]⟩

/-- Fixed admissible enumerations for the named equality search on ¬C. -/
@[blueprint "chap8__definition_8_2_1"]
structure EqualityNegationSearch {L : Language} (hEq : L.hasEquality = true)
    (C : FormulaN L) where
  builtFromX : (compoundNegationInput C).builtFromX
  freeBound : LCS.FirstOrder.Gentzen.crossNoFreeBoundInf (compoundNegationInput C)
  enumeration : LCS.FirstOrder.Completeness.Search.SearchEnumeration (compoundNegationInput C)
  equalityEnumeration : LCS.FirstOrder.Equality.Search.EqEnumeration hEq (compoundNegationInput C)

/-- A finite finished round of the named equality search, not an arbitrary
    termination oracle or a decision procedure for equality. -/
@[blueprint "chap8__definition_8_2_1"]
def EqualityNegationSearch.finishes {L : Language} {hEq : L.hasEquality = true}
    {C : FormulaN L} (search : EqualityNegationSearch hEq C) (k : Nat) : Prop :=
  LCS.FirstOrder.Equality.Search.allFinished hEq
    (LCS.FirstOrder.Equality.Search.searchEq hEq (compoundNegationInput C)
      search.builtFromX search.freeBound search.enumeration search.equalityEnumeration k)

/-- Each compound-instance test uses one fixed admissible run of the named
    equality proof search on its negation. That search accepts at a finished
    round and supplies no negative answer merely from a nonfinished round. -/
@[blueprint "chap8__definition_8_2_1"]
def UsesSequentialEqualitySearch {L : Language} {B : FormulaN L}
    (run : CompoundInstanceSequentialRun L B) (hEq : L.hasEquality = true) : Prop :=
  ∀ n ci, run.enumeration n = some ci →
    ∃ search : EqualityNegationSearch (L := GroundRunLanguage run.skolem) hEq ci.toFormula,
      ∀ k b, run.test ci.toFormula k b ↔ b = true ∧ search.finishes k

/-- For an unsatisfiable equality-free input, sequential testing reaches a
    compound instance whose negation is valid and accepts it in finite time.
    The original input, normalization and enumeration are those of this run.
    Uniform executable enumeration and decision procedures remain deferred. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem compoundInstanceSearch_eventually_finds_valid_negation
    {L : Language} (hNoEq : L.withoutEquality) {B : FormulaN L}
    (run : CompoundInstanceSequentialRun L B) (hUnsat : Formula.isUnsatisfiable B) :
    ∃ n time ci steps, run.reached n time ∧ run.enumeration n = some ci ∧
      run.test ci.toFormula steps true ∧ Formula.isValid (.neg ci.toFormula)

/-- There is an unsatisfiable equality input whose same sequential run reaches
    a satisfiable, equality-containing QF compound instance C. The named search
    on ¬C has no finished round. This is an existential search obstruction,
    not undecidability of quantifier-free equality. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem equalitySearch_blocking_instance :
    ∃ (L : Language) (hEq : L.hasEquality = true) (B : FormulaN L)
      (run : CompoundInstanceSequentialRun L B) (n time : Nat)
      (ci : LCS.Herbrand.SHGTheorem.CInstance (GroundRunLanguage run.skolem)),
      Formula.isUnsatisfiable B ∧ UsesSequentialEqualitySearch run hEq ∧
      run.reached n time ∧ run.enumeration n = some ci ∧
      CompoundInstanceAdmissible B run.skolem ci ∧
      ¬ Formula.isUnsatisfiable ci.toFormula ∧ ¬ Formula.isValid (.neg ci.toFormula) ∧
      ¬ LCS.FirstOrder.SemanticsN.formulaNoEq ci.toFormula ∧
      ∃ search : EqualityNegationSearch (L := GroundRunLanguage run.skolem) hEq ci.toFormula,
        (∀ k b, run.test ci.toFormula k b ↔ b = true ∧ search.finishes k) ∧
        ∀ k, ¬ search.finishes k

/-- The very same reached compound instance with a divergent equality search
    prevents all later instances from being reached, even for unsatisfiable B.
    Together with equalitySearch_blocking_instance this gives a possible
    sequential stall; it makes no claim about other equality algorithms. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem sequentialEqualitySearch_may_stall
    {L : Language} (hEq : L.hasEquality = true) {B : FormulaN L}
    (run : CompoundInstanceSequentialRun L B) (hUnsat : Formula.isUnsatisfiable B)
    (n time : Nat) (ci : LCS.Herbrand.SHGTheorem.CInstance (GroundRunLanguage run.skolem))
    (hReached : run.reached n time) (hEntry : run.enumeration n = some ci)
    (search : EqualityNegationSearch (L := GroundRunLanguage run.skolem) hEq ci.toFormula)
    (hTest : ∀ k b, run.test ci.toFormula k b ↔ b = true ∧ search.finishes k)
    (hDiverges : ∀ k, ¬ search.finishes k) :
    (∀ k b, ¬ run.test ci.toFormula k b) ∧
      ∀ m later, n < m → ¬ run.reached m later


/-- A supplied unsatisfiability tester for equality-free QF formulae in its
    declared domain. Every test terminates with a correct Boolean answer;
    the relation records a finite local duration, not an executable decider. -/
@[blueprint "chap8__definition_8_2_1"]
structure QFTesterSpec (L : Language) (hNoEq : L.withoutEquality)
    (domain : FormulaN L → Prop) where
  result : FormulaN L → Nat → Bool → Prop
  total : ∀ C, LCS.FirstOrder.SemanticsN.isQuantifierFree C → domain C →
    ∃ steps answer, result C steps answer
  correct : ∀ C, LCS.FirstOrder.SemanticsN.isQuantifierFree C → domain C →
    ∀ steps answer, result C steps answer →
      (answer = true ↔ Formula.isUnsatisfiable C)

/-- Recompute sequential reached stages for the replacement tester. Each
    advance consumes the same next instance and a finite negative result. -/
@[blueprint "chap8__definition_8_2_1"]
def qfTesterReached {L : Language} {hNoEq : L.withoutEquality}
    {domain : FormulaN L → Prop} (tester : QFTesterSpec L hNoEq domain)
    (enumeration : Nat → Option (LCS.Herbrand.SHGTheorem.CInstance L)) : Nat → Nat → Prop
  | 0, time => time = 0
  | n + 1, time => ∃ start ci steps,
      qfTesterReached tester enumeration n start ∧ enumeration n = some ci ∧
        tester.result ci.toFormula steps false ∧ time = start + steps + 1

/-- A formula is unsatisfiable precisely when its negation is valid. -/
theorem qfTester_unsat_iff_valid_neg {L : Language} (C : FormulaN L) :
    Formula.isUnsatisfiable C ↔ Formula.isValid (.neg C) := by
  constructor
  · intro h M s hc
    exact h ⟨M, s, hc⟩
  · intro h ⟨M, s, hc⟩
    exact h M s hc

/-- Replace a run's tester, retaining its exact original input, fresh
    normalization and fair enumeration. The replacement domain must cover
    every admissible compound instance; its own durations determine reachability. -/
@[blueprint "chap8__definition_8_2_1"]
def CompoundInstanceSequentialRun.withTester {L : Language} {B : FormulaN L}
    (run : CompoundInstanceSequentialRun L B) (hNoEq : L.withoutEquality)
    {domain : FormulaN (GroundRunLanguage run.skolem) → Prop}
    (tester : QFTesterSpec (GroundRunLanguage run.skolem) hNoEq domain)
    (hDomain : ∀ ci, CompoundInstanceAdmissible B run.skolem ci → domain ci.toFormula) :
    CompoundInstanceSequentialRun L B where
  inputClosed := run.inputClosed
  skolem := run.skolem
  sameInput := run.sameInput
  normalizationCorrect := run.normalizationCorrect
  enumeration := run.enumeration
  origin := run.origin
  fair := run.fair
  exhausted := run.exhausted
  test := tester.result
  testSound := by
    intro ci hc k b hb
    exact (tester.correct ci.toFormula hc.2.2.2.1 (hDomain ci hc) k b hb).trans
      (qfTester_unsat_iff_valid_neg ci.toFormula)
  equalityFreeTotal := by
    intro _ ci hc
    exact tester.total ci.toFormula hc.2.2.2.1 (hDomain ci hc)
  reached := qfTesterReached tester run.enumeration
  initial := fun _ => Iff.rfl
  next := fun _ _ => Iff.rfl

/-- Any correct total QF tester whose domain covers the compound instances
    can replace the original tester and retains same-input eventual discovery. -/
@[blueprint "chap8__definition_8_2_1"]
theorem sequentialRun_with_correct_tester
    {L : Language} {B : FormulaN L} (run : CompoundInstanceSequentialRun L B)
    (hNoEq : L.withoutEquality)
    {domain : FormulaN (GroundRunLanguage run.skolem) → Prop}
    (tester : QFTesterSpec (GroundRunLanguage run.skolem) hNoEq domain)
    (hDomain : ∀ ci, CompoundInstanceAdmissible B run.skolem ci → domain ci.toFormula)
    (hUnsat : Formula.isUnsatisfiable B) :
    let configured := run.withTester hNoEq tester hDomain
    ∃ n time ci steps, configured.reached n time ∧ configured.enumeration n = some ci ∧
      configured.test ci.toFormula steps true ∧ Formula.isValid (.neg ci.toFormula)

/-- Structural clause presentation: literal leaves and disjunction append.
    This is a relation on the actual formula, not an arbitrary equisatisfiable set. -/
@[blueprint "chap8__definition_8_2_1"]
inductive QFClausePresentation {L : Language} (hNoEq : L.withoutEquality) :
    FormulaN L → FOClause L hNoEq → Prop where
  | positive (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L) :
      QFClausePresentation hNoEq (.predN P ts) [.pos (.predN P ts)]
  | negative (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L) :
      QFClausePresentation hNoEq (.neg (.predN P ts)) [.neg (.predN P ts)]
  | disjunction {A B C D} : QFClausePresentation hNoEq A C →
      QFClausePresentation hNoEq B D → QFClausePresentation hNoEq (.disj A B) (C ++ D)

/-- Structural finite CNF presentation of the actual compound instance. -/
@[blueprint "chap8__definition_8_2_1"]
inductive QFCNFPresentation {L : Language} (hNoEq : L.withoutEquality) :
    FormulaN L → List (FOClause L hNoEq) → Prop where
  | clause {A C} : QFClausePresentation hNoEq A C → QFCNFPresentation hNoEq A [C]
  | conjunction {A B S T} : QFCNFPresentation hNoEq A S →
      QFCNFPresentation hNoEq B T → QFCNFPresentation hNoEq (.conj A B) (S ++ T)

/-- The finite-resolution option applies when the closed compound instance
    is already in CNF; no conversion of arbitrary QF syntax is assumed. -/
@[blueprint "chap8__definition_8_2_1"]
def QFCNFDomain {L : Language} (hNoEq : L.withoutEquality) (C : FormulaN L) : Prop :=
  FormulaN.isClosed C ∧ ∃ clauses, QFCNFPresentation hNoEq C clauses

/-- The named equality-free search option tests ∅ ⇒ ¬C. Its finite finished
    tree gives a positive answer exactly when all its leaves are axioms. -/
@[blueprint "chap8__definition_8_2_1"]
def QFTesterUsesSearch {L : Language} {hNoEq : L.withoutEquality}
    (tester : QFTesterSpec L hNoEq (fun C => FormulaN.isClosed C)) : Prop :=
  ∀ C, LCS.FirstOrder.SemanticsN.isQuantifierFree C → FormulaN.isClosed C →
    ∃ (hq : (compoundNegationInput C).builtFromX)
      (hFB : LCS.FirstOrder.Gentzen.crossNoFreeBoundInf (compoundNegationInput C))
      (enum : LCS.FirstOrder.Completeness.Search.SearchEnumeration (compoundNegationInput C)),
      ∀ k b, tester.result C k b ↔
        LCS.FirstOrder.Completeness.Search.allFinished hNoEq
          (LCS.FirstOrder.Completeness.Search.search51 hNoEq (compoundNegationInput C) hq hFB enum k) ∧
        (b = true ↔ ∀ leaf ∈
          (LCS.FirstOrder.Completeness.Search.search51 hNoEq (compoundNegationInput C) hq hFB enum k).tree.forget.leaves,
          LCS.FirstOrder.Gentzen.isAxiom leaf)

/-- The finite-resolution alternative presents that same CNF instance as
    clauses, encodes its finitely occurring atoms injectively, and certifies
    positive results by Chapter 4 resolution DAGs. Termination/negative answers
    are supplied by the common tester contract; saturation is not implemented. -/
@[blueprint "chap8__definition_8_2_1"]
def QFTesterUsesFiniteResolution {L : Language} {hNoEq : L.withoutEquality}
    (tester : QFTesterSpec L hNoEq (QFCNFDomain hNoEq)) : Prop :=
  ∀ C, QFCNFDomain hNoEq C →
    ∃ (clauses : List (FOClause L hNoEq)) (encode : FOAtom L hNoEq → Nat),
      QFCNFPresentation hNoEq C clauses ∧
      (∀ a ∈ groundClauseSetAtoms hNoEq clauses, ∀ b ∈ groundClauseSetAtoms hNoEq clauses,
        encode a = encode b → a = b) ∧
      (∀ k, tester.result C k true → ∃ D : ResolutionDAG,
        D.isRefutationFor (groundClauseSetToProp hNoEq encode clauses)) ∧
      ((∃ D : ResolutionDAG, D.isRefutationFor (groundClauseSetToProp hNoEq encode clauses)) ↔
        ∃ k, tester.result C k true)

/-- The named search has a correct-tester specification on closed equality-free
    QF instances. This asserts availability of the specification, not a uniform
    executable search/decider implementation. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem qfSearchTester_available {L : Language} (hNoEq : L.withoutEquality) :
    ∃ tester : QFTesterSpec L hNoEq (fun C => FormulaN.isClosed C), QFTesterUsesSearch tester

/-- Finite resolution supplies the alternative specification when each tested
    compound instance is CNF. Executable enumeration/saturation stays deferred. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem qfFiniteResolutionTester_available {L : Language} (hNoEq : L.withoutEquality) :
    ∃ tester : QFTesterSpec L hNoEq (QFCNFDomain hNoEq), QFTesterUsesFiniteResolution tester

/-- A concrete universal ranked signature: numbered constants and numbered
    function/predicate symbols at every finite arity, with identity equality.
    Any countable first-order signature embeds by arity-preserving renaming. -/
@[blueprint "chap8__definition_8_2_1"]
def GeneralFOLanguage : Language where
  constSymbols := Nat
  funSymbols := Nat × Nat
  funArity := Prod.snd
  predSymbols := Nat × Nat
  predArity := Prod.snd
  hasEquality := true

/-- Natural-number codes for general first-order syntax; malformed numbers
    are rejected by the decoder and excluded from both semantic sets. -/
@[blueprint "chap8__definition_8_2_1"]
abbrev GeneralFOCode := Nat

/-- Cantor pairing, used only as effective coding machinery. -/
def generalFOPair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- Locate the diagonal by successive triangular-number subtraction. -/
def generalFOUnpairAux : Nat → Nat → Nat → Nat × Nat
  | 0, diagonal, rest => (diagonal - rest, rest)
  | fuel + 1, diagonal, rest =>
      if rest < diagonal + 1 then (diagonal - rest, rest)
      else generalFOUnpairAux fuel (diagonal + 1) (rest - (diagonal + 1))

def generalFOUnpair (n : Nat) : Nat × Nat := generalFOUnpairAux (n + 1) 0 n

def generalFOEncodeList : List Nat → Nat
  | [] => 0
  | x :: xs => generalFOPair x (generalFOEncodeList xs) + 1

def generalFODecodeList : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | 0, _ + 1 => none
  | fuel + 1, n + 1 => do
      let pair := generalFOUnpair n
      let rest ← generalFODecodeList fuel pair.2
      pure (pair.1 :: rest)

/-- Effective term encoding. Function arities are the lengths of their
    encoded argument lists, so symbol identity retains both number and rank. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFOEncodeTerm : Term GeneralFOLanguage → Nat
  | .var x => generalFOPair 0 x + 1
  | .const c => generalFOPair 1 c + 1
  | .func f ts => generalFOPair 2
      (generalFOPair f.1 (generalFOEncodeList (List.ofFn (fun i => generalFOEncodeTerm (ts i))))) + 1

/-- Effective tagged encoding of all normalized first-order constructors,
    retaining variable names, symbol ranks, equality and both quantifiers. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFOEncode : FormulaN GeneralFOLanguage → GeneralFOCode
  | .predN P ts => generalFOPair 0
      (generalFOPair P.1 (generalFOEncodeList (List.ofFn (fun i => generalFOEncodeTerm (ts i))))) + 1
  | .eq_ _ t u => generalFOPair 1 (generalFOPair (generalFOEncodeTerm t) (generalFOEncodeTerm u)) + 1
  | .neg A => generalFOPair 2 (generalFOEncode A) + 1
  | .conj A B => generalFOPair 3 (generalFOPair (generalFOEncode A) (generalFOEncode B)) + 1
  | .disj A B => generalFOPair 4 (generalFOPair (generalFOEncode A) (generalFOEncode B)) + 1
  | .impl A B => generalFOPair 5 (generalFOPair (generalFOEncode A) (generalFOEncode B)) + 1
  | .all x A => generalFOPair 6 (generalFOPair x (generalFOEncode A)) + 1
  | .ex x A => generalFOPair 7 (generalFOPair x (generalFOEncode A)) + 1

/-- A structurally terminating term parser; fuel bounds syntax depth, not
    validity search. The public decoder supplies the code-dependent bound. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFODecodeTerm : Nat → Nat → Option (Term GeneralFOLanguage)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 => do
      let (tag, payload) := generalFOUnpair code
      match tag with
      | 0 => pure (.var payload)
      | 1 => pure (.const payload)
      | 2 =>
          let (name, args) := generalFOUnpair payload
          let codes ← generalFODecodeList fuel args
          let ts ← codes.mapM (generalFODecodeTerm fuel)
          pure (.func (name, ts.length) ts.get)
      | _ => none

/-- Effective formula parser for the fixed constructor tags. Unknown tags
    and ill-formed subterms return none. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFODecodeAux : Nat → Nat → Option (FormulaN GeneralFOLanguage)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 => do
      let (tag, payload) := generalFOUnpair code
      let (left, right) := generalFOUnpair payload
      match tag with
      | 0 =>
          let codes ← generalFODecodeList fuel right
          let ts ← codes.mapM (generalFODecodeTerm fuel)
          pure (.predN (left, ts.length) ts.get)
      | 1 => pure (.eq_ rfl (← generalFODecodeTerm fuel left) (← generalFODecodeTerm fuel right))
      | 2 => pure (.neg (← generalFODecodeAux fuel payload))
      | 3 => pure (.conj (← generalFODecodeAux fuel left) (← generalFODecodeAux fuel right))
      | 4 => pure (.disj (← generalFODecodeAux fuel left) (← generalFODecodeAux fuel right))
      | 5 => pure (.impl (← generalFODecodeAux fuel left) (← generalFODecodeAux fuel right))
      | 6 => pure (.all left (← generalFODecodeAux fuel right))
      | 7 => pure (.ex left (← generalFODecodeAux fuel right))
      | _ => none

/-- Decode with a bound derived from the input code, not a fixed cutoff. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFODecode (code : GeneralFOCode) : Option (FormulaN GeneralFOLanguage) :=
  generalFODecodeAux (code + 1) code

/-- The concrete syntactic operation of prefixing negation to a formula code. -/
@[blueprint "chap8__definition_8_2_1"]
def generalFONegation (code : GeneralFOCode) : GeneralFOCode := generalFOPair 2 code + 1

/-- Validity set of the general encoded problem, rejecting malformed inputs. -/
@[blueprint "chap8__definition_8_2_1"]
def GeneralFOCode.Valid (code : GeneralFOCode) : Prop :=
  ∃ A, generalFODecode code = some A ∧ Formula.isValid A

/-- Unsatisfiability set of the same encoded problem. -/
@[blueprint "chap8__definition_8_2_1"]
def GeneralFOCode.Unsatisfiable (code : GeneralFOCode) : Prop :=
  ∃ A, generalFODecode code = some A ∧ Formula.isUnsatisfiable A

/-- A total recursive Boolean decider, using chapter 7's unbounded partial-
    recursive convergence semantics. Every natural input terminates; every
    output is 0 or 1, and 1 means membership. Classical Decidable is not used. -/
@[blueprint "chap8__definition_8_2_1"]
def TotalRecursiveDecider (P : Nat → Prop)
    (program : LCS.Herbrand.PrimRecursive.PartialRec 1) : Prop :=
  program.isTotal ∧ ∀ n value, program.converges (fun _ => n) value →
    (value = 0 ∨ value = 1) ∧ (value = 1 ↔ P n)

/-- Actual symbol-renaming data, with injectivity in each syntactic sort. -/
@[blueprint "chap8__definition_8_2_1"]
structure GeneralFOEmbedding (L : Language) where
  constants : L.constSymbols → Nat
  functions : L.funSymbols → Nat
  predicates : L.predSymbols → Nat
  constantsInjective : Function.Injective constants
  functionsInjective : Function.Injective functions
  predicatesInjective : Function.Injective predicates

/-- Arity-preserving structural embedding of terms in the universal signature. -/
@[blueprint "chap8__definition_8_2_1"]
def GeneralFOEmbedding.term {L : Language} (e : GeneralFOEmbedding L) : Term L → Term GeneralFOLanguage
  | .var x => .var x
  | .const c => .const (e.constants c)
  | .func f ts => .func (e.functions f, L.funArity f) (fun i => e.term (ts i))

/-- Structural formula embedding, preserving logical constructors and equality. -/
@[blueprint "chap8__definition_8_2_1"]
def GeneralFOEmbedding.formula {L : Language} (e : GeneralFOEmbedding L) : FormulaN L → FormulaN GeneralFOLanguage
  | .predN P ts => .predN (e.predicates P, L.predArity P) (fun i => e.term (ts i))
  | .eq_ _ t u => .eq_ rfl (e.term t) (e.term u)
  | .neg A => .neg (e.formula A)
  | .conj A B => .conj (e.formula A) (e.formula B)
  | .disj A B => .disj (e.formula A) (e.formula B)
  | .impl A B => .impl (e.formula A) (e.formula B)
  | .all x A => .all x (e.formula A)
  | .ex x A => .ex x (e.formula A)

/-- Coding adequacy: parsing the effective encoding recovers every formula. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem generalFO_decode_encode (A : FormulaN GeneralFOLanguage) :
    generalFODecode (generalFOEncode A) = some A

/-- The concrete well-formed-code test is recursive in the chapter 7 model. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem generalFO_syntax_recursive :
    ∃ program, TotalRecursiveDecider (fun n => (generalFODecode n).isSome = true) program

/-- Negation on codes is a total recursive operation, not an assumed oracle. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem generalFO_negation_recursive :
    ∃ program : LCS.Herbrand.PrimRecursive.PartialRec 1,
      program.isTotal ∧ ∀ n, program.converges (fun _ => n) (generalFONegation n)

/-- Every textbook countable ranked signature admits the supplied renaming
    data; the structural embedding functions themselves are defined above. -/
@[blueprint "chap8__definition_8_2_1"]
theorem generalFO_embedding_exists (L : FirstOrderLanguage) :
    Nonempty (GeneralFOEmbedding L.toLanguage)

/-- Semantic coding adequacy through actual structural symbol renaming. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem generalFO_embedding_adequate {L : Language} (e : GeneralFOEmbedding L) (A : FormulaN L) :
    (Formula.isValid A ↔ GeneralFOCode.Valid (generalFOEncode (e.formula A))) ∧
    (Formula.isUnsatisfiable A ↔ GeneralFOCode.Unsatisfiable (generalFOEncode (e.formula A)))

/-- Church's general unsatisfiability claim: no total recursive decider for
    this effective general syntax. This does not deny positive semidecision
    or assert undecidability of every restricted signature or fragment. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem church_unsatisfiability_undecidable :
    ¬ ∃ program, TotalRecursiveDecider GeneralFOCode.Unsatisfiable program

/-- Church's corresponding general validity claim on the same code domain. -/
@[attach_debt, blueprint "chap8__definition_8_2_1"]
theorem church_validity_undecidable :
    ¬ ∃ program, TotalRecursiveDecider GeneralFOCode.Valid program

end LCS.FOResolution.GroundResolution
