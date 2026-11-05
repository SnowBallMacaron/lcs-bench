import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.ResolutionTrees
import LCS.FOResolution.Method.GroundExtension
import Attach
import LCS.FOResolution.Method.ProofsStamp

/-! # FOResolution.Method
    Formalization of Chapter 8, Section 8.5.1.
    Separating substitutions, resolvents, and resolution DAGs
    for first-order logic.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- The motivating literal-subset assertion of §8.4.1: for disjoint-variable
    clauses and the given substitution whose moved support is exactly their
    variable union, complementary image literals have nonempty source subsets.
    The C-side witness contains the unbarred literals: their conjugates belong
    to C. Every literal in either witness has the same image Q under sigma.
    Lists represent finite sets through membership; witnesses need not contain
    all preimages. Exact support already enforces finite support. -/
@[attach_debt, blueprint "chap8__definition_8_4_2"]
theorem unification_literal_subset_witnesses {L : Language}
    (hNoEq : L.withoutEquality) (B C : FOClause L hNoEq)
    (sigma : Nat → Term L) (Q : FOLiteral L hNoEq)
    (hDisjoint : Set.inter (clauseFV hNoEq B) (clauseFV hNoEq C) = Set.empty)
    (hSupport : (fun x => sigma x ≠ Term.var x) =
      Set.union (clauseFV hNoEq B) (clauseFV hNoEq C))
    (hB : Q ∈ substLits hNoEq sigma B)
    (hC : FOLiteral.conjugate hNoEq Q ∈ substLits hNoEq sigma C) :
    ∃ BS CS : List (FOLiteral L hNoEq),
      BS ≠ [] ∧ CS ≠ [] ∧
      IsSublist BS B ∧ IsSublist (LitSetConjugate hNoEq CS) C ∧
      (∀ lit, lit ∈ BS → substLit hNoEq sigma lit = Q) ∧
      (∀ lit, lit ∈ CS → substLit hNoEq sigma lit = Q)

-- ===================================================================
-- Definition 8.5.3: First-order resolution tree and DAG
-- ===================================================================


/-- Definition 8.5.3: A resolution step stores its ordered premise occurrences,
    selected literals, separating pair, and substitution giving the resolvent.
    The two premises may name the same vertex. -/
@[blueprint "chap8__definition_8_5_3"]
structure FOResolutionDAGStep (L : Language) (hNoEq : L.withoutEquality)
    (size : Nat) where
  left : Fin size
  right : Fin size
  resolvedA : FOClause L hNoEq
  resolvedB : FOClause L hNoEq
  rho : Nat → Term L
  rho' : Nat → Term L
  sigma : Nat → Term L

/-- Definition 8.5.3: Follow ordered premises in a resolution DAG;
    false selects the left occurrence and true selects the right occurrence. -/
@[blueprint "chap8__definition_8_5_3"]
def foResolutionFollow {L : Language} {hNoEq : L.withoutEquality} {size : Nat}
    (step : Fin size → Option (FOResolutionDAGStep L hNoEq size))
    (v : Fin size) : List Bool → Option (Fin size)
  | [] => some v
  | side :: path => do
      let s ← step v
      foResolutionFollow step (if side then s.right else s.left) path

/-- Definition 8.5.3: A finite rooted resolution DAG component. Its vertices
    carry clauses and its nonleaf vertices carry legal resolvents of their
    ordered premises. Rank strictly decreases towards premises, and every
    vertex occurs below the root. Shared premises retain their vertex identity.
    The input-clause condition is expressed by `isResolutionDAGFor`. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
structure FOResolutionDAGCore (L : Language) (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] where
  size : Nat
  root : Fin size
  label : Fin size → FOClause L hNoEq
  step : Fin size → Option (FOResolutionDAGStep L hNoEq size)
  rank : Fin size → Nat
  rankDecreases : ∀ v s, step v = some s →
    rank s.left < rank v ∧ rank s.right < rank v
  rooted : ∀ v, ∃ path, foResolutionFollow step root path = some v
  lawful : ∀ v s, step v = some s →
    IsResolventVia hNoEq (label v) (label s.left) (label s.right)
      s.resolvedA s.resolvedB s.rho s.rho' s.sigma

/-- Definition 8.5.3: The input S of a resolution DAG is a finite set of
    clauses, represented extensionally by membership in a finite list. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionFiniteInput {L : Language} {hNoEq : L.withoutEquality}
    (S : FOClause L hNoEq → Prop) : Prop :=
  ∃ clauses : List (FOClause L hNoEq), ∀ C, S C ↔ C ∈ clauses

/-- Definition 8.5.3: A resolution DAG component for finite S has every
    leaf labeled by a clause in S; its internal resolvents are certified. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionDAGCore.isResolutionDAGFor {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAGCore L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  FOResolutionFiniteInput S ∧ ∀ v, D.step v = none → S (D.label v)

/-- Definition 8.5.3: A tree occurrence is selected by its sequence of
    ordered premises, including the empty sequence for the root. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionTree.occurrence {L : Language} {hNoEq : L.withoutEquality} :
    FOResolutionTree L hNoEq → List Bool → Option (FOResolutionTree L hNoEq)
  | T, [] => some T
  | .axiom_ _, _ :: _ => none
  | .resolve left right _ _ _ _ _, side :: path =>
    occurrence (if side then right else left) path

/-- Definition 8.5.3: Unfolding a resolution DAG preserves each ordered
    premise and its inference witnesses. Leaf clauses are unchanged; internal
    resolvent labels agree by literal membership, as clauses are sets. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionDAGCore.UnfoldsAt {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FOLiteral L hNoEq)] (D : FOResolutionDAGCore L hNoEq) :
    FOResolutionTree L hNoEq → Fin D.size → Prop
  | .axiom_ C, v => D.step v = none ∧ C = D.label v
  | .resolve left right A B rho rho' sigma, v =>
    ∃ s, D.step v = some s ∧
      A = s.resolvedA ∧ B = s.resolvedB ∧
      rho = s.rho ∧ rho' = s.rho' ∧ sigma = s.sigma ∧
      (∀ lit, lit ∈ FOResolutionTree.label hNoEq
        (.resolve left right A B rho rho' sigma) ↔ lit ∈ D.label v) ∧
      D.UnfoldsAt left s.left ∧ D.UnfoldsAt right s.right

/-- Definition 8.5.3: The rooted-tree-occurrence quotient presentation of a
    resolution DAG. Following premises maps occurrences onto all vertices;
    two occurrences are identified precisely when they reach the same vertex.
    The unfolding condition preserves labels and ordered resolution steps. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionDAGCore.IsOccurrenceQuotient {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAGCore L hNoEq) (T : FOResolutionTree L hNoEq) : Prop :=
  D.UnfoldsAt T D.root ∧
  ∀ v, ∃ path subtree, T.occurrence path = some subtree ∧
    foResolutionFollow D.step D.root path = some v

/-- Definition 8.5.3: A resolution DAG component for finite S is equivalent
    to an onto rooted-tree-occurrence quotient of a resolution tree for S in
    the existing singleton list presentation. This also covers a leaf root,
    in particular the zero-step refutation when the empty clause belongs to S. -/
@[attach_debt, blueprint "chap8__definition_8_5_3"]
theorem FOResolutionDAGCore.unfolding_iff {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAGCore L hNoEq) (S : FOClause L hNoEq → Prop) :
    D.isResolutionDAGFor S ↔
      FOResolutionFiniteInput S ∧ ∃ T : FOResolutionTree L hNoEq,
        D.IsOccurrenceQuotient T ∧ FOResolutionDAG.isResolutionDAGFor hNoEq [T] S

/-- Definition 8.5.3: A resolution refutation in the singleton tree-list
    presentation of a finite input S gives a finite shared-node resolution DAG
    component with empty root. The given tree presents that component by its
    occurrences, preserving premises and resolvent witnesses. A leaf labeled
    by the empty clause is included as a zero-step refutation. -/
@[attach_debt, blueprint "chap8__definition_8_5_3"]
theorem FOResolutionDAG.toSharedRefutation {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAG L hNoEq) (S : FOClause L hNoEq → Prop)
    (hFinite : FOResolutionFiniteInput S)
    (hRef : FOResolutionDAG.isResolutionRefutation hNoEq D S) :
    ∃ G : FOResolutionDAGCore L hNoEq,
      G.isResolutionDAGFor S ∧ G.label G.root = [] ∧
      ∃ T : FOResolutionTree L hNoEq, D = [T] ∧ G.IsOccurrenceQuotient T

/-- Definition 8.5.3: A finite shared-node resolution DAG component for S
    whose root is the empty clause unfolds to a singleton tree-list resolution
    refutation of S. Its tree occurrences map onto the original component,
    preserving ordered premises and resolvent witnesses, including a leaf root. -/
@[attach_debt, blueprint "chap8__definition_8_5_3"]
theorem FOResolutionDAGCore.toTreeRefutation {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (G : FOResolutionDAGCore L hNoEq) (S : FOClause L hNoEq → Prop)
    (hFor : G.isResolutionDAGFor S) (hEmpty : G.label G.root = []) :
    ∃ T : FOResolutionTree L hNoEq,
      G.IsOccurrenceQuotient T ∧ FOResolutionDAG.isResolutionRefutation hNoEq [T] S

/-- Definition 8.5.3: A finite family of distinct resolution DAG components,
    represented by a list. Distinctness compares vertex counts, roots, clause
    labels and inference data, including ordered premises and resolvent
    witnesses. Rank certificates certify acyclicity of the components.
    The empty list is allowed. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
structure FOResolutionDAGFamily (L : Language) (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] where
  components : List (FOResolutionDAGCore L hNoEq)
  distinct : components.Pairwise (fun G H =>
    ¬ (G.size = H.size ∧ HEq G.root H.root ∧
      HEq G.label H.label ∧ HEq G.step H.step))

/-- Definition 8.5.3: A resolution DAG for finite S is a finite family of
    distinct components whose leaves are labeled by clauses in S. Each
    component certifies legal resolvents at its nonleaf vertices. The empty
    family is a resolution DAG for every finite S. -/
@[blueprint "chap8__definition_8_5_3"]
def FOResolutionDAGFamily.isResolutionDAGFor {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (F : FOResolutionDAGFamily L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  FOResolutionFiniteInput S ∧
    ∀ G, G ∈ F.components → G.isResolutionDAGFor S

/-- Definition 8.5.3: A resolution refutation of S is a resolution DAG for S
    consisting of a single component whose root is labeled by the empty clause.
    This includes a one-vertex leaf component when the empty clause belongs
    to S; no resolution step is required in that case. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
def FOResolutionDAGFamily.isResolutionRefutation {L : Language}
    {hNoEq : L.withoutEquality} [DecidableEq (FOLiteral L hNoEq)]
    (F : FOResolutionDAGFamily L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  F.isResolutionDAGFor S ∧
    ∃ G : FOResolutionDAGCore L hNoEq, F.components = [G] ∧ G.label G.root = []

-- ===================================================================
-- Definition 8.5.2: First-order resolvent
-- ===================================================================

end LCS.FOResolution.Method

namespace LCS.FOResolution.ClauseForm.FOAtomCore

open LCS.FirstOrder.Basic
open LCS.FOResolution.Unification


end LCS.FOResolution.ClauseForm.FOAtomCore

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification


-- ===================================================================
-- Definition 8.5.3 (companion defs): label, leavesFrom, isWellFormed,
-- isResolutionDAGFor, isResolutionRefutation
-- ===================================================================

namespace FOResolutionTree


end FOResolutionTree

namespace FOResolutionDAG


end FOResolutionDAG

-- ===================================================================
-- Theorem 8.5.1 infrastructure: conservative fresh-ground extension
-- ===================================================================


namespace FreshGroundLanguage



end FreshGroundLanguage

namespace FOResolutionTree

open FreshGroundLanguage


end FOResolutionTree

-- ===================================================================
-- Example 8.5.1: Worked resolvent example
-- ===================================================================

/-- Example 8.5.1: The displayed positive literal set for the first pivot choice. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_normalized_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a),
    FOLiteralCore.pos (exPred_P (Term.var 1) (Term.var 4)),
    FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]

/-- Example 8.5.1: Renaming, C-side conjugation, and absolute value give the displayed first set. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_normalize_first :
    LitSetAbs (L := exClauseFormLang) rfl
      (substLits (L := exClauseFormLang) rfl exRes_rho_first exRes_A'_first ++
        substLits (L := exClauseFormLang) rfl exRes_rho'_first (LitSetConjugate (L := exClauseFormLang) rfl exRes_B'_first)) =
      exRes_normalized_first

/-- Example 8.5.1: The displayed first substitution moves exactly its named variables and fixes the others. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_first_equations :
    exRes_sigma_first 2 = Term.var 1 ∧
    exRes_sigma_first 4 = exSkolemConst_a ∧
    (∀ x, x ≠ 2 → x ≠ 4 → exRes_sigma_first x = Term.var x)

/-- Example 8.5.1: The first unifier's common image P(z₁, a). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_common_first : FOLiteral exClauseFormLang rfl :=
  FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a)

/-- Example 8.5.1: The first substitution unifies the displayed literals, has input-bounded finite support, and every finite-support unifier factors through it on all variables by a finite-support substitution. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_first_mgu :
    (∀ lit, lit ∈ exRes_normalized_first →
      substLit (L := exClauseFormLang) rfl exRes_sigma_first lit = exRes_common_first) ∧
    (∀ x, exRes_sigma_first x ≠ Term.var x →
      clauseFV (L := exClauseFormLang) rfl exRes_normalized_first x) ∧
    (∃ support : List Nat, ∀ x, x ∉ support →
      exRes_sigma_first x = Term.var x) ∧
    (∀ tau : Nat → Term exClauseFormLang,
      (∃ support : List Nat, ∀ x, x ∉ support → tau x = Term.var x) →
      (∀ lit, lit ∈ exRes_normalized_first → ∀ lit', lit' ∈ exRes_normalized_first →
        substLit (L := exClauseFormLang) rfl tau lit = substLit (L := exClauseFormLang) rfl tau lit') →
      ∃ theta : Nat → Term exClauseFormLang,
        (∃ support : List Nat, ∀ x, x ∉ support → theta x = Term.var x) ∧
        ∀ x, tau x = termSubstAll (exRes_sigma_first x) theta)

/-- Example 8.5.1: The stored first output is a resolvent via precisely the displayed pivots, separating maps and MGU. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_first_isResolventVia :
    @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _) exRes_C_first exResClause_A exResClause_B
      exRes_A'_first exRes_B'_first
      exRes_rho_first exRes_rho'_first exRes_sigma_first

/-- Example 8.5.1: The displayed positive literal set for the second pivot choice. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_normalized_second : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a),
    FOLiteralCore.pos (exPred_P (Term.var 1) (Term.var 4)),
    FOLiteralCore.pos (exPred_P (Term.var 4) (Term.var 1)),
    FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]

/-- Example 8.5.1: Renaming, C-side conjugation, and absolute value give the displayed second set. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_normalize_second :
    LitSetAbs (L := exClauseFormLang) rfl
      (substLits (L := exClauseFormLang) rfl exRes_rho_second exRes_A'_second ++
        substLits (L := exClauseFormLang) rfl exRes_rho'_second (LitSetConjugate (L := exClauseFormLang) rfl exRes_B'_second)) =
      exRes_normalized_second

/-- Example 8.5.1: The displayed second substitution moves exactly its named variables and fixes the others. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_second_equations :
    exRes_sigma_second 1 = exSkolemConst_a ∧
    exRes_sigma_second 2 = exSkolemConst_a ∧
    exRes_sigma_second 4 = exSkolemConst_a ∧
    (∀ x, x ≠ 1 → x ≠ 2 → x ≠ 4 → exRes_sigma_second x = Term.var x)

/-- Example 8.5.1: The second unifier's common image P(a, a). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_common_second : FOLiteral exClauseFormLang rfl :=
  FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a)

/-- Example 8.5.1: The second substitution unifies the displayed literals, has input-bounded finite support, and every finite-support unifier factors through it on all variables by a finite-support substitution. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_second_mgu :
    (∀ lit, lit ∈ exRes_normalized_second →
      substLit (L := exClauseFormLang) rfl exRes_sigma_second lit = exRes_common_second) ∧
    (∀ x, exRes_sigma_second x ≠ Term.var x →
      clauseFV (L := exClauseFormLang) rfl exRes_normalized_second x) ∧
    (∃ support : List Nat, ∀ x, x ∉ support →
      exRes_sigma_second x = Term.var x) ∧
    (∀ tau : Nat → Term exClauseFormLang,
      (∃ support : List Nat, ∀ x, x ∉ support → tau x = Term.var x) →
      (∀ lit, lit ∈ exRes_normalized_second → ∀ lit', lit' ∈ exRes_normalized_second →
        substLit (L := exClauseFormLang) rfl tau lit = substLit (L := exClauseFormLang) rfl tau lit') →
      ∃ theta : Nat → Term exClauseFormLang,
        (∃ support : List Nat, ∀ x, x ∉ support → theta x = Term.var x) ∧
        ∀ x, tau x = termSubstAll (exRes_sigma_second x) theta)

/-- Example 8.5.1: The stored second output is a resolvent via precisely the displayed pivots, separating maps and MGU. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_second_isResolventVia :
    @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _) exRes_C_second exResClause_A exResClause_B
      exRes_A'_second exRes_B'_second
      exRes_rho_second exRes_rho'_second exRes_sigma_second

/-- Example 8.5.1: Both displayed renaming pairs separate the same parents; x may remain fixed. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_separating_pairs :
    IsSeparatingPair (L := exClauseFormLang) rfl exRes_rho_first exRes_rho'_first exResClause_A exResClause_B ∧
    IsSeparatingPair (L := exClauseFormLang) rfl exRes_rho_second exRes_rho'_second exResClause_A exResClause_B

/-- Example 8.5.1: The two stored outputs are extensionally distinct resolvents of the same parents. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exResolventExample_spec :
    @IsResolvent exClauseFormLang rfl (Classical.typeDecidableEq _) exResolventExample.1 exResClause_A exResClause_B ∧
    @IsResolvent exClauseFormLang rfl (Classical.typeDecidableEq _) exResolventExample.2 exResClause_A exResClause_B ∧
    ¬ (∀ lit, lit ∈ exResolventExample.1 ↔ lit ∈ exResolventExample.2)



/-- Example 8.5.2: The positive unit label U = {P(a,f(a))}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_U : FOClause exClauseFormLang rfl := exRes_C_second

/-- Example 8.5.2: The positive unit label V = {P(f(a),a)}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_V : FOClause exClauseFormLang rfl :=
  [FOLiteralCore.pos (exPred_P
    (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)) exSkolemConst_a)]

/-- Example 8.5.2: The negative unit label W = {neg P(a,f(a))}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_W : FOClause exClauseFormLang rfl :=
  [FOLiteralCore.neg (exPred_P exSkolemConst_a
    (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)))]

/-- Example 8.5.2: The identity substitutions displayed at the inference nodes. -/
@[blueprint "chap8__example_8_5_2"]
def exRefId : Nat → Term exClauseFormLang := Term.var

/-- Example 8.5.2: An internal vertex stores its two premise vertex IDs,
    pivot subsets, separating maps, and unifier. IDs range over the seven
    displayed vertices C1,C2,C3,U,V,W,E in that order. -/
@[blueprint "chap8__example_8_5_2"]
structure ExRefInference where
  left : Fin 7
  right : Fin 7
  resolvedA : FOClause exClauseFormLang rfl
  resolvedB : FOClause exClauseFormLang rfl
  rho : Nat → Term exClauseFormLang
  rho' : Nat → Term exClauseFormLang
  sigma : Nat → Term exClauseFormLang

/-- Example 8.5.2: A graph vertex has its displayed clause and, precisely
    at an internal vertex, its local inference data. -/
@[blueprint "chap8__example_8_5_2"]
structure ExRefNode where
  clause : FOClause exClauseFormLang rfl
  inference : Option ExRefInference

/-- Example 8.5.2: The finite graph table with vertices C1,C2,C3,U,V,W,E.
    Each premise occurrence names a vertex in this same table. In particular
    the three occurrences of C1 all reference vertex 0; E is vertex 6. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exResolutionRefutation (i : Fin 7) : ExRefNode :=
  match i.val with
  | 0 => ⟨exRefClause_C1, none⟩
  | 1 => ⟨exRefClause_C2, none⟩
  | 2 => ⟨exRefClause_C3, none⟩
  | 3 => ⟨exRefLabel_U, some {
      left := 1, right := 0
      resolvedA := [FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a)]
      resolvedB := exRefClause_C1
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 | 2 | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | 4 => ⟨exRefLabel_V, some {
      left := 0, right := 2
      resolvedA := exRefClause_C1
      resolvedB := [FOLiteralCore.pos (exPred_P (Term.var 3) exSkolemConst_a)]
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 | 3 | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | 5 => ⟨exRefLabel_W, some {
      left := 0, right := 4
      resolvedA := [FOLiteralCore.neg (exPred_P (Term.var 1) exSkolemConst_a),
        FOLiteralCore.neg (exPred_P (Term.var 1) (Term.var 4))]
      resolvedB := exRefLabel_V
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 => Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)
        | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | _ => ⟨[], some {
      left := 3, right := 5
      resolvedA := exRefLabel_U, resolvedB := exRefLabel_W
      rho := exRefId, rho' := exRefId, sigma := exRefId }⟩

/-- Example 8.5.2: The root is the displayed empty-clause vertex E. -/
@[blueprint "chap8__example_8_5_2"]
def exResolutionRefutation_root : Fin 7 := 6

/-- Example 8.5.2: Follow ordered premise occurrences in the finite graph;
    false chooses the left premise and true the right premise. -/
@[blueprint "chap8__example_8_5_2"]
def exResolutionRefutation_follow (i : Fin 7) : List Bool → Option (Fin 7)
  | [] => some i
  | side :: rest => do
      let step ← (exResolutionRefutation i).inference
      exResolutionRefutation_follow (if side then step.right else step.left) rest

/-- Example 8.5.2: The four corrected computation trees have exactly the
    displayed labels U,V,W,empty. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exRefStep_labels :
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep1 = exRefLabel_U ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep2 = exRefLabel_V ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep3 = exRefLabel_W ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep4 = []

/-- Example 8.5.2: Every internal graph vertex is a lawful resolution
    inference with its own stored premise IDs and substitution witnesses. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exResolutionRefutation_lawful :
    ∀ (i : Fin 7) (step : ExRefInference),
      (exResolutionRefutation i).inference = some step →
      @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _)
        (exResolutionRefutation i).clause
        (exResolutionRefutation step.left).clause
        (exResolutionRefutation step.right).clause
        step.resolvedA step.resolvedB step.rho step.rho' step.sigma

/-- Example 8.5.2: Premises precede their conclusions, every one of the
    seven vertices is reachable from E, and exactly the three input vertices
    are leaves. Together with lawful inferences and the empty root this
    certifies the displayed finite shared refutation. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exResolutionRefutation_correct :
    (∀ (i : Fin 7) (step : ExRefInference),
      (exResolutionRefutation i).inference = some step →
      step.left.val < i.val ∧ step.right.val < i.val) ∧
    (∀ i : Fin 7, ∃ path : List Bool,
      exResolutionRefutation_follow exResolutionRefutation_root path = some i) ∧
    (∀ i : Fin 7, (exResolutionRefutation i).inference = none ↔ i.val < 3) ∧
    (exResolutionRefutation 0).clause = exRefClause_C1 ∧
    (exResolutionRefutation 1).clause = exRefClause_C2 ∧
    (exResolutionRefutation 2).clause = exRefClause_C3 ∧
    (∀ (i : Fin 7) (step : ExRefInference),
      (exResolutionRefutation i).inference = some step →
      @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _)
        (exResolutionRefutation i).clause
        (exResolutionRefutation step.left).clause
        (exResolutionRefutation step.right).clause
        step.resolvedA step.resolvedB step.rho step.rho' step.sigma) ∧
    (exResolutionRefutation exResolutionRefutation_root).clause = []

/-- Example 8.5.2: The occurrences of C1 below U, W and V all name
    the same vertex, rather than three copies with equal labels. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exResolutionRefutation_shared_C1 :
    exResolutionRefutation_follow exResolutionRefutation_root [false, true] = some 0 ∧
    exResolutionRefutation_follow exResolutionRefutation_root [true, false] = some 0 ∧
    exResolutionRefutation_follow exResolutionRefutation_root [true, true, false] = some 0

end LCS.FOResolution.Method
