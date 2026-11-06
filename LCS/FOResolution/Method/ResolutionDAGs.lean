import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Resolvents
import Attach
import LCS.FOResolution.Method.ResolutionDAGs.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- Definition 8.5.3: A first-order resolution tree, encoding a DAG for
    first-order clauses with separating pair + mgu at each resolve node. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
inductive FOResolutionTree (L : Language) (hNoEq : L.withoutEquality) : Type where
  /-- A leaf node labeled with a clause from the input set S -/
  | axiom_ : FOClause L hNoEq → FOResolutionTree L hNoEq
  /-- An internal resolution step node with two subtrees, the literal
      subsets A' (resolvedA) and B' (resolvedB) that are resolved on,
      a separating pair (rho, rho') of substitutions, and a most
      general unifier sigma. The resolvent clause is computed as
      sigma(rho(label(T1) - resolvedA) ++ rho'(label(T2) - resolvedB)). -/
  | resolve :
      FOResolutionTree L hNoEq →
      FOResolutionTree L hNoEq →
      (resolvedA : List (FOLiteral L hNoEq)) →
      (resolvedB : List (FOLiteral L hNoEq)) →
      (rho : Nat → Term L) →
      (rho' : Nat → Term L) →
      (sigma : Nat → Term L) →
      FOResolutionTree L hNoEq

-- ===================================================================
-- Definition 8.5.3 (companion type): First-order resolution DAG
-- ===================================================================

/-- Definition 8.5.3: A first-order resolution DAG is a finite set
    (represented as a list) of resolution trees. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
abbrev FOResolutionDAG (L : Language) (hNoEq : L.withoutEquality) : Type :=
  List (FOResolutionTree L hNoEq)

namespace FOResolutionTree

/-- Definition 8.5.3 (companion): The label (clause) at a resolution
    tree node. For a leaf, it is the clause itself. For an internal
    node, it is the resolvent clause computed from the labels of the
    two children using the separating pair and MGU. -/
@[blueprint "chap8__definition_8_5_3"]
def label {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)] :
    FOResolutionTree L hNoEq → FOClause L hNoEq
  | .axiom_ C => C
  | .resolve T1 T2 resolvedA resolvedB rho rho' sigma =>
    substLits (hNoEq := by first | exact hNoEq | done) sigma (substLits (hNoEq := by first | exact hNoEq | done) rho (listDiff (label (hNoEq := by first | exact hNoEq | done) T1) resolvedA) ++
                     substLits (hNoEq := by first | exact hNoEq | done) rho' (listDiff (label (hNoEq := by first | exact hNoEq | done) T2) resolvedB))

/-- Definition 8.5.3 (companion): Predicate that all leaves of a
    resolution tree are labeled with clauses from a given set S. -/
@[blueprint "chap8__definition_8_5_3"]
def leavesFrom {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → (FOClause L hNoEq → Prop) → Prop
  | .axiom_ C, S => S C
  | .resolve T1 T2 _ _ _ _ _, S =>
    leavesFrom (hNoEq := by first | exact hNoEq | done) T1 S ∧ leavesFrom (hNoEq := by first | exact hNoEq | done) T2 S

/-- Definition 8.5.3 (companion): Predicate that a resolution tree is
    well-formed: every internal node represents a valid resolution step
    (the label is a resolvent of the two children's labels via the given
    separating pair and MGU). -/
@[blueprint "chap8__definition_8_5_3"]
def isWellFormed {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)] :
    FOResolutionTree L hNoEq → Prop
  | .axiom_ _ => True
  | .resolve T1 T2 resolvedA resolvedB rho rho' sigma =>
    isWellFormed (hNoEq := by first | exact hNoEq | done) T1 ∧
    isWellFormed (hNoEq := by first | exact hNoEq | done) T2 ∧
    IsResolventVia (hNoEq := by first | exact hNoEq | done)
      (label (hNoEq := by first | exact hNoEq | done) (.resolve T1 T2 resolvedA resolvedB rho rho' sigma))
      (label (hNoEq := by first | exact hNoEq | done) T1) (label (hNoEq := by first | exact hNoEq | done) T2) resolvedA resolvedB rho rho' sigma

end FOResolutionTree

namespace FOResolutionDAG

/-- Definition 8.5.3 (companion): A resolution DAG D is a resolution DAG
    for a set of clauses S iff D is nonempty, every tree in D has leaves
    from S, and every tree in D is well-formed. -/
@[blueprint "chap8__definition_8_5_3"]
def isResolutionDAGFor {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAG L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  D ≠ [] ∧
  (∀ T, T ∈ D → T.leavesFrom (hNoEq := by first | exact hNoEq | done) S) ∧
  (∀ T, T ∈ D → T.isWellFormed (hNoEq := by first | exact hNoEq | done))

/-- Definition 8.5.3: A resolution DAG is a resolution refutation iff
    it consists of a single tree whose root is the empty clause. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
def isResolutionRefutation {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAG L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  ∃ T : FOResolutionTree L hNoEq,
      D = [T] ∧
      T.leavesFrom (hNoEq := by first | exact hNoEq | done) S ∧
      T.isWellFormed (hNoEq := by first | exact hNoEq | done) ∧
      T.label (hNoEq := by first | exact hNoEq | done) = []

end FOResolutionDAG

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

end LCS.FOResolution.Method
end
