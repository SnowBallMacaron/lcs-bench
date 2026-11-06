import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import Attach
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF.ProofsStamp

/-! # Occurrence-indexed GCNF' proofs

Carrier for the proof of Lemma 9.2.2: unary GCNF' proofs indexed by the exact list of clause occurrences, occurrence-sensitive proof paths, exact root occurrences and root-rule certificates. -/

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- A unary GCNF' proof indexed by the exact list of clause occurrences at its
root.  A rule replaces one occurrence of `clauseWithLiteral A B`, at the
position determined by `pre` and `post`, by `A` in the left premise and by the
singleton clause `{B}` in the right premise.  Equal clauses at other positions
remain distinct occurrences. -/
@[blueprint "chap9__lemma_9_2_2"]
inductive OccurrenceGCNFProof : List Clause → Type where
  | axiom_ (clauses : List Clause)
      (hTriv : ∃ P : Nat,
        Clause.single (Literal.pos P) ∈ clauses ∧
        Clause.single (Literal.neg P) ∈ clauses) :
      OccurrenceGCNFProof clauses
  | rule (pre post : List Clause) (A : Clause) (B : Literal)
      (left : OccurrenceGCNFProof (pre ++ A :: post))
      (right :
        OccurrenceGCNFProof (pre ++ Clause.single B :: post)) :
      OccurrenceGCNFProof
        (pre ++ clauseWithLiteral A B :: post)

namespace OccurrenceGCNFProof

/-- Ordinary proof depth: axioms have depth zero and every unary rule
contributes one level. -/
def depth : {clauses : List Clause} → OccurrenceGCNFProof clauses → Nat
  | _, .axiom_ _ _ => 0
  | _, .rule _ _ _ _ left right =>
      1 + max (depth left) (depth right)

/-- The occurrence lists labeling the axiom leaves, from left to right. -/
def axiomLeaves :
    {clauses : List Clause} →
    OccurrenceGCNFProof clauses → List (List Clause)
  | _, .axiom_ clauses _ => [clauses]
  | _, .rule _ _ _ _ left right =>
      axiomLeaves left ++ axiomLeaves right

/-- Every axiom leaf of an occurrence proof contains only singleton clauses. -/
@[blueprint "chap9__lemma_9_2_2"]
def axiomsAllSingleLiteral :
    {clauses : List Clause} → OccurrenceGCNFProof clauses → Prop
  | _, .axiom_ clauses _ =>
      ∀ C ∈ clauses, ∃ L : Literal, C = Clause.single L
  | _, .rule _ _ _ _ left right =>
      axiomsAllSingleLiteral left ∧
      axiomsAllSingleLiteral right

/-! ## Occurrence-sensitive proof paths -/

/-- A path from the root of an occurrence proof to one particular node.
The constructors record every left/right premise choice, so equal subproof
values reused at different positions remain distinct occurrences. -/
inductive RootToNodePath :
    {rootClauses nodeClauses : List Clause} →
    (root : OccurrenceGCNFProof rootClauses) →
    (node : OccurrenceGCNFProof nodeClauses) → Type where
  /-- The empty path identifies the root occurrence itself. -/
  | root {clauses : List Clause}
      (T : OccurrenceGCNFProof clauses) :
      RootToNodePath T T
  /-- Descend through the left premise of a unary occurrence rule. -/
  | leftPremise (pre post : List Clause)
      (A : Clause) (B : Literal)
      (left :
        OccurrenceGCNFProof (pre ++ A :: post))
      (right :
        OccurrenceGCNFProof
          (pre ++ Clause.single B :: post))
      {nodeClauses : List Clause}
      {node : OccurrenceGCNFProof nodeClauses}
      (path : RootToNodePath left node) :
      RootToNodePath
        (.rule pre post A B left right) node
  /-- Descend through the right premise of a unary occurrence rule. -/
  | rightPremise (pre post : List Clause)
      (A : Clause) (B : Literal)
      (left :
        OccurrenceGCNFProof (pre ++ A :: post))
      (right :
        OccurrenceGCNFProof
          (pre ++ Clause.single B :: post))
      {nodeClauses : List Clause}
      {node : OccurrenceGCNFProof nodeClauses}
      (path : RootToNodePath right node) :
      RootToNodePath
        (.rule pre post A B left right) node

/-- A node occurrence in a fixed occurrence proof, identified by its path
rather than by structural equality of the stored subproof. -/
structure NodeOccurrence
    {rootClauses : List Clause}
    (root : OccurrenceGCNFProof rootClauses)
    (nodeClauses : List Clause) where
  node : OccurrenceGCNFProof nodeClauses
  path : RootToNodePath root node

/-- Compose occurrence-sensitive root-to-node paths while retaining every
recorded premise choice. -/
def RootToNodePath.trans
    {rootClauses middleClauses nodeClauses : List Clause}
    {root : OccurrenceGCNFProof rootClauses}
    {middle : OccurrenceGCNFProof middleClauses}
    {node : OccurrenceGCNFProof nodeClauses}
    (first : RootToNodePath root middle)
    (second : RootToNodePath middle node) :
    RootToNodePath root node :=
  match first with
  | .root _ => second
  | .leftPremise pre post A B left right path =>
      .leftPremise pre post A B left right
        (path.trans second)
  | .rightPremise pre post A B left right path =>
      .rightPremise pre post A B left right
        (path.trans second)

end OccurrenceGCNFProof

/-- Evidence that `C` is a particular occurrence in `clauses`, represented by
the prefix and suffix around that occurrence.  This carries the positional
information needed by later permutation arguments without choosing a default
clause when the list is empty. -/
@[blueprint "chap9__lemma_9_2_2"]
structure RootOccurrence (clauses : List Clause) (C : Clause) where
  pre : List Clause
  post : List Clause
  split : clauses = pre ++ C :: post

namespace RootOccurrence

/-- Replace the clause at an exact root occurrence while retaining its
position. -/
def replace {clauses : List Clause} {C : Clause}
    (occ : RootOccurrence clauses C) (replacement : Clause) :
    RootOccurrence
      (occ.pre ++ replacement :: occ.post) replacement :=
  ⟨occ.pre, occ.post, rfl⟩

/-- Regard an exact root occurrence as an occurrence of an equal clause.
Only the clause index changes; the stored prefix and suffix are retained. -/
def castClause {clauses : List Clause} {C C' : Clause}
    (occ : RootOccurrence clauses C) (h : C = C') :
    RootOccurrence clauses C' :=
  h ▸ occ

end RootOccurrence
namespace OccurrenceGCNFProof

/-- Transport an occurrence proof along equality of its exact list index. -/
def transport {clauses clauses' : List Clause}
    (h : clauses = clauses')
    (T : OccurrenceGCNFProof clauses) :
    OccurrenceGCNFProof clauses' :=
  h ▸ T

/-- Transporting the list index does not change ordinary proof depth. -/
theorem depth_transport {clauses clauses' : List Clause}
    (h : clauses = clauses')
    (T : OccurrenceGCNFProof clauses) :
    (transport h T).depth = T.depth := by
  subst clauses'
  rfl

/-- Transporting the list index does not change the ordered axiom-leaf
enumeration. -/
theorem axiomLeaves_transport {clauses clauses' : List Clause}
    (h : clauses = clauses')
    (T : OccurrenceGCNFProof clauses) :
    (transport h T).axiomLeaves = T.axiomLeaves := by
  subst clauses'
  rfl

/-- Transporting the list index does not change the literal-only axiom
condition. -/
theorem axiomsAllSingleLiteral_transport
    {clauses clauses' : List Clause}
    (h : clauses = clauses')
    (T : OccurrenceGCNFProof clauses) :
    (transport h T).axiomsAllSingleLiteral ↔
      T.axiomsAllSingleLiteral := by
  subst clauses'
  rfl

/-- Apply a unary occurrence rule at an explicitly selected root occurrence.
The result is transported only along the occurrence's checked split equation. -/
def ruleAt {clauses : List Clause} {A : Clause} {B : Literal}
    (selected :
      RootOccurrence clauses (clauseWithLiteral A B))
    (left :
      OccurrenceGCNFProof
        (selected.pre ++ A :: selected.post))
    (right :
      OccurrenceGCNFProof
        (selected.pre ++ Clause.single B :: selected.post)) :
    OccurrenceGCNFProof clauses :=
  transport selected.split.symm
    (.rule selected.pre selected.post A B left right)

/-- Ordinary depth at an explicitly selected root obeys the usual
`1 + max` equation. -/
theorem depth_ruleAt {clauses : List Clause}
    {A : Clause} {B : Literal}
    (selected :
      RootOccurrence clauses (clauseWithLiteral A B))
    (left :
      OccurrenceGCNFProof
        (selected.pre ++ A :: selected.post))
    (right :
      OccurrenceGCNFProof
        (selected.pre ++ Clause.single B :: selected.post)) :
    (ruleAt selected left right).depth =
      1 + max left.depth right.depth := by
  rw [ruleAt, depth_transport]
  rfl

/-- The axiom leaves of a rule at an explicit occurrence are exactly the
leaves of its left premise followed by the leaves of its right premise. -/
theorem axiomLeaves_ruleAt
    {clauses : List Clause} {A : Clause} {B : Literal}
    (selected :
      RootOccurrence clauses (clauseWithLiteral A B))
    (left :
      OccurrenceGCNFProof
        (selected.pre ++ A :: selected.post))
    (right :
      OccurrenceGCNFProof
        (selected.pre ++ Clause.single B :: selected.post)) :
    (ruleAt selected left right).axiomLeaves =
      left.axiomLeaves ++ right.axiomLeaves := by
  rw [ruleAt, axiomLeaves_transport]
  rfl

/-- A rule at an explicit root occurrence has literal-only axiom leaves
exactly when both of its actual premises do. -/
theorem axiomsAllSingleLiteral_ruleAt
    {clauses : List Clause} {A : Clause} {B : Literal}
    (selected :
      RootOccurrence clauses (clauseWithLiteral A B))
    (left :
      OccurrenceGCNFProof
        (selected.pre ++ A :: selected.post))
    (right :
      OccurrenceGCNFProof
        (selected.pre ++ Clause.single B :: selected.post)) :
    (ruleAt selected left right).axiomsAllSingleLiteral ↔
      left.axiomsAllSingleLiteral ∧
      right.axiomsAllSingleLiteral := by
  rw [ruleAt, axiomsAllSingleLiteral_transport]
  rfl

/-- Evidence that a proof's root rule selects one exact occurrence, including
its exact prefix and suffix. -/
structure RootRuleAt {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    {A : Clause} {B : Literal}
    (selected :
      RootOccurrence clauses (clauseWithLiteral A B)) where
  left :
    OccurrenceGCNFProof
      (selected.pre ++ A :: selected.post)
  right :
    OccurrenceGCNFProof
      (selected.pre ++ Clause.single B :: selected.post)
  tree_eq : T = ruleAt selected left right

/-- A root-rule certificate exposes the ordinary depth recurrence of the
certified tree. -/
theorem RootRuleAt.depth_eq {clauses : List Clause}
    {T : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {selected :
      RootOccurrence clauses (clauseWithLiteral A B)}
    (rooted : RootRuleAt T selected) :
    T.depth = 1 + max rooted.left.depth rooted.right.depth := by
  rcases rooted with ⟨left, right, tree_eq⟩
  subst T
  exact depth_ruleAt selected left right

/-- A root-rule certificate exposes the exact ordered axiom-leaf
concatenation of the certified tree. -/
theorem RootRuleAt.axiomLeaves_eq {clauses : List Clause}
    {T : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {selected :
      RootOccurrence clauses (clauseWithLiteral A B)}
    (rooted : RootRuleAt T selected) :
    T.axiomLeaves =
      rooted.left.axiomLeaves ++ rooted.right.axiomLeaves := by
  rcases rooted with ⟨left, right, tree_eq⟩
  subst T
  exact axiomLeaves_ruleAt selected left right

/-- A root-rule certificate exposes the literal-only axiom condition of both
actual premises. -/
theorem RootRuleAt.axiomsAllSingleLiteral_iff
    {clauses : List Clause}
    {T : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {selected :
      RootOccurrence clauses (clauseWithLiteral A B)}
    (rooted : RootRuleAt T selected) :
    T.axiomsAllSingleLiteral ↔
      rooted.left.axiomsAllSingleLiteral ∧
      rooted.right.axiomsAllSingleLiteral := by
  rcases rooted with ⟨left, right, tree_eq⟩
  subst T
  exact axiomsAllSingleLiteral_ruleAt selected left right

/-- The output contract for an occurrence-level root permutation.  Besides
the exact selected root occurrence, it records ordinary-depth equality and
preservation of the literal-only axiom condition. -/
structure RootPermutation {clauses : List Clause}
    (source : OccurrenceGCNFProof clauses)
    {A : Clause} {B : Literal}
    (target :
      RootOccurrence clauses (clauseWithLiteral A B)) where
  tree : OccurrenceGCNFProof clauses
  rooted : RootRuleAt tree target
  depth_eq : tree.depth = source.depth
  axiomLeaves_perm :
    tree.axiomLeaves.Perm source.axiomLeaves
  axiomsAllSingleLiteral_iff :
    tree.axiomsAllSingleLiteral ↔
      source.axiomsAllSingleLiteral

/-- Same-target case of root permutation: when the current root rule already
selects the requested occurrence, retain the proof itself.  Exact occurrence
identity, not equality of clause values, selects this branch. -/
def RootRuleAt.sameTarget {clauses : List Clause}
    {T : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {selected :
      RootOccurrence clauses (clauseWithLiteral A B)}
    (rooted : RootRuleAt T selected) :
    RootPermutation T selected where
  tree := T
  rooted := rooted
  depth_eq := rfl
  axiomLeaves_perm := .refl _
  axiomsAllSingleLiteral_iff := Iff.rfl

end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.ruleAt

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.axiomLeaves

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.depth

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation.rooted

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation.tree

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootRuleAt.left

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.RootOccurrence.replace

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootRuleAt

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation
