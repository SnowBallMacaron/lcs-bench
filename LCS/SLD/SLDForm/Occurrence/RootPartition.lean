import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF
import LCS.SLD.SLDForm.Occurrence.RootPermutation
import Attach
import LCS.SLD.SLDForm.Occurrence.RootPartition.ProofsStamp

/-! # Root-partition macros on an exact occurrence

Carrier for the proof of Lemma 9.2.2: exposing an arbitrary disjoint partition of a clause at the root by successive root moves. -/

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFProof

/-! ## Arbitrary right-partition macros on an exact occurrence -/

/-- The residual clause obtained by placing an ordered list of peeled
literals around the fixed left partition `A`.  Its recursive presentation
makes the next unary pivot definitionally visible at the head of a nonempty
order. -/
@[blueprint "chap9__lemma_9_2_2"]
def partitionResidual (A : Clause) : List Literal → Clause
  | [] => A
  | b :: bs =>
      clauseWithLiteral (partitionResidual A bs) b

/-- A structural certificate that the requested `order` is peeled by genuine
root rules along the actual selected occurrence's left spine.  The right
premise at each level is retained but is not part of the residual spine. -/
inductive RootPartitionMacro (A : Clause) :
    {clauses : List Clause} →
    (T : OccurrenceGCNFProof clauses) →
    (order : List Literal) →
    (target :
      RootOccurrence clauses (partitionResidual A order)) →
    Type where
  /-- The final right literal is peeled, leaving exactly `A` in the left
  premise. -/
  | last {clauses : List Clause}
      {T : OccurrenceGCNFProof clauses}
      {b : Literal}
      {target :
        RootOccurrence clauses (partitionResidual A [b])}
      (rooted : RootRuleAt T target) :
      RootPartitionMacro A T [b] target
  /-- Peel the head literal and continue at the same exact occurrence in the
  actual left premise. -/
  | cons {clauses : List Clause}
      {T : OccurrenceGCNFProof clauses}
      {b b' : Literal} {bs : List Literal}
      {target :
        RootOccurrence clauses
          (partitionResidual A (b :: b' :: bs))}
      (rooted : RootRuleAt T target)
      (tail :
        RootPartitionMacro A rooted.left (b' :: bs)
          (target.replace
            (partitionResidual A (b' :: bs)))) :
      RootPartitionMacro A T (b :: b' :: bs) target

/-- The result of executing a whole ordered root-partition plan. -/
@[blueprint "chap9__lemma_9_2_2"]
structure OrderedRootPartitionPermutation
    (A : Clause)
    {clauses : List Clause}
    (source : OccurrenceGCNFProof clauses)
    (order : List Literal)
    (target :
      RootOccurrence clauses (partitionResidual A order)) where
  tree : OccurrenceGCNFProof clauses
  rootedMacro : RootPartitionMacro A tree order target
  depth_eq : tree.depth = source.depth
  axiomLeaves_perm :
    tree.axiomLeaves.Perm source.axiomLeaves
  axiomsAllSingleLiteral_iff :
    tree.axiomsAllSingleLiteral ↔
      source.axiomsAllSingleLiteral

/-- A checkable plan for successively exposing the literals in `order` at the
root and then continuing down the actual selected occurrence's left spine.
Each head plan is itself built only from same-target steps and the two atomic
distinct-position diamonds. -/
@[blueprint "chap9__lemma_9_2_2"]
inductive RootPartitionPlan (A : Clause) :
    {clauses : List Clause} →
    (source : OccurrenceGCNFProof clauses) →
    (order : List Literal) →
    (target :
      RootOccurrence clauses (partitionResidual A order)) →
    Type where
  | last {clauses : List Clause}
      {source : OccurrenceGCNFProof clauses}
      {b : Literal}
      {target :
        RootOccurrence clauses (partitionResidual A [b])}
      (headPlan : RootPermutationPlan source target) :
      RootPartitionPlan A source [b] target
  | cons {clauses : List Clause}
      {source : OccurrenceGCNFProof clauses}
      {b b' : Literal} {bs : List Literal}
      {target :
        RootOccurrence clauses
          (partitionResidual A (b :: b' :: bs))}
      (headPlan : RootPermutationPlan source target)
      (tailPlan :
        RootPartitionPlan A
          headPlan.execute.rooted.left (b' :: bs)
          (target.replace
            (partitionResidual A (b' :: bs)))) :
      RootPartitionPlan A source (b :: b' :: bs) target

/-- Exact occurrence-level certificate for an arbitrary nonempty disjoint
partition `C = A ∪ B`.  The right side is enumerated specifically by
`B.toList`, and the macro is tied to the supplied root occurrence rather than
to clause-value membership alone. -/
structure RootPartitionCertificate
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    {C : Clause}
    (target : RootOccurrence clauses C)
    (A B : Clause) where
  leftNonempty : ∃ a, a ∈ A
  rightNonempty : ∃ b, b ∈ B
  disjoint : ∀ l, l ∈ A → l ∉ B
  unionEq : C = Clause.union A B
  orderNodup : B.toList.Nodup
  orderEq : Clause.ofList B.toList = B
  target_eq : C = partitionResidual A B.toList
  rootedMacro :
    RootPartitionMacro A T B.toList
      (target.castClause target_eq)

/-- An arbitrary-partition root permutation retains both its exact structural
certificate and all invariants of the ordered occurrence transformation. -/
structure RootPartitionPermutation
    {clauses : List Clause}
    (source : OccurrenceGCNFProof clauses)
    {C : Clause}
    (target : RootOccurrence clauses C)
    (A B : Clause) where
  tree : OccurrenceGCNFProof clauses
  certificate :
    RootPartitionCertificate tree target A B
  depth_eq : tree.depth = source.depth
  axiomLeaves_perm :
    tree.axiomLeaves.Perm source.axiomLeaves
  axiomsAllSingleLiteral_iff :
    tree.axiomsAllSingleLiteral ↔
      source.axiomsAllSingleLiteral

end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.OrderedRootPartitionPermutation.axiomsAllSingleLiteral_iff

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPartitionMacro
