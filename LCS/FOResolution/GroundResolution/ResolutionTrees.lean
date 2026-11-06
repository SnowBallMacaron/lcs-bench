import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Graph
import LCS.Herbrand.PrimRecursive
import LCS.FirstOrder.Equality.Search.Procedure
import LCS.CutElim.LKe.Equivalence
import Attach
import LCS.FOResolution.GroundResolution.ResolutionTrees.ProofsStamp

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm

/-- Example 8.3.1 (companion): Finite binary resolution-tree syntax over
    a first-order language without equality. Leaves store clauses and
    internal nodes store two premise trees and a pivot literal.
    `labelSpec` certifies groundness and the resolution inferences;
    `isRefutation` additionally requires input-clause leaves and an empty
    root label. Internal clause labels are specified by `labelSpec`. -/
@[blueprint "chap8__example_8_3_1"]
inductive FOResolutionTree (L : Language) (hNoEq : L.withoutEquality) : Type where
  /-- A leaf node labeled with a ground clause from the input set -/
  | axiom_ : FOClause L hNoEq → FOResolutionTree L hNoEq
  /-- A resolution step combining two subtrees via pivot literal L -/
  | resolve : FOResolutionTree L hNoEq → FOResolutionTree L hNoEq →
      (pivot : FOLiteral L hNoEq) → FOResolutionTree L hNoEq

namespace FOResolutionTree

/-- Example 8.3.1 (companion): Certified ground-resolution labeling in
    a language without equality. A leaf has its stored ground clause.
    A resolution step has certified premise labels containing the pivot
    and its conjugate, respectively. Its ground conclusion is extensionally
    the union of those labels with the pivot and its conjugate removed.
    The specification uses literal membership, so list ordering and
    repetitions do not change the represented resolvent. -/
@[blueprint "chap8__example_8_3_1"]
def labelSpec {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → FOClause L hNoEq → Prop
  | .axiom_ C, C' =>
    C' = C ∧ FOClause.isGround hNoEq C
  | .resolve T1 T2 pivot, C' =>
    ∃ C1 C2 : FOClause L hNoEq,
      labelSpec (hNoEq := hNoEq) T1 C1 ∧ labelSpec (hNoEq := hNoEq) T2 C2 ∧
      pivot ∈ C1 ∧
      FOLiteral.conjugate hNoEq pivot ∈ C2 ∧
      FOClause.isGround hNoEq C' ∧
      (∀ lit, lit ∈ C' ↔
        (lit ∈ C1 ∧ lit ≠ pivot) ∨
        (lit ∈ C2 ∧ lit ≠ FOLiteral.conjugate hNoEq pivot))

/-- Lemma 8.3.1 (companion): All leaf clauses in a first-order
    resolution tree are members of the clause set S. -/
@[blueprint "chap8__lemma_8_3_1"]
def leavesFrom {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → (FOClause L hNoEq → Prop) → Prop
  | .axiom_ C, S => S C
  | .resolve T1 T2 _, S => T1.leavesFrom (hNoEq := hNoEq) S ∧ T2.leavesFrom (hNoEq := hNoEq) S

/-- Lemma 8.3.1 (companion): A ground-resolution refutation over a
    language without equality certifies that every clause in S is ground,
    every leaf belongs to S, and the root has the certified empty label.
    The input predicate S need not be finite here; the completeness theorem
    uses a finite list of ground clauses. -/
@[blueprint "chap8__lemma_8_3_1"]
def isRefutation {L : Language} (hNoEq : L.withoutEquality)
    (T : FOResolutionTree L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  (∀ C, S C → FOClause.isGround hNoEq C) ∧
  T.leavesFrom hNoEq S ∧
  labelSpec (hNoEq := hNoEq) T []

end FOResolutionTree

open LCS.FirstOrder.SemanticsN
namespace FOResolutionTree

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- A certified ground-resolution label is ground at every node. -/
theorem labelSpec_isGround {L : Language} (hNoEq : L.withoutEquality)
    {T : FOResolutionTree L hNoEq} {C : FOClause L hNoEq}
    (hSpec : T.labelSpec (hNoEq := hNoEq) C) :
    C.isGround hNoEq := by
  cases T with
  | axiom_ source =>
    exact hSpec.1 ▸ hSpec.2
  | resolve _ _ _ =>
    exact hSpec.choose_spec.choose_spec.2.2.2.2.1

end FOResolutionTree

open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FOResolution.Unification

end LCS.FOResolution.GroundResolution
end
