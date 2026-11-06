import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF
import LCS.SLD.SLDForm.Occurrence.CommutingDiamond
import Attach
import LCS.SLD.SLDForm.Occurrence.RootPermutation.ProofsStamp

/-! # Moving one selected rule to the root

Carrier for the proof of Lemma 9.2.2: structural plans that permute a requested unary rule to the root, their execution and the inference-interchange certificates they produce. -/

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFProof

/-- A checkable structural witness that a requested unary rule is the first
rule selecting one exact occurrence on every branch.
The `belowFirst` and `belowSecond` constructors record only rules at a
distinct list position before the requested rule.  Consequently their
execution uses the two atomic commuting diamonds above.  There is
intentionally no constructor for changing the pivot order at the same
occurrence: that triangular conversion does not preserve ordinary max-depth
in general. -/
inductive RootPermutationPlan :
    {clauses : List Clause} →
    (source : OccurrenceGCNFProof clauses) →
    {A : Clause} → {B : Literal} →
    (target :
      RootOccurrence clauses (clauseWithLiteral A B)) →
    Type where
  /-- The requested occurrence is already selected by the root rule. -/
  | atRoot {clauses : List Clause}
      {source : OccurrenceGCNFProof clauses}
      {A : Clause} {B : Literal}
      {target :
        RootOccurrence clauses (clauseWithLiteral A B)}
      (rooted : RootRuleAt source target) :
      RootPermutationPlan source target
  /-- A rule at the first distinguished position precedes the requested rule
  at the second position in both premises. -/
  | belowFirst (ctx : TwoOccurrenceContext)
      (C A : Clause) (D B : Literal)
      (left :
        OccurrenceGCNFProof
          (ctx.fill C (clauseWithLiteral A B)))
      (right :
        OccurrenceGCNFProof
          (ctx.fill (Clause.single D)
            (clauseWithLiteral A B)))
      (leftPlan :
        RootPermutationPlan left
          (ctx.secondOccurrence C
            (clauseWithLiteral A B)))
      (rightPlan :
        RootPermutationPlan right
          (ctx.secondOccurrence (Clause.single D)
            (clauseWithLiteral A B))) :
      RootPermutationPlan
        (UnaryRuleSquare.splitFirst ctx C D
          (clauseWithLiteral A B) left right)
        (ctx.secondOccurrence
          (clauseWithLiteral C D)
          (clauseWithLiteral A B))
  /-- A rule at the second distinguished position precedes the requested rule
  at the first position in both premises. -/
  | belowSecond (ctx : TwoOccurrenceContext)
      (A C : Clause) (B D : Literal)
      (left :
        OccurrenceGCNFProof
          (ctx.fill (clauseWithLiteral A B) C))
      (right :
        OccurrenceGCNFProof
          (ctx.fill (clauseWithLiteral A B)
            (Clause.single D)))
      (leftPlan :
        RootPermutationPlan left
          (ctx.firstOccurrence
            (clauseWithLiteral A B) C))
      (rightPlan :
        RootPermutationPlan right
          (ctx.firstOccurrence
            (clauseWithLiteral A B)
            (Clause.single D))) :
      RootPermutationPlan
        (UnaryRuleSquare.splitSecond ctx
          (clauseWithLiteral A B) C D left right)
        (ctx.firstOccurrence
          (clauseWithLiteral A B)
          (clauseWithLiteral C D))

/-- Assemble the four atomic corners after recursively exposing a requested
second-position rule in both premises of a first-position rule. -/
def belowFirstSquare (ctx : TwoOccurrenceContext)
    (C A : Clause) (D B : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill C (clauseWithLiteral A B))}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single D)
          (clauseWithLiteral A B))}
    (leftPerm :
      RootPermutation left
        (ctx.secondOccurrence C
          (clauseWithLiteral A B)))
    (rightPerm :
      RootPermutation right
        (ctx.secondOccurrence (Clause.single D)
          (clauseWithLiteral A B))) :
    UnaryRuleSquare ctx C A D B where
  leftLeft :=
    transport
      (ctx.fill_eq_secondReplacement
        C (clauseWithLiteral A B) A).symm
      leftPerm.rooted.left
  leftRight :=
    transport
      (ctx.fill_eq_secondReplacement
        C (clauseWithLiteral A B)
        (Clause.single B)).symm
      leftPerm.rooted.right
  rightLeft :=
    transport
      (ctx.fill_eq_secondReplacement
        (Clause.single D) (clauseWithLiteral A B) A).symm
      rightPerm.rooted.left
  rightRight :=
    transport
      (ctx.fill_eq_secondReplacement
        (Clause.single D) (clauseWithLiteral A B)
        (Clause.single B)).symm
      rightPerm.rooted.right

/-- The intermediate first-then-second tree assembled from two recursive
second-position permutations has the depth of the original first-position
root applied to the two permuted premises. -/
theorem belowFirstSquare_depth
    (ctx : TwoOccurrenceContext)
    (C A : Clause) (D B : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill C (clauseWithLiteral A B))}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single D)
          (clauseWithLiteral A B))}
    (leftPerm :
      RootPermutation left
        (ctx.secondOccurrence C
          (clauseWithLiteral A B)))
    (rightPerm :
      RootPermutation right
        (ctx.secondOccurrence (Clause.single D)
          (clauseWithLiteral A B))) :
    (belowFirstSquare ctx C A D B
      leftPerm rightPerm).firstThenSecond.depth =
      1 + max leftPerm.tree.depth rightPerm.tree.depth := by
  let square :=
    belowFirstSquare ctx C A D B leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitSecond ctx C A B
        square.leftLeft square.leftRight).depth =
        leftPerm.tree.depth := by
    rw [UnaryRuleSquare.depth_splitSecond]
    simp only [square, belowFirstSquare, depth_transport]
    exact leftPerm.rooted.depth_eq.symm
  have hRight :
      (UnaryRuleSquare.splitSecond ctx
        (Clause.single D) A B
        square.rightLeft square.rightRight).depth =
        rightPerm.tree.depth := by
    rw [UnaryRuleSquare.depth_splitSecond]
    simp only [square, belowFirstSquare, depth_transport]
    exact rightPerm.rooted.depth_eq.symm
  rw [UnaryRuleSquare.firstThenSecond,
    UnaryRuleSquare.depth_splitFirst, hLeft, hRight]

/-- The intermediate first-then-second tree has exactly the concatenated
axiom leaves of the two recursively permuted premises. -/
theorem belowFirstSquare_axiomLeaves
    (ctx : TwoOccurrenceContext)
    (C A : Clause) (D B : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill C (clauseWithLiteral A B))}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single D)
          (clauseWithLiteral A B))}
    (leftPerm :
      RootPermutation left
        (ctx.secondOccurrence C
          (clauseWithLiteral A B)))
    (rightPerm :
      RootPermutation right
        (ctx.secondOccurrence (Clause.single D)
          (clauseWithLiteral A B))) :
    (belowFirstSquare ctx C A D B
      leftPerm rightPerm).firstThenSecond.axiomLeaves =
      leftPerm.tree.axiomLeaves ++
        rightPerm.tree.axiomLeaves := by
  let square :=
    belowFirstSquare ctx C A D B leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitSecond ctx C A B
        square.leftLeft square.leftRight).axiomLeaves =
        leftPerm.tree.axiomLeaves := by
    rw [UnaryRuleSquare.axiomLeaves_splitSecond]
    simp only [square, belowFirstSquare,
      axiomLeaves_transport]
    exact leftPerm.rooted.axiomLeaves_eq.symm
  have hRight :
      (UnaryRuleSquare.splitSecond ctx
        (Clause.single D) A B
        square.rightLeft square.rightRight).axiomLeaves =
        rightPerm.tree.axiomLeaves := by
    rw [UnaryRuleSquare.axiomLeaves_splitSecond]
    simp only [square, belowFirstSquare,
      axiomLeaves_transport]
    exact rightPerm.rooted.axiomLeaves_eq.symm
  rw [UnaryRuleSquare.firstThenSecond,
    UnaryRuleSquare.axiomLeaves_splitFirst, hLeft, hRight]

/-- The literal-only axiom condition of the intermediate
first-then-second tree is exactly the conjunction of the conditions on the
two recursively permuted premises. -/
theorem belowFirstSquare_axiomsAllSingleLiteral
    (ctx : TwoOccurrenceContext)
    (C A : Clause) (D B : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill C (clauseWithLiteral A B))}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single D)
          (clauseWithLiteral A B))}
    (leftPerm :
      RootPermutation left
        (ctx.secondOccurrence C
          (clauseWithLiteral A B)))
    (rightPerm :
      RootPermutation right
        (ctx.secondOccurrence (Clause.single D)
          (clauseWithLiteral A B))) :
    (belowFirstSquare ctx C A D B
      leftPerm rightPerm).firstThenSecond.axiomsAllSingleLiteral ↔
      leftPerm.tree.axiomsAllSingleLiteral ∧
        rightPerm.tree.axiomsAllSingleLiteral := by
  let square :=
    belowFirstSquare ctx C A D B leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitSecond ctx C A B
        square.leftLeft square.leftRight).axiomsAllSingleLiteral ↔
        leftPerm.tree.axiomsAllSingleLiteral := by
    rw [UnaryRuleSquare.axiomsAllSingleLiteral_splitSecond]
    simp only [square, belowFirstSquare,
      axiomsAllSingleLiteral_transport]
    exact leftPerm.rooted.axiomsAllSingleLiteral_iff.symm
  have hRight :
      (UnaryRuleSquare.splitSecond ctx
        (Clause.single D) A B
        square.rightLeft square.rightRight).axiomsAllSingleLiteral ↔
        rightPerm.tree.axiomsAllSingleLiteral := by
    rw [UnaryRuleSquare.axiomsAllSingleLiteral_splitSecond]
    simp only [square, belowFirstSquare,
      axiomsAllSingleLiteral_transport]
    exact rightPerm.rooted.axiomsAllSingleLiteral_iff.symm
  rw [UnaryRuleSquare.firstThenSecond,
    UnaryRuleSquare.axiomsAllSingleLiteral_splitFirst,
    hLeft, hRight]

/-- Assemble the four atomic corners after recursively exposing a requested
first-position rule in both premises of a second-position rule. -/
def belowSecondSquare (ctx : TwoOccurrenceContext)
    (A C : Clause) (B D : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B) C)}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B)
          (Clause.single D))}
    (leftPerm :
      RootPermutation left
        (ctx.firstOccurrence
          (clauseWithLiteral A B) C))
    (rightPerm :
      RootPermutation right
        (ctx.firstOccurrence
          (clauseWithLiteral A B) (Clause.single D))) :
    UnaryRuleSquare ctx A C B D where
  leftLeft :=
    transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B) C A).symm
      leftPerm.rooted.left
  leftRight :=
    transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B)
        (Clause.single D) A).symm
      rightPerm.rooted.left
  rightLeft :=
    transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B) C
        (Clause.single B)).symm
      leftPerm.rooted.right
  rightRight :=
    transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B)
        (Clause.single D)
        (Clause.single B)).symm
      rightPerm.rooted.right

/-- The intermediate second-then-first tree assembled from two recursive
first-position permutations has the expected outer depth. -/
theorem belowSecondSquare_depth
    (ctx : TwoOccurrenceContext)
    (A C : Clause) (B D : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B) C)}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B)
          (Clause.single D))}
    (leftPerm :
      RootPermutation left
        (ctx.firstOccurrence
          (clauseWithLiteral A B) C))
    (rightPerm :
      RootPermutation right
        (ctx.firstOccurrence
          (clauseWithLiteral A B) (Clause.single D))) :
    (belowSecondSquare ctx A C B D
      leftPerm rightPerm).secondThenFirst.depth =
      1 + max leftPerm.tree.depth rightPerm.tree.depth := by
  let square :=
    belowSecondSquare ctx A C B D leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitFirst ctx A B C
        square.leftLeft square.rightLeft).depth =
        leftPerm.tree.depth := by
    rw [UnaryRuleSquare.depth_splitFirst]
    simp only [square, belowSecondSquare, depth_transport]
    exact leftPerm.rooted.depth_eq.symm
  have hRight :
      (UnaryRuleSquare.splitFirst ctx A B
        (Clause.single D)
        square.leftRight square.rightRight).depth =
        rightPerm.tree.depth := by
    rw [UnaryRuleSquare.depth_splitFirst]
    simp only [square, belowSecondSquare, depth_transport]
    exact rightPerm.rooted.depth_eq.symm
  rw [UnaryRuleSquare.secondThenFirst,
    UnaryRuleSquare.depth_splitSecond, hLeft, hRight]

/-- The intermediate second-then-first tree has exactly the concatenated
axiom leaves of the two recursively permuted premises. -/
theorem belowSecondSquare_axiomLeaves
    (ctx : TwoOccurrenceContext)
    (A C : Clause) (B D : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B) C)}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B)
          (Clause.single D))}
    (leftPerm :
      RootPermutation left
        (ctx.firstOccurrence
          (clauseWithLiteral A B) C))
    (rightPerm :
      RootPermutation right
        (ctx.firstOccurrence
          (clauseWithLiteral A B) (Clause.single D))) :
    (belowSecondSquare ctx A C B D
      leftPerm rightPerm).secondThenFirst.axiomLeaves =
      leftPerm.tree.axiomLeaves ++
        rightPerm.tree.axiomLeaves := by
  let square :=
    belowSecondSquare ctx A C B D leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitFirst ctx A B C
        square.leftLeft square.rightLeft).axiomLeaves =
        leftPerm.tree.axiomLeaves := by
    rw [UnaryRuleSquare.axiomLeaves_splitFirst]
    simp only [square, belowSecondSquare,
      axiomLeaves_transport]
    exact leftPerm.rooted.axiomLeaves_eq.symm
  have hRight :
      (UnaryRuleSquare.splitFirst ctx A B
        (Clause.single D)
        square.leftRight square.rightRight).axiomLeaves =
        rightPerm.tree.axiomLeaves := by
    rw [UnaryRuleSquare.axiomLeaves_splitFirst]
    simp only [square, belowSecondSquare,
      axiomLeaves_transport]
    exact rightPerm.rooted.axiomLeaves_eq.symm
  rw [UnaryRuleSquare.secondThenFirst,
    UnaryRuleSquare.axiomLeaves_splitSecond, hLeft, hRight]

/-- The literal-only axiom condition of the intermediate
second-then-first tree is exactly the conjunction of the conditions on the
two recursively permuted premises. -/
theorem belowSecondSquare_axiomsAllSingleLiteral
    (ctx : TwoOccurrenceContext)
    (A C : Clause) (B D : Literal)
    {left :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B) C)}
    {right :
      OccurrenceGCNFProof
        (ctx.fill (clauseWithLiteral A B)
          (Clause.single D))}
    (leftPerm :
      RootPermutation left
        (ctx.firstOccurrence
          (clauseWithLiteral A B) C))
    (rightPerm :
      RootPermutation right
        (ctx.firstOccurrence
          (clauseWithLiteral A B) (Clause.single D))) :
    (belowSecondSquare ctx A C B D
      leftPerm rightPerm).secondThenFirst.axiomsAllSingleLiteral ↔
      leftPerm.tree.axiomsAllSingleLiteral ∧
        rightPerm.tree.axiomsAllSingleLiteral := by
  let square :=
    belowSecondSquare ctx A C B D leftPerm rightPerm
  have hLeft :
      (UnaryRuleSquare.splitFirst ctx A B C
        square.leftLeft square.rightLeft).axiomsAllSingleLiteral ↔
        leftPerm.tree.axiomsAllSingleLiteral := by
    rw [UnaryRuleSquare.axiomsAllSingleLiteral_splitFirst]
    simp only [square, belowSecondSquare,
      axiomsAllSingleLiteral_transport]
    exact leftPerm.rooted.axiomsAllSingleLiteral_iff.symm
  have hRight :
      (UnaryRuleSquare.splitFirst ctx A B
        (Clause.single D)
        square.leftRight square.rightRight).axiomsAllSingleLiteral ↔
        rightPerm.tree.axiomsAllSingleLiteral := by
    rw [UnaryRuleSquare.axiomsAllSingleLiteral_splitFirst]
    simp only [square, belowSecondSquare,
      axiomsAllSingleLiteral_transport]
    exact rightPerm.rooted.axiomsAllSingleLiteral_iff.symm
  rw [UnaryRuleSquare.secondThenFirst,
    UnaryRuleSquare.axiomsAllSingleLiteral_splitSecond,
    hLeft, hRight]

/-- Execute a structural root-permutation plan.  Every recursive commuting
step is an application of one of the exact atomic diamonds, so the resulting
certificate preserves ordinary depth and every axiom leaf with
multiplicity. -/
def RootPermutationPlan.execute
    {clauses : List Clause}
    {source : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {target :
      RootOccurrence clauses (clauseWithLiteral A B)}
    (plan : RootPermutationPlan source target) :
    RootPermutation source target :=
  match plan with
  | .atRoot rooted =>
      rooted.sameTarget
  | .belowFirst ctx C A D B left right
      leftPlan rightPlan =>
      let leftPerm := leftPlan.execute
      let rightPerm := rightPlan.execute
      let square :=
        belowFirstSquare ctx C A D B leftPerm rightPerm
      let commuted :=
        UnaryRuleSquare.commuteSecondToRoot square
      {
        tree := commuted.tree
        rooted := commuted.rooted
        depth_eq := by
          calc
            commuted.tree.depth =
                square.firstThenSecond.depth :=
              commuted.depth_eq
            _ =
                1 + max leftPerm.tree.depth
                  rightPerm.tree.depth :=
              belowFirstSquare_depth
                ctx C A D B leftPerm rightPerm
            _ = 1 + max left.depth right.depth := by
              rw [leftPerm.depth_eq, rightPerm.depth_eq]
            _ =
                (UnaryRuleSquare.splitFirst ctx C D
                  (clauseWithLiteral A B)
                  left right).depth :=
              (UnaryRuleSquare.depth_splitFirst
                ctx C D (clauseWithLiteral A B)
                left right).symm
        axiomLeaves_perm := by
          apply commuted.axiomLeaves_perm.trans
          rw [belowFirstSquare_axiomLeaves,
            UnaryRuleSquare.axiomLeaves_splitFirst]
          exact leftPerm.axiomLeaves_perm.append
            rightPerm.axiomLeaves_perm
        axiomsAllSingleLiteral_iff := by
          calc
            commuted.tree.axiomsAllSingleLiteral ↔
                square.firstThenSecond.axiomsAllSingleLiteral :=
              commuted.axiomsAllSingleLiteral_iff
            _ ↔
                leftPerm.tree.axiomsAllSingleLiteral ∧
                  rightPerm.tree.axiomsAllSingleLiteral :=
              belowFirstSquare_axiomsAllSingleLiteral
                ctx C A D B leftPerm rightPerm
            _ ↔
                left.axiomsAllSingleLiteral ∧
                  right.axiomsAllSingleLiteral :=
              and_congr
                leftPerm.axiomsAllSingleLiteral_iff
                rightPerm.axiomsAllSingleLiteral_iff
            _ ↔
                (UnaryRuleSquare.splitFirst ctx C D
                  (clauseWithLiteral A B)
                  left right).axiomsAllSingleLiteral :=
              (UnaryRuleSquare.axiomsAllSingleLiteral_splitFirst
                ctx C D (clauseWithLiteral A B)
                left right).symm
      }
  | .belowSecond ctx A C B D left right
      leftPlan rightPlan =>
      let leftPerm := leftPlan.execute
      let rightPerm := rightPlan.execute
      let square :=
        belowSecondSquare ctx A C B D leftPerm rightPerm
      let commuted :=
        UnaryRuleSquare.commuteFirstToRoot square
      {
        tree := commuted.tree
        rooted := commuted.rooted
        depth_eq := by
          calc
            commuted.tree.depth =
                square.secondThenFirst.depth :=
              commuted.depth_eq
            _ =
                1 + max leftPerm.tree.depth
                  rightPerm.tree.depth :=
              belowSecondSquare_depth
                ctx A C B D leftPerm rightPerm
            _ = 1 + max left.depth right.depth := by
              rw [leftPerm.depth_eq, rightPerm.depth_eq]
            _ =
                (UnaryRuleSquare.splitSecond ctx
                  (clauseWithLiteral A B) C D
                  left right).depth :=
              (UnaryRuleSquare.depth_splitSecond
                ctx (clauseWithLiteral A B) C D
                left right).symm
        axiomLeaves_perm := by
          apply commuted.axiomLeaves_perm.trans
          rw [belowSecondSquare_axiomLeaves,
            UnaryRuleSquare.axiomLeaves_splitSecond]
          exact leftPerm.axiomLeaves_perm.append
            rightPerm.axiomLeaves_perm
        axiomsAllSingleLiteral_iff := by
          calc
            commuted.tree.axiomsAllSingleLiteral ↔
                square.secondThenFirst.axiomsAllSingleLiteral :=
              commuted.axiomsAllSingleLiteral_iff
            _ ↔
                leftPerm.tree.axiomsAllSingleLiteral ∧
                  rightPerm.tree.axiomsAllSingleLiteral :=
              belowSecondSquare_axiomsAllSingleLiteral
                ctx A C B D leftPerm rightPerm
            _ ↔
                left.axiomsAllSingleLiteral ∧
                  right.axiomsAllSingleLiteral :=
              and_congr
                leftPerm.axiomsAllSingleLiteral_iff
                rightPerm.axiomsAllSingleLiteral_iff
            _ ↔
                (UnaryRuleSquare.splitSecond ctx
                  (clauseWithLiteral A B) C D
                  left right).axiomsAllSingleLiteral :=
              (UnaryRuleSquare.axiomsAllSingleLiteral_splitSecond
                ctx (clauseWithLiteral A B) C D
                left right).symm
      }

/-- A finite derivation of inference interchange between two exact occurrence
proofs. Atomic steps reuse the four corner subproofs at two distinct selected
positions. Context closure preserves the actual parent and both premise slots;
equality of depths or of leaf labels alone cannot construct this certificate. -/
@[blueprint "chap9__lemma_9_2_2"]
inductive InferencePermutationCertificate : {clauses : List Clause} →
    OccurrenceGCNFProof clauses → OccurrenceGCNFProof clauses → Type where
  | refl {clauses} (T : OccurrenceGCNFProof clauses) :
      InferencePermutationCertificate T T
  | symm {clauses} {T U : OccurrenceGCNFProof clauses} :
      InferencePermutationCertificate T U → InferencePermutationCertificate U T
  | trans {clauses} {T U V : OccurrenceGCNFProof clauses} :
      InferencePermutationCertificate T U → InferencePermutationCertificate U V →
        InferencePermutationCertificate T V
  | interchange {ctx : TwoOccurrenceContext} {A C : Clause} {B D : Literal}
      (square : UnaryRuleSquare ctx A C B D) :
      InferencePermutationCertificate square.firstThenSecond square.secondThenFirst
  | underRule {clauses : List Clause} {A : Clause} {B : Literal}
      (selected : RootOccurrence clauses (clauseWithLiteral A B))
      {left left' : OccurrenceGCNFProof (selected.pre ++ A :: selected.post)}
      {right right' : OccurrenceGCNFProof (selected.pre ++ Clause.single B :: selected.post)} :
      InferencePermutationCertificate left left' →
      InferencePermutationCertificate right right' →
      InferencePermutationCertificate (ruleAt selected left right) (ruleAt selected left' right')

end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutationPlan

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutationPlan.execute
