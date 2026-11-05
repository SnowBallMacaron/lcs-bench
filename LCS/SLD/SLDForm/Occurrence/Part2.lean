import LCS.Item
import LCS.Util
import Attach
import LCS.SLD.SLDForm.Occurrence.Part2.ProofsStamp
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.Part1
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
section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFProof
namespace InferencePermutationCertificate
def ofEq {clauses : List Clause} {T U : OccurrenceGCNFProof clauses}
    (h : T = U) : InferencePermutationCertificate T U := by
  cases h; exact .refl _
def cast {xs ys : List Clause} (h : xs = ys)
    {T U : OccurrenceGCNFProof xs} (c : InferencePermutationCertificate T U) :
    InferencePermutationCertificate (transport h T) (transport h U) := by
  cases h; exact c

def splitFirst (ctx : TwoOccurrenceContext) (A : Clause) (B : Literal) (C : Clause)
    {l l' : OccurrenceGCNFProof (ctx.fill A C)}
    {r r' : OccurrenceGCNFProof (ctx.fill (Clause.single B) C)}
    (hl : InferencePermutationCertificate l l') (hr : InferencePermutationCertificate r r') :
    InferencePermutationCertificate (UnaryRuleSquare.splitFirst ctx A B C l r)
      (UnaryRuleSquare.splitFirst ctx A B C l' r') :=
  .underRule _ (hl.cast _) (hr.cast _)

def splitSecond (ctx : TwoOccurrenceContext) (A C : Clause) (D : Literal)
    {l l' : OccurrenceGCNFProof (ctx.fill A C)}
    {r r' : OccurrenceGCNFProof (ctx.fill A (Clause.single D))}
    (hl : InferencePermutationCertificate l l') (hr : InferencePermutationCertificate r r') :
    InferencePermutationCertificate (UnaryRuleSquare.splitSecond ctx A C D l r)
      (UnaryRuleSquare.splitSecond ctx A C D l' r') :=
  .underRule _ (hl.cast _) (hr.cast _)

end InferencePermutationCertificate
end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFProof

theorem transport_roundtrip {xs ys : List Clause} (h : xs = ys)
    (T : OccurrenceGCNFProof ys) : transport h (transport h.symm T) = T := by
  cases h; rfl

/-- The finite interchange certificate follows the actual executor output. -/
def RootPermutationPlan.permutationCertificate
    {clauses : List Clause} {source : OccurrenceGCNFProof clauses}
    {A : Clause} {B : Literal}
    {target : RootOccurrence clauses (clauseWithLiteral A B)}
    (plan : RootPermutationPlan source target) :
    InferencePermutationCertificate source plan.execute.tree :=
  match plan with
  | .atRoot _ => .refl _
  | .belowFirst ctx C A D B _ _ lp rp => by
    let ihL := lp.permutationCertificate
    let ihR := rp.permutationCertificate
    let square := belowFirstSquare ctx C A D B lp.execute rp.execute
    have hMid : square.firstThenSecond =
        UnaryRuleSquare.splitFirst ctx C D (clauseWithLiteral A B)
          lp.execute.tree rp.execute.tree := by
      unfold UnaryRuleSquare.firstThenSecond
      congr 1
      · rw [lp.execute.rooted.tree_eq]
        simp [square, belowFirstSquare, UnaryRuleSquare.splitSecond, transport_roundtrip]
      · rw [rp.execute.rooted.tree_eq]
        simp [square, belowFirstSquare, UnaryRuleSquare.splitSecond, transport_roundtrip]
    have c := InferencePermutationCertificate.splitFirst ctx C D
      (clauseWithLiteral A B) ihL ihR
    rw [← hMid] at c
    exact .trans c (.interchange square)
  | .belowSecond ctx A C B D _ _ lp rp => by
    let ihL := lp.permutationCertificate
    let ihR := rp.permutationCertificate
    let square := belowSecondSquare ctx A C B D lp.execute rp.execute
    have hMid : square.secondThenFirst =
        UnaryRuleSquare.splitSecond ctx (clauseWithLiteral A B) C D
          lp.execute.tree rp.execute.tree := by
      unfold UnaryRuleSquare.secondThenFirst
      congr 1
      · rw [lp.execute.rooted.tree_eq]
        simp [square, belowSecondSquare, UnaryRuleSquare.splitFirst, transport_roundtrip]
      · rw [rp.execute.rooted.tree_eq]
        simp [square, belowSecondSquare, UnaryRuleSquare.splitFirst, transport_roundtrip]
    have c := InferencePermutationCertificate.splitSecond ctx
      (clauseWithLiteral A B) C D ihL ihR
    rw [← hMid] at c
    exact .trans c (.symm (.interchange square))

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

/-- The recursive residual represents exactly `A` union the literals in the
order. -/
theorem partitionResidual_eq_union
    (A : Clause) (order : List Literal) :
    partitionResidual A order =
      Clause.union A (Clause.ofList order) := by
  induction order with
  | nil =>
      apply LCS.Finset.ext
      intro l
      simp [partitionResidual, Clause.union, Clause.ofList]
  | cons b bs ih =>
      rw [partitionResidual, ih]
      apply LCS.Finset.ext
      intro l
      simp only [clauseWithLiteral, Clause.union,
        Clause.ofList, LCS.Finset.mem_insert,
        LCS.Finset.mem_union, LCS.Finset.mem_ofList,
        List.mem_cons]
      constructor
      · rintro (hlb | hA | hbs)
        · exact Or.inr (Or.inl hlb)
        · exact Or.inl hA
        · exact Or.inr (Or.inr hbs)
      · rintro (hA | hlb | hbs)
        · exact Or.inr (Or.inl hA)
        · exact Or.inl hlb
        · exact Or.inr (Or.inr hbs)

/-- The chosen list representative of a clause has no duplicate literals. -/
theorem clause_toList_nodup (C : Clause) :
    C.toList.Nodup := by
  have hNodup : C.val.Nodup := C.nodup
  rw [← C.toList_ofList_eq] at hNodup
  exact hNodup

/-- A partition equality identifies the target clause with the residual
obtained by enumerating the right partition using `B.toList`. -/
theorem partitionResidual_toList_eq_of_partition
    {C A B : Clause}
    (hPart : C = Clause.union A B) :
    C = partitionResidual A B.toList := by
  calc
    C = Clause.union A B := hPart
    _ = Clause.union A (Clause.ofList B.toList) := by
      rw [ofList_toList_eq B]
    _ = partitionResidual A B.toList :=
      (partitionResidual_eq_union A B.toList).symm

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

/-- Execute every planned root move and rebuild the already-exposed prefix
while preserving exact ordinary depth and the full axiom-leaf multiset. -/
@[blueprint "chap9__lemma_9_2_2"]
def RootPartitionPlan.execute
    {A : Clause}
    {clauses : List Clause}
    {source : OccurrenceGCNFProof clauses}
    {order : List Literal}
    {target :
      RootOccurrence clauses (partitionResidual A order)}
    (plan : RootPartitionPlan A source order target) :
    OrderedRootPartitionPermutation A source order target :=
  match plan with
  | .last headPlan =>
      let headPerm := headPlan.execute
      {
        tree := headPerm.tree
        rootedMacro := .last headPerm.rooted
        depth_eq := headPerm.depth_eq
        axiomLeaves_perm := headPerm.axiomLeaves_perm
        axiomsAllSingleLiteral_iff :=
          headPerm.axiomsAllSingleLiteral_iff
      }
  | .cons headPlan tailPlan =>
      let headPerm := headPlan.execute
      let tailPerm := tailPlan.execute
      let rebuilt :=
        ruleAt target tailPerm.tree headPerm.rooted.right
      let rebuiltRooted : RootRuleAt rebuilt target :=
        {
          left := tailPerm.tree
          right := headPerm.rooted.right
          tree_eq := rfl
        }
      {
        tree := rebuilt
        rootedMacro :=
          .cons rebuiltRooted tailPerm.rootedMacro
        depth_eq := by
          calc
            rebuilt.depth =
                1 + max tailPerm.tree.depth
                  headPerm.rooted.right.depth :=
              depth_ruleAt target tailPerm.tree
                headPerm.rooted.right
            _ =
                1 + max headPerm.rooted.left.depth
                  headPerm.rooted.right.depth := by
              rw [tailPerm.depth_eq]
            _ = headPerm.tree.depth :=
              headPerm.rooted.depth_eq.symm
            _ = _ := headPerm.depth_eq
        axiomLeaves_perm := by
          have hRebuiltToHead :
              rebuilt.axiomLeaves.Perm
                headPerm.tree.axiomLeaves := by
            change (ruleAt target tailPerm.tree headPerm.rooted.right).axiomLeaves.Perm _
            erw [axiomLeaves_ruleAt,
              headPerm.rooted.axiomLeaves_eq]
            exact
              tailPerm.axiomLeaves_perm.append_right
                headPerm.rooted.right.axiomLeaves
          exact hRebuiltToHead.trans
            headPerm.axiomLeaves_perm
        axiomsAllSingleLiteral_iff := by
          calc
            rebuilt.axiomsAllSingleLiteral ↔
                tailPerm.tree.axiomsAllSingleLiteral ∧
                  headPerm.rooted.right.axiomsAllSingleLiteral :=
              axiomsAllSingleLiteral_ruleAt target
                tailPerm.tree headPerm.rooted.right
            _ ↔
                headPerm.rooted.left.axiomsAllSingleLiteral ∧
                  headPerm.rooted.right.axiomsAllSingleLiteral :=
              and_congr
                tailPerm.axiomsAllSingleLiteral_iff Iff.rfl
            _ ↔ headPerm.tree.axiomsAllSingleLiteral :=
              headPerm.rooted.axiomsAllSingleLiteral_iff.symm
            _ ↔ _ :=
              headPerm.axiomsAllSingleLiteral_iff
      }

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

/-- Execute a checked `B.toList` partition plan and package the exact
occurrence-level certificate.  Totality is deliberately conditional on the
data-bearing plan; no unverified arbitrary-tree permutation is assumed. -/
noncomputable def RootPartitionPlan.executeToList
    {clauses : List Clause}
    {source : OccurrenceGCNFProof clauses}
    {C : Clause}
    (target : RootOccurrence clauses C)
    (A B : Clause)
    (hA : ∃ a, a ∈ A)
    (hB : ∃ b, b ∈ B)
    (hDisjoint : ∀ l, l ∈ A → l ∉ B)
    (hPart : C = Clause.union A B)
    (plan :
      RootPartitionPlan A source B.toList
        (target.castClause
          (partitionResidual_toList_eq_of_partition hPart))) :
    RootPartitionPermutation source target A B :=
  let target_eq :=
    partitionResidual_toList_eq_of_partition hPart
  let ordered := plan.execute
  {
    tree := ordered.tree
    certificate := {
      leftNonempty := hA
      rightNonempty := hB
      disjoint := hDisjoint
      unionEq := hPart
      orderNodup := clause_toList_nodup B
      orderEq := ofList_toList_eq B
      target_eq := target_eq
      rootedMacro := ordered.rootedMacro
    }
    depth_eq := ordered.depth_eq
    axiomLeaves_perm := ordered.axiomLeaves_perm
    axiomsAllSingleLiteral_iff :=
      ordered.axiomsAllSingleLiteral_iff
  }

/-- Compose the head and residual-spine interchanges for the exact output
of the supplied partition plan. This does not construct a plan from a tree. -/
def RootPartitionPlan.permutationCertificate
    {A : Clause} {clauses : List Clause} {source : OccurrenceGCNFProof clauses}
    {order : List Literal} {target : RootOccurrence clauses (partitionResidual A order)}
    (plan : RootPartitionPlan A source order target) :
    InferencePermutationCertificate source plan.execute.tree :=
  match plan with
  | .last headPlan => headPlan.permutationCertificate
  | .cons headPlan tailPlan => by
    have c : InferencePermutationCertificate headPlan.execute.tree
        (ruleAt _ tailPlan.execute.tree headPlan.execute.rooted.right) := by
      exact .trans (.ofEq headPlan.execute.rooted.tree_eq)
        (.underRule _ tailPlan.permutationCertificate (.refl _))
    exact .trans headPlan.permutationCertificate c

/-- The exact target occurrence recorded by a partition certificate is a
member of the root occurrence list. -/
theorem RootPartitionCertificate.target_mem
    {clauses : List Clause}
    {T : OccurrenceGCNFProof clauses}
    {C A B : Clause}
    {target : RootOccurrence clauses C}
    (_h : RootPartitionCertificate T target A B) :
    C ∈ clauses :=
  target.mem

end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- An occurrence-preserving derivation of an extensional clause sequent.
The root list is duplicate-free, so it contains exactly one occurrence for
each clause in `S`; internal rule premises may contain equal clauses at
different positions and intentionally retain that multiplicity. -/
structure OccurrenceGCNFDerivation (S : ClauseSequent) where
  occurrences : List Clause
  nodupRoot : occurrences.Nodup
  erase_eq : ClauseSequent.ofList occurrences = S
  tree : OccurrenceGCNFProof occurrences

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFDerivation

/-- Root-list membership agrees with membership in the extensional root
sequent. -/
theorem mem_occurrences_iff {S : ClauseSequent}
    (D : OccurrenceGCNFDerivation S) (C : Clause) :
    C ∈ D.occurrences ↔ C ∈ S := by
  constructor
  · intro hC
    have hErase :
        C ∈ ClauseSequent.ofList D.occurrences :=
      (LCS.Finset.mem_ofList_exp C D.occurrences).mpr hC
    rw [D.erase_eq] at hErase
    exact hErase
  · intro hC
    have hErase :
        C ∈ ClauseSequent.ofList D.occurrences := by
      rw [D.erase_eq]
      exact hC
    exact
      (LCS.Finset.mem_ofList_exp C D.occurrences).mp hErase

/-- Membership in the extensional root supplies an exact occurrence witness;
no arbitrary sentinel is selected. -/
theorem rootOccurrence {S : ClauseSequent}
    (D : OccurrenceGCNFDerivation S) {C : Clause}
    (hC : C ∈ S) :
    Nonempty (RootOccurrence D.occurrences C) :=
  RootOccurrence.of_mem ((D.mem_occurrences_iff C).mpr hC)

end OccurrenceGCNFDerivation
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- Erase occurrence multiplicity from a clause list. -/
@[blueprint "chap9__lemma_9_2_2"]
def eraseOccurrences (clauses : List Clause) : ClauseSequent :=
  ClauseSequent.ofList clauses

/-- Erasure preserves exactly list membership, while forgetting duplicate
occurrences. -/
theorem mem_eraseOccurrences_iff (clauses : List Clause) (C : Clause) :
    C ∈ eraseOccurrences clauses ↔ C ∈ clauses :=
  LCS.Finset.mem_ofList_exp C clauses

/-- The chosen list representative of a finite set is duplicate-free. -/
theorem clauseSequent_toList_nodup (S : ClauseSequent) :
    S.toList.Nodup := by
  have hNodup : S.val.Nodup := S.nodup
  rw [← S.toList_ofList_eq] at hNodup
  exact hNodup

/-- Erasing the chosen list representative recovers the original finite set. -/
theorem eraseOccurrences_toList (S : ClauseSequent) :
    eraseOccurrences S.toList = S := by
  apply LCS.Finset.ext
  intro C
  rw [mem_eraseOccurrences_iff, LCS.Finset.mem_toList]

/-! ## One-way compression to the existing GCNF' carrier -/

/-- Transport a finite-set GCNF' proof along equality of its indexed root.
Keeping this operation local makes the casts inserted by compression explicit. -/
def transportGCNFProofTree {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) :
    GCNFProofTree S' :=
  h ▸ T

/-- The image of a singleton principal set is the singleton containing the
corresponding extended clause. -/
theorem mapSet_singleton_clauseWithLiteral
    (A : Clause) (B : Literal) :
    ClauseSequent.mapSet (ClauseSequent.single A)
        (fun C => clauseWithLiteral C B) =
      ClauseSequent.single (clauseWithLiteral A B) := by
  apply LCS.Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨A', hA', hEq⟩ :=
      (mem_image_iff
        (fun X => clauseWithLiteral X B)
        (ClauseSequent.single A) C).mp hC
    have hAeq : A' = A :=
      (mem_csingle A' A).mp hA'
    subst A'
    exact (mem_csingle C (clauseWithLiteral A B)).mpr hEq.symm
  · intro hC
    have hEq : C = clauseWithLiteral A B :=
      (mem_csingle C (clauseWithLiteral A B)).mp hC
    exact
      (mem_image_iff
        (fun X => clauseWithLiteral X B)
        (ClauseSequent.single A) C).mpr
        ⟨A, (mem_csingle A A).mpr rfl, hEq.symm⟩

/-- Compress an occurrence proof to the existing finite-set GCNF' proof tree.
Literal-only axiom leaves certify ordinariness of every clause used in the
compressed tree. Every occurrence rule becomes a singleton-`As`, singleton-`Cs`
rule with the same context in both premises. -/
@[blueprint "chap9__lemma_9_2_2"]
def compress :
    {clauses : List Clause} →
    (T : OccurrenceGCNFProof clauses) →
    T.axiomsAllSingleLiteral →
    GCNFProofTree (eraseOccurrences clauses)
  | _, .axiom_ clauses hTriv, hLeaves => by
      exact
        .axiom_ (eraseOccurrences clauses)
          (by
            intro C hC
            obtain ⟨L, rfl⟩ := hLeaves C ((mem_eraseOccurrences_iff clauses C).mp hC)
            exact Clause.single_ordinary L)
          (by
            rcases hTriv with ⟨P, hPos, hNeg⟩
            exact
              ⟨P,
                (mem_eraseOccurrences_iff clauses
                  (Clause.single (Literal.pos P))).mpr hPos,
                (mem_eraseOccurrences_iff clauses
                  (Clause.single (Literal.neg P))).mpr hNeg⟩)
  | _, .rule pre post A B left right, hLeaves => by
      let Gamma : ClauseSequent :=
        eraseOccurrences (pre ++ post)
      have hLeft :
          eraseOccurrences (pre ++ A :: post) =
            LCS.Finset.union Gamma (ClauseSequent.single A) :=
        ofList_replace_eq_union pre post A
      have hRight :
          eraseOccurrences (pre ++ Clause.single B :: post) =
            LCS.Finset.union Gamma
              (ClauseSequent.single (Clause.single B)) :=
        ofList_replace_eq_union pre post (Clause.single B)
      have hConclusion :
          eraseOccurrences
              (pre ++ clauseWithLiteral A B :: post) =
            LCS.Finset.union Gamma
              (ClauseSequent.mapSet (ClauseSequent.single A)
                (fun C => clauseWithLiteral C B)) := by
        rw [mapSet_singleton_clauseWithLiteral]
        exact ofList_replace_eq_union pre post
          (clauseWithLiteral A B)
      let leftTree :
          GCNFProofTree
            (LCS.Finset.union Gamma (ClauseSequent.single A)) :=
        transportGCNFProofTree hLeft (compress left hLeaves.1)
      let rightTree :
          GCNFProofTree
            (LCS.Finset.union Gamma
              (ClauseSequent.single (Clause.single B))) :=
        transportGCNFProofTree hRight (compress right hLeaves.2)
      let ruleTree :
          GCNFProofTree
            (LCS.Finset.union Gamma
              (ClauseSequent.mapSet (ClauseSequent.single A)
                (fun C => clauseWithLiteral C B))) :=
        .rule Gamma (ClauseSequent.single A) B
          (ClauseSequent.single A) Gamma Gamma
          (ClauseSequent.ordinary_subset leftTree.ordinary
            (fun C hC => LCS.Finset.mem_union.mpr (Or.inl hC)))
          (ClauseSequent.ordinary_subset leftTree.ordinary
            (fun C hC => LCS.Finset.mem_union.mpr (Or.inr hC)))
          leftTree rightTree
          ⟨A, (mem_csingle A A).mpr rfl⟩
          (fun _ hC => hC)
          (fun _ hC =>
            (LCS.Finset.mem_union_exp _ Gamma _).mpr
              (Or.inl hC))
          (fun _ hC =>
            (LCS.Finset.mem_union_exp _ Gamma _).mpr
              (Or.inl hC))
      exact transportGCNFProofTree hConclusion.symm ruleTree

/-! ## Compression invariants available below `Completeness` -/

/-- Chapter-9-local structural predicate saying that every compressed rule is
unary and uses exactly the same context in both premises.  Axiom nodes have no
rule-shape obligation. -/
def IsUnaryOccurrenceCompression :
    {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _ _ => True
  | _, .rule Gamma As _B Cs Gamma1 Gamma2 _ _ left right _ _ _ _ =>
      (∃ A : Clause,
        As = ClauseSequent.single A ∧
        Cs = ClauseSequent.single A) ∧
      Gamma1 = Gamma ∧
      Gamma2 = Gamma ∧
      IsUnaryOccurrenceCompression left ∧
      IsUnaryOccurrenceCompression right

/-- A local old-tree depth recurrence.  A later adapter can identify it with
the `proofDepth` declaration in `Completeness` without introducing an import
cycle here. -/
def gcnfDepth : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ _ _ => 0
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _ =>
      1 + max (gcnfDepth left) (gcnfDepth right)

theorem isUnaryOccurrenceCompression_transport
    {S S' : ClauseSequent} (h : S = S')
    (T : GCNFProofTree S) :
    IsUnaryOccurrenceCompression
        (transportGCNFProofTree h T) ↔
      IsUnaryOccurrenceCompression T := by
  subst S'
  rfl

theorem gcnfDepth_transport
    {S S' : ClauseSequent} (h : S = S')
    (T : GCNFProofTree S) :
    gcnfDepth (transportGCNFProofTree h T) =
      gcnfDepth T := by
  subst S'
  rfl

theorem axiomsAllSingleLiteral_transport
    {S S' : ClauseSequent} (h : S = S')
    (T : GCNFProofTree S) :
    GCNFProofTree.axiomsAllSingleLiteral
        (transportGCNFProofTree h T) ↔
      GCNFProofTree.axiomsAllSingleLiteral T := by
  subst S'
  rfl

/-- Compression always has the exact singleton/no-weakening rule shape. -/
theorem compress_isUnaryOccurrenceCompression
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    (hLeaves : T.axiomsAllSingleLiteral) :
    IsUnaryOccurrenceCompression (compress T hLeaves) := by
  revert hLeaves
  induction T with
  | axiom_ =>
      intro hLeaves
      simp [compress, IsUnaryOccurrenceCompression]
  | rule pre post A B left right ihLeft ihRight =>
      intro hLeaves
      simp only [compress]
      rw [isUnaryOccurrenceCompression_transport]
      simp only [IsUnaryOccurrenceCompression]
      refine
        ⟨⟨A, rfl, rfl⟩, trivial, trivial, ?_, ?_⟩
      · exact
          (isUnaryOccurrenceCompression_transport
            (ofList_replace_eq_union pre post A)
            (compress left hLeaves.1)).2 (ihLeft hLeaves.1)
      · exact
          (isUnaryOccurrenceCompression_transport
            (ofList_replace_eq_union pre post
              (Clause.single B))
            (compress right hLeaves.2)).2 (ihRight hLeaves.2)

/-- Compression preserves ordinary proof depth exactly. -/
theorem gcnfDepth_compress
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    (hLeaves : T.axiomsAllSingleLiteral) :
    gcnfDepth (compress T hLeaves) = T.depth := by
  revert hLeaves
  induction T with
  | axiom_ =>
      intro hLeaves
      simp [compress, gcnfDepth, OccurrenceGCNFProof.depth]
  | rule pre post A B left right ihLeft ihRight =>
      intro hLeaves
      simp only [compress]
      rw [gcnfDepth_transport]
      simp only [gcnfDepth]
      erw [gcnfDepth_transport, gcnfDepth_transport,
        ihLeft, ihRight]
      rfl

/-- Compression preserves the literal-only axiom condition. -/
theorem compress_axiomsAllSingleLiteral
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    (hLeaves : T.axiomsAllSingleLiteral) :
    GCNFProofTree.axiomsAllSingleLiteral (compress T hLeaves) := by
  revert hLeaves
  induction T with
  | axiom_ root hTriv =>
      intro hLeaves
      intro C hC
      exact
        hLeaves C
          ((mem_eraseOccurrences_iff root C).mp hC)
  | rule pre post A B left right ihLeft ihRight =>
      intro hLeaves
      simp only [OccurrenceGCNFProof.axiomsAllSingleLiteral] at hLeaves
      simp only [compress]
      rw [axiomsAllSingleLiteral_transport]
      simp only [GCNFProofTree.axiomsAllSingleLiteral]
      constructor
      · apply
          (axiomsAllSingleLiteral_transport
            (ofList_replace_eq_union pre post A)
            (compress left hLeaves.1)).2
        exact ihLeft hLeaves.1
      · apply
          (axiomsAllSingleLiteral_transport
            (ofList_replace_eq_union pre post
              (Clause.single B))
            (compress right hLeaves.2)).2
        exact ihRight hLeaves.2

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFDerivation

/-- Compress a root derivation to a finite-set GCNF' proof of the same
extensional sequent. -/
def compress {S : ClauseSequent}
    (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    GCNFProofTree S :=
  transportGCNFProofTree D.erase_eq
    (Occurrence.compress D.tree hD)

theorem compress_isUnaryOccurrenceCompression
    {S : ClauseSequent} (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    IsUnaryOccurrenceCompression (D.compress hD) :=
  (isUnaryOccurrenceCompression_transport D.erase_eq
    (Occurrence.compress D.tree hD)).2
    (Occurrence.compress_isUnaryOccurrenceCompression D.tree hD)

theorem gcnfDepth_compress
    {S : ClauseSequent} (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    Occurrence.gcnfDepth (D.compress hD) = D.tree.depth := by
  erw [OccurrenceGCNFDerivation.compress,
    Occurrence.gcnfDepth_transport]
  exact Occurrence.gcnfDepth_compress D.tree hD

theorem compress_axiomsAllSingleLiteral
    {S : ClauseSequent} (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    GCNFProofTree.axiomsAllSingleLiteral (D.compress hD) :=
  (Occurrence.axiomsAllSingleLiteral_transport D.erase_eq
    (Occurrence.compress D.tree hD)).2
    (Occurrence.compress_axiomsAllSingleLiteral D.tree hD)

end OccurrenceGCNFDerivation
end LCS.SLD.SLDForm.Occurrence
end


attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.OrderedRootPartitionPermutation.axiomsAllSingleLiteral_iff

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPartitionMacro

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutationPlan

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutationPlan.execute
