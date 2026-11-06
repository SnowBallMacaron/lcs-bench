import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF
import Attach
import LCS.SLD.SLDForm.Occurrence.CommutingDiamond.ProofsStamp

/-! # Interchanging two rules at distinct root positions

Carrier for the proof of Lemma 9.2.2: two distinct root positions and the atomic commuting diamond of two unary rules, with depth and axiom-leaf invariants. -/

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- A list context with two ordered, distinct occurrence positions.
`pre` precedes the first occurrence, `middle` separates the two positions,
and `post` follows the second.  The clause values inserted at the positions
may be equal; the positions remain distinct. -/
structure TwoOccurrenceContext where
  pre : List Clause
  middle : List Clause
  post : List Clause

namespace TwoOccurrenceContext

/-- Fill both distinguished positions of a two-occurrence context. -/
def fill (ctx : TwoOccurrenceContext)
    (first second : Clause) : List Clause :=
  ctx.pre ++
    (first :: (ctx.middle ++ (second :: ctx.post)))

/-- The exact first position in a filled two-occurrence context. -/
def firstOccurrence (ctx : TwoOccurrenceContext)
    (first second : Clause) :
    RootOccurrence (ctx.fill first second) first :=
  ⟨ctx.pre, ctx.middle ++ (second :: ctx.post), rfl⟩

/-- The exact second position in a filled two-occurrence context. -/
def secondOccurrence (ctx : TwoOccurrenceContext)
    (first second : Clause) :
    RootOccurrence (ctx.fill first second) second :=
  ⟨ctx.pre ++ (first :: ctx.middle), ctx.post, by
    simp only [fill, List.append_assoc, List.cons_append]⟩

/-- Replacing the first distinguished position has exactly the split index
required by `firstOccurrence`. -/
theorem fill_eq_firstReplacement (ctx : TwoOccurrenceContext)
    (selected second replacement : Clause) :
    ctx.fill replacement second =
      (ctx.firstOccurrence selected second).pre ++
        replacement ::
        (ctx.firstOccurrence selected second).post := by
  rfl

/-- Replacing the second distinguished position has exactly the split index
required by `secondOccurrence`. -/
theorem fill_eq_secondReplacement (ctx : TwoOccurrenceContext)
    (first selected replacement : Clause) :
    ctx.fill first replacement =
      (ctx.secondOccurrence first selected).pre ++
        replacement ::
        (ctx.secondOccurrence first selected).post := by
  simp only [fill, secondOccurrence, List.append_assoc,
    List.cons_append]

end TwoOccurrenceContext

/-- The four corner proofs of the commuting square for two unary occurrence
rules.  The first rule replaces its selected clause by `A` or `{B}`; the
second replaces its selected clause by `C` or `{D}`. -/
structure UnaryRuleSquare (ctx : TwoOccurrenceContext)
    (A C : Clause) (B D : Literal) where
  leftLeft : OccurrenceGCNFProof (ctx.fill A C)
  leftRight :
    OccurrenceGCNFProof
      (ctx.fill A (Clause.single D))
  rightLeft :
    OccurrenceGCNFProof
      (ctx.fill (Clause.single B) C)
  rightRight :
    OccurrenceGCNFProof
      (ctx.fill (Clause.single B) (Clause.single D))

namespace UnaryRuleSquare

/-- Assemble a rule at the first distinguished position. -/
def splitFirst (ctx : TwoOccurrenceContext)
    (A : Clause) (B : Literal) (second : Clause)
    (left : OccurrenceGCNFProof (ctx.fill A second))
    (right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single B) second)) :
    OccurrenceGCNFProof
      (ctx.fill (clauseWithLiteral A B) second) := by
  let selected :=
    ctx.firstOccurrence (clauseWithLiteral A B) second
  exact OccurrenceGCNFProof.ruleAt selected
    (OccurrenceGCNFProof.transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B) second A)
      left)
    (OccurrenceGCNFProof.transport
      (ctx.fill_eq_firstReplacement
        (clauseWithLiteral A B) second (Clause.single B))
      right)

/-- Assemble a rule at the second distinguished position. -/
def splitSecond (ctx : TwoOccurrenceContext)
    (first : Clause) (C : Clause) (D : Literal)
    (left : OccurrenceGCNFProof (ctx.fill first C))
    (right :
      OccurrenceGCNFProof
        (ctx.fill first (Clause.single D))) :
    OccurrenceGCNFProof
      (ctx.fill first (clauseWithLiteral C D)) := by
  let selected :=
    ctx.secondOccurrence first (clauseWithLiteral C D)
  exact OccurrenceGCNFProof.ruleAt selected
    (OccurrenceGCNFProof.transport
      (ctx.fill_eq_secondReplacement
        first (clauseWithLiteral C D) C)
      left)
    (OccurrenceGCNFProof.transport
      (ctx.fill_eq_secondReplacement
        first (clauseWithLiteral C D) (Clause.single D))
      right)

/-- Ordinary depth equation for a rule at the first position. -/
theorem depth_splitFirst (ctx : TwoOccurrenceContext)
    (A : Clause) (B : Literal) (second : Clause)
    (left : OccurrenceGCNFProof (ctx.fill A second))
    (right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single B) second)) :
    (splitFirst ctx A B second left right).depth =
      1 + max left.depth right.depth := by
  simp only [splitFirst, OccurrenceGCNFProof.depth_ruleAt,
    OccurrenceGCNFProof.depth_transport]

/-- Ordinary depth equation for a rule at the second position. -/
theorem depth_splitSecond (ctx : TwoOccurrenceContext)
    (first : Clause) (C : Clause) (D : Literal)
    (left : OccurrenceGCNFProof (ctx.fill first C))
    (right :
      OccurrenceGCNFProof
        (ctx.fill first (Clause.single D))) :
    (splitSecond ctx first C D left right).depth =
      1 + max left.depth right.depth := by
  simp only [splitSecond, OccurrenceGCNFProof.depth_ruleAt,
    OccurrenceGCNFProof.depth_transport]

/-- Exact axiom-leaf equation for a split at the first position. -/
theorem axiomLeaves_splitFirst (ctx : TwoOccurrenceContext)
    (A : Clause) (B : Literal) (second : Clause)
    (left : OccurrenceGCNFProof (ctx.fill A second))
    (right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single B) second)) :
    (splitFirst ctx A B second left right).axiomLeaves =
      left.axiomLeaves ++ right.axiomLeaves := by
  simp only [splitFirst, OccurrenceGCNFProof.axiomLeaves_ruleAt,
    OccurrenceGCNFProof.axiomLeaves_transport]

/-- Exact axiom-leaf equation for a split at the second position. -/
theorem axiomLeaves_splitSecond (ctx : TwoOccurrenceContext)
    (first : Clause) (C : Clause) (D : Literal)
    (left : OccurrenceGCNFProof (ctx.fill first C))
    (right :
      OccurrenceGCNFProof
        (ctx.fill first (Clause.single D))) :
    (splitSecond ctx first C D left right).axiomLeaves =
      left.axiomLeaves ++ right.axiomLeaves := by
  simp only [splitSecond, OccurrenceGCNFProof.axiomLeaves_ruleAt,
    OccurrenceGCNFProof.axiomLeaves_transport]

/-- Literal-only axiom leaves are conjunctive across a split at the first
position. -/
theorem axiomsAllSingleLiteral_splitFirst
    (ctx : TwoOccurrenceContext)
    (A : Clause) (B : Literal) (second : Clause)
    (left : OccurrenceGCNFProof (ctx.fill A second))
    (right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single B) second)) :
    (splitFirst ctx A B second left right).axiomsAllSingleLiteral ↔
      left.axiomsAllSingleLiteral ∧
      right.axiomsAllSingleLiteral := by
  simp only [splitFirst,
    OccurrenceGCNFProof.axiomsAllSingleLiteral_ruleAt,
    OccurrenceGCNFProof.axiomsAllSingleLiteral_transport]

/-- Literal-only axiom leaves are conjunctive across a split at the second
position. -/
theorem axiomsAllSingleLiteral_splitSecond
    (ctx : TwoOccurrenceContext)
    (first : Clause) (C : Clause) (D : Literal)
    (left : OccurrenceGCNFProof (ctx.fill first C))
    (right :
      OccurrenceGCNFProof
        (ctx.fill first (Clause.single D))) :
    (splitSecond ctx first C D left right).axiomsAllSingleLiteral ↔
      left.axiomsAllSingleLiteral ∧
      right.axiomsAllSingleLiteral := by
  simp only [splitSecond,
    OccurrenceGCNFProof.axiomsAllSingleLiteral_ruleAt,
    OccurrenceGCNFProof.axiomsAllSingleLiteral_transport]

/-- A split assembled at the first position exposes that exact root
occurrence. -/
def rootRuleAt_splitFirst (ctx : TwoOccurrenceContext)
    (A : Clause) (B : Literal) (second : Clause)
    (left : OccurrenceGCNFProof (ctx.fill A second))
    (right :
      OccurrenceGCNFProof
        (ctx.fill (Clause.single B) second)) :
    OccurrenceGCNFProof.RootRuleAt
      (splitFirst ctx A B second left right)
      (ctx.firstOccurrence (clauseWithLiteral A B) second) := by
  refine
    { left :=
        OccurrenceGCNFProof.transport
          (ctx.fill_eq_firstReplacement
            (clauseWithLiteral A B) second A)
          left
      right :=
        OccurrenceGCNFProof.transport
          (ctx.fill_eq_firstReplacement
            (clauseWithLiteral A B) second
            (Clause.single B))
          right
      tree_eq := ?_ }
  rfl

/-- A split assembled at the second position exposes that exact root
occurrence. -/
def rootRuleAt_splitSecond (ctx : TwoOccurrenceContext)
    (first : Clause) (C : Clause) (D : Literal)
    (left : OccurrenceGCNFProof (ctx.fill first C))
    (right :
      OccurrenceGCNFProof
        (ctx.fill first (Clause.single D))) :
    OccurrenceGCNFProof.RootRuleAt
      (splitSecond ctx first C D left right)
      (ctx.secondOccurrence first (clauseWithLiteral C D)) := by
  refine
    { left :=
        OccurrenceGCNFProof.transport
          (ctx.fill_eq_secondReplacement
            first (clauseWithLiteral C D) C)
          left
      right :=
        OccurrenceGCNFProof.transport
          (ctx.fill_eq_secondReplacement
            first (clauseWithLiteral C D)
            (Clause.single D))
          right
      tree_eq := ?_ }
  rfl

/-- First apply the rule at the first position, then the rule at the second
position in each premise. -/
def firstThenSecond {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    OccurrenceGCNFProof
      (ctx.fill (clauseWithLiteral A B)
        (clauseWithLiteral C D)) :=
  splitFirst ctx A B (clauseWithLiteral C D)
    (splitSecond ctx A C D
      square.leftLeft square.leftRight)
    (splitSecond ctx (Clause.single B) C D
      square.rightLeft square.rightRight)

/-- First apply the rule at the second position, then the rule at the first
position in each premise. -/
def secondThenFirst {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    OccurrenceGCNFProof
      (ctx.fill (clauseWithLiteral A B)
        (clauseWithLiteral C D)) :=
  splitSecond ctx (clauseWithLiteral A B) C D
    (splitFirst ctx A B C
      square.leftLeft square.rightLeft)
    (splitFirst ctx A B (Clause.single D)
      square.leftRight square.rightRight)

/-- Expanded ordinary-depth equation for the first-then-second side of the
commuting diamond. -/
theorem depth_firstThenSecond {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.firstThenSecond.depth =
      2 + max
        (max square.leftLeft.depth square.leftRight.depth)
        (max square.rightLeft.depth
          square.rightRight.depth) := by
  rw [firstThenSecond, depth_splitFirst,
    depth_splitSecond, depth_splitSecond]
  omega

/-- Expanded ordinary-depth equation for the second-then-first side of the
commuting diamond. -/
theorem depth_secondThenFirst {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.depth =
      2 + max
        (max square.leftLeft.depth square.rightLeft.depth)
        (max square.leftRight.depth
          square.rightRight.depth) := by
  rw [secondThenFirst, depth_splitSecond,
    depth_splitFirst, depth_splitFirst]
  omega

/-- Commuting the two distinct-position rules preserves ordinary proof depth
exactly. -/
theorem depth_commute {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.depth =
      square.firstThenSecond.depth := by
  rw [depth_secondThenFirst, depth_firstThenSecond]
  omega

/-- Expanded axiom-leaf equation for the first-then-second side. -/
theorem axiomLeaves_firstThenSecond
    {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.firstThenSecond.axiomLeaves =
      (square.leftLeft.axiomLeaves ++
        square.leftRight.axiomLeaves) ++
      (square.rightLeft.axiomLeaves ++
        square.rightRight.axiomLeaves) := by
  rw [firstThenSecond, axiomLeaves_splitFirst,
    axiomLeaves_splitSecond, axiomLeaves_splitSecond]

/-- Expanded axiom-leaf equation for the second-then-first side. -/
theorem axiomLeaves_secondThenFirst
    {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.axiomLeaves =
      (square.leftLeft.axiomLeaves ++
        square.rightLeft.axiomLeaves) ++
      (square.leftRight.axiomLeaves ++
        square.rightRight.axiomLeaves) := by
  rw [secondThenFirst, axiomLeaves_splitSecond,
    axiomLeaves_splitFirst, axiomLeaves_splitFirst]

/-- The commuting conversion preserves every axiom leaf with multiplicity;
only the left-to-right enumeration order changes. -/
theorem axiomLeaves_commute {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.axiomLeaves.Perm
      square.firstThenSecond.axiomLeaves := by
  rw [axiomLeaves_secondThenFirst,
    axiomLeaves_firstThenSecond]
  simpa only [List.append_assoc] using
    List.Perm.append_left square.leftLeft.axiomLeaves
      (List.Perm.append_right
        square.rightRight.axiomLeaves
        (List.perm_append_comm :
          (square.rightLeft.axiomLeaves ++
            square.leftRight.axiomLeaves).Perm
          (square.leftRight.axiomLeaves ++
            square.rightLeft.axiomLeaves)))

/-- The first-then-second tree has literal-only axiom leaves exactly when all
four corner proofs do. -/
theorem axiomsAllSingleLiteral_firstThenSecond
    {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.firstThenSecond.axiomsAllSingleLiteral ↔
      square.leftLeft.axiomsAllSingleLiteral ∧
      square.leftRight.axiomsAllSingleLiteral ∧
      square.rightLeft.axiomsAllSingleLiteral ∧
      square.rightRight.axiomsAllSingleLiteral := by
  rw [firstThenSecond, axiomsAllSingleLiteral_splitFirst,
    axiomsAllSingleLiteral_splitSecond,
    axiomsAllSingleLiteral_splitSecond]
  constructor
  · rintro ⟨⟨hLL, hLR⟩, hRL, hRR⟩
    exact ⟨hLL, hLR, hRL, hRR⟩
  · rintro ⟨hLL, hLR, hRL, hRR⟩
    exact ⟨⟨hLL, hLR⟩, hRL, hRR⟩

/-- The second-then-first tree has literal-only axiom leaves exactly when all
four corner proofs do. -/
theorem axiomsAllSingleLiteral_secondThenFirst
    {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.axiomsAllSingleLiteral ↔
      square.leftLeft.axiomsAllSingleLiteral ∧
      square.leftRight.axiomsAllSingleLiteral ∧
      square.rightLeft.axiomsAllSingleLiteral ∧
      square.rightRight.axiomsAllSingleLiteral := by
  rw [secondThenFirst, axiomsAllSingleLiteral_splitSecond,
    axiomsAllSingleLiteral_splitFirst,
    axiomsAllSingleLiteral_splitFirst]
  constructor
  · rintro ⟨⟨hLL, hRL⟩, hLR, hRR⟩
    exact ⟨hLL, hLR, hRL, hRR⟩
  · rintro ⟨hLL, hLR, hRL, hRR⟩
    exact ⟨⟨hLL, hRL⟩, hLR, hRR⟩

/-- Commuting the two rules preserves the literal-only axiom condition in
both directions. -/
theorem axiomsAllSingleLiteral_commute
    {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    square.secondThenFirst.axiomsAllSingleLiteral ↔
      square.firstThenSecond.axiomsAllSingleLiteral := by
  rw [axiomsAllSingleLiteral_secondThenFirst,
    axiomsAllSingleLiteral_firstThenSecond]

/-- Move the rule at the second list position above the rule at the first.
The returned root certificate names the exact second occurrence, including its
prefix and suffix. -/
def commuteSecondToRoot {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    OccurrenceGCNFProof.RootPermutation
      square.firstThenSecond
      (ctx.secondOccurrence
        (clauseWithLiteral A B)
        (clauseWithLiteral C D)) where
  tree := square.secondThenFirst
  rooted :=
    rootRuleAt_splitSecond ctx
      (clauseWithLiteral A B) C D
      (splitFirst ctx A B C
        square.leftLeft square.rightLeft)
      (splitFirst ctx A B (Clause.single D)
        square.leftRight square.rightRight)
  depth_eq := depth_commute square
  axiomLeaves_perm := axiomLeaves_commute square
  axiomsAllSingleLiteral_iff :=
    axiomsAllSingleLiteral_commute square

/-- Move the rule at the first list position above the rule at the second.
This is the other ordering of the distinct-position case. -/
def commuteFirstToRoot {ctx : TwoOccurrenceContext}
    {A C : Clause} {B D : Literal}
    (square : UnaryRuleSquare ctx A C B D) :
    OccurrenceGCNFProof.RootPermutation
      square.secondThenFirst
      (ctx.firstOccurrence
        (clauseWithLiteral A B)
        (clauseWithLiteral C D)) where
  tree := square.firstThenSecond
  rooted :=
    rootRuleAt_splitFirst ctx A B
      (clauseWithLiteral C D)
      (splitSecond ctx A C D
        square.leftLeft square.leftRight)
      (splitSecond ctx (Clause.single B) C D
        square.rightLeft square.rightRight)
  depth_eq := (depth_commute square).symm
  axiomLeaves_perm := (axiomLeaves_commute square).symm
  axiomsAllSingleLiteral_iff :=
    (axiomsAllSingleLiteral_commute square).symm

end UnaryRuleSquare
end LCS.SLD.SLDForm.Occurrence
end

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.fill

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.firstThenSecond

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.secondThenFirst

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.firstOccurrence

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.secondOccurrence

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.splitFirst

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.splitSecond
