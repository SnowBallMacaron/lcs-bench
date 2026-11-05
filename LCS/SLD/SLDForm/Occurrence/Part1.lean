import LCS.Item
import LCS.Util
import Attach
import LCS.SLD.SLDForm.Occurrence.Part1.ProofsStamp
import LCS.SLD.SLDForm

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

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace OccurrenceGCNFProof

/-- The exact occurrence list at the root of an occurrence proof. -/
def conclusion {clauses : List Clause}
    (_ : OccurrenceGCNFProof clauses) : List Clause :=
  clauses

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

/-- A finite occurrence proof always has at least one axiom leaf. -/
theorem axiomLeaves_nonempty {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses) :
    T.axiomLeaves ≠ [] := by
  induction T with
  | axiom_ =>
      simp [axiomLeaves]
  | rule _ _ _ _ left right ihLeft _ihRight =>
      intro hEmpty
      change left.axiomLeaves ++ right.axiomLeaves = [] at hEmpty
      cases hLeaves : left.axiomLeaves with
      | nil =>
          exact ihLeft hLeaves
      | cons leaf leaves =>
          simp [hLeaves] at hEmpty

/-- The recursive literal-leaf predicate is equivalent to checking every
occurrence list returned by `axiomLeaves`. -/
theorem axiomsAllSingleLiteral_iff_axiomLeaves
    {clauses : List Clause} (T : OccurrenceGCNFProof clauses) :
    T.axiomsAllSingleLiteral ↔
      ∀ leaf ∈ T.axiomLeaves,
        ∀ C ∈ leaf, ∃ L : Literal, C = Clause.single L := by
  induction T with
  | axiom_ =>
      simp [axiomsAllSingleLiteral, axiomLeaves]
  | rule _ _ _ _ left right ihLeft ihRight =>
      simp only [axiomsAllSingleLiteral, axiomLeaves, List.mem_append]
      rw [ihLeft, ihRight]
      constructor
      · rintro ⟨hLeft, hRight⟩ leaf (hLeaf | hLeaf)
        · exact hLeft leaf hLeaf
        · exact hRight leaf hLeaf
      · intro h
        constructor
        · intro leaf hLeaf
          exact h leaf (Or.inl hLeaf)
        · intro leaf hLeaf
          exact h leaf (Or.inr hLeaf)

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

/-- Regression for proof-node occurrence identity: even when the same proof
value is reused as both premises, its left and right occurrences have distinct
paths.  Choosing `A = {B}` makes the premise indices exactly equal. -/
theorem duplicateEqualSubproofOccurrences_distinct
    (pre post : List Clause) (B : Literal)
    (sub :
      OccurrenceGCNFProof
        (pre ++ Clause.single B :: post)) :
    let root :
        OccurrenceGCNFProof
          (pre ++
            clauseWithLiteral (Clause.single B) B :: post) :=
      .rule pre post (Clause.single B) B sub sub
    let left : NodeOccurrence root
        (pre ++ Clause.single B :: post) :=
      ⟨sub,
        .leftPremise pre post (Clause.single B) B
          sub sub (.root sub)⟩
    let right : NodeOccurrence root
        (pre ++ Clause.single B :: post) :=
      ⟨sub,
        .rightPremise pre post (Clause.single B) B
          sub sub (.root sub)⟩
    left ≠ right := by
  dsimp only
  intro h
  cases h

end OccurrenceGCNFProof
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- Evidence that `C` is a particular occurrence in `clauses`, represented by
the prefix and suffix around that occurrence.  This carries the positional
information needed by later permutation arguments without choosing a default
clause when the list is empty. -/
@[blueprint "chap9__lemma_9_2_2"]
structure RootOccurrence (clauses : List Clause) (C : Clause) where
  pre : List Clause
  post : List Clause
  split : clauses = pre ++ C :: post

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
namespace RootOccurrence

/-- A represented root occurrence is a member of its root list. -/
theorem mem {clauses : List Clause} {C : Clause}
    (occ : RootOccurrence clauses C) :
    C ∈ clauses := by
  rw [occ.split]
  exact List.mem_append_right occ.pre (List.mem_cons_self)

/-- List membership constructively yields an exact root occurrence. -/
theorem of_mem {clauses : List Clause} {C : Clause}
    (hC : C ∈ clauses) :
    Nonempty (RootOccurrence clauses C) := by
  induction clauses with
  | nil =>
      simp at hC
  | cons D rest ih =>
      rcases List.mem_cons.mp hC with hDC | hRest
      · subst D
        exact ⟨⟨[], rest, by simp⟩⟩
      · rcases ih hRest with ⟨occ⟩
        exact
          ⟨⟨D :: occ.pre, occ.post, by
            calc
              D :: rest =
                  D :: (occ.pre ++ C :: occ.post) :=
                congrArg (D :: ·) occ.split
              _ = (D :: occ.pre) ++ C :: occ.post := rfl⟩⟩

/-- Exact root occurrences exist precisely for list members. -/
theorem nonempty_iff_mem {clauses : List Clause} {C : Clause} :
    Nonempty (RootOccurrence clauses C) ↔ C ∈ clauses := by
  constructor
  · rintro ⟨occ⟩
    exact occ.mem
  · exact of_mem

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
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
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

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
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

/-- Regression for duplicate clause values: the first and second positions do
not collapse even when both contain the same clause. -/
theorem duplicateEqualClauseOccurrences_distinct
    (ctx : TwoOccurrenceContext) (C : Clause) :
    ctx.firstOccurrence C C ≠
      ctx.secondOccurrence C C := by
  intro h
  have hPre := congrArg RootOccurrence.pre h
  have hLength := congrArg List.length hPre
  simp only [firstOccurrence, secondOccurrence,
    List.length_append, List.length_cons] at hLength
  omega

end TwoOccurrenceContext
end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

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

end LCS.SLD.SLDForm.Occurrence
end

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF
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


attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.ruleAt

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.fill

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.firstThenSecond

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.secondThenFirst

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.axiomLeaves

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.depth

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation.rooted

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation.tree

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootRuleAt.left

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.RootOccurrence.replace

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootRuleAt

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.OccurrenceGCNFProof.RootPermutation

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.firstOccurrence

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.TwoOccurrenceContext.secondOccurrence

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.splitFirst

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Occurrence.UnaryRuleSquare.splitSecond
