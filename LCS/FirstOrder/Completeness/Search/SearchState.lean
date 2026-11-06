import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.TermEnumerations
import Attach
import LCS.FirstOrder.Completeness.Search.SearchState.ProofsStamp

/-! # The search state of Definition 5.5.1 (Section 5.5.2)

Branch records, possibly infinite deduction trees and search trees, the search
state with its input tails, the round-end update of TERM₀ and the AVAILᵢ lists,
and finished leaves.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen

/-- Definition 5.5.1: Each branch records its own principal formulae used
with the globally indexed TERM₀ and TERM₁ entries. -/
@[blueprint "chap5__definition_5_5_1"]
structure BranchRecords (L : Language) where
  FORM0 : Nat → List (FormulaN L)
  FORM1 : Nat → List (FormulaN L)

/-- Definition 5.5.1: The initial root has empty formula records. -/
@[blueprint "chap5__definition_5_5_1"]
def BranchRecords.empty (L : Language) : BranchRecords L :=
  ⟨fun _ => [], fun _ => []⟩

/-- Definition 5.5.1: A newly appended TERM₁ entry has an empty FORM₁
record on each branch; other records remain unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
def BranchRecords.clearFORM1 {L : Language} (r : BranchRecords L) (k : Nat) :
    BranchRecords L :=
  { r with FORM1 := fun j => if j = k then [] else r.FORM1 j }

/-- Definition 5.5.1: Append the current input heads to a finite sequent;
an exhausted side contributes no formula. -/
@[blueprint "chap5__definition_5_5_1"]
def extendSeq {L : Language} (s : Sequent L)
    (newAnt newSuc : Option (FormulaN L)) : Sequent L :=
  Sequent.mk (s.antecedent ++ newAnt.toList) (s.succedent ++ newSuc.toList)

/-- Definition 5.5.1: A finite stage of first-order infinite search, with
G-rule edges and explicit input-introduction edges. -/
@[blueprint "chap5__definition_5_5_1"]
inductive InfGDeductionTreeExt {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) : InfGDeductionTreeExt s
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      (sub : InfGDeductionTreeExt prem) : InfGDeductionTreeExt conc
  | twoPremise {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (left : InfGDeductionTreeExt p1) (right : InfGDeductionTreeExt p2) :
      InfGDeductionTreeExt conc
  | extend {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (sub : InfGDeductionTreeExt (extendSeq s newAnt newSuc)) : InfGDeductionTreeExt s

/-- Definition 5.5.1: The root sequent of a search-stage deduction tree. -/
@[blueprint "chap5__definition_5_5_1"]
def InfGDeductionTreeExt.conclusion {L : Language} {s : Sequent L}
    (_ : InfGDeductionTreeExt s) : Sequent L := s

/-- Definition 5.5.1: Leaf labels in lexicographic tree-address order. -/
@[blueprint "chap5__definition_5_5_1"]
def InfGDeductionTreeExt.leaves {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → List (Sequent L)
  | _, .leaf s => [s]
  | _, .onePremise _ sub => sub.leaves
  | _, .twoPremise _ left right => left.leaves ++ right.leaves
  | _, .extend _ _ sub => sub.leaves

/-- Definition 5.5.1: Search trees carry independent formula records at
leaves, actual G-rule witnesses, and explicit input-introduction edges. The conclusion is
an index, so every extension preserves the root sequent. -/
@[blueprint "chap5__definition_5_5_1"]
inductive SearchTree {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) (records : BranchRecords L) : SearchTree s
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      (sub : SearchTree prem) : SearchTree conc
  | twoPremise {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (left : SearchTree p1) (right : SearchTree p2) : SearchTree conc
  | extend {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (sub : SearchTree (extendSeq s newAnt newSuc)) : SearchTree s

/-- Definition 5.5.1: Forget branch records while preserving every G-rule
and input-introduction edge. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.forget {L : Language} : {s : Sequent L} → SearchTree s → InfGDeductionTreeExt s
  | _, .leaf s _ => .leaf s
  | _, .onePremise rule sub => .onePremise rule sub.forget
  | _, .twoPremise rule left right => .twoPremise rule left.forget right.forget
  | _, .extend a b sub => .extend a b sub.forget

/-- Definition 5.5.1: Initialize the newly appended TERM₁ record on every
branch of the tree, leaving its deductions and FORM₀ records unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.clearFORM1 {L : Language} (k : Nat) : {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s r => .leaf s (r.clearFORM1 k)
  | _, .onePremise rule sub => .onePremise rule (sub.clearFORM1 k)
  | _, .twoPremise rule left right =>
    .twoPremise rule (left.clearFORM1 k) (right.clearFORM1 k)
  | _, .extend a b sub => .extend a b (sub.clearFORM1 k)

/-- Definition 5.5.1: Global term lists, availability streams and activation
counter, together with the remaining input and the tree's branch-local records.
TERM₀ is the round snapshot; TERM₁ is its in-progress update. -/
@[blueprint "chap5__definition_5_5_1"]
structure SearchState (L : Language) (root : Sequent L) where
  TERM0 : List (Term L)
  TERM1 : List (Term L)
  avail : Nat → TermStream L
  numact : Nat
  /-- L and R are the antecedent and succedent streams of the remaining input. -/
  remaining : InfSequentN L
  tree : SearchTree root

/-- Definition 5.5.1: Take the tails of both input streams, preserving
absence of holes. -/
@[blueprint "chap5__definition_5_5_1"]
def inputTail {L : Language} (q : InfSequentN L) : InfSequentN L :=
  { antecedent := fun n => q.antecedent (n + 1)
    succedent := fun n => q.succedent (n + 1)
    antecedent_noHoles := fun n => q.antecedent_noHoles (n + 1)
    succedent_noHoles := fun n => q.succedent_noHoles (n + 1) }

/-- Definition 5.5.1: Initially the tree consists of the input heads;
L and R are their tails, and the term bookkeeping comes from the admissible
enumerations with empty formula records at the unique root. The input uses
the x-variables and satisfies the set-wide free/bound convention. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchState.init {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  let initial := initialTermState hL q hq terms avail
  { TERM0 := initial.term0.map Prod.fst
    TERM1 := initial.term0.map Prod.fst
    avail := initial.avail
    numact := 0
    remaining := inputTail q
    tree := .leaf _ (BranchRecords.empty L) }

/-- Definition 5.5.1: Commit this branch's FORM₁ records for the existing
TERM₁ positions to FORM₀; appended availability heads have empty FORM₀ records. -/
@[blueprint "chap5__definition_5_5_1"]
def BranchRecords.commitRound {L : Language} (records : BranchRecords L)
    (term1Length : Nat) : BranchRecords L :=
  { records with FORM0 := fun k => if k < term1Length then records.FORM1 k else [] }

/-- Definition 5.5.1: Commit the formula records separately on every branch. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.commitRound {L : Language} (term1Length : Nat) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => .leaf s (records.commitRound term1Length)
  | _, .onePremise rule sub => .onePremise rule (sub.commitRound term1Length)
  | _, .twoPremise rule left right =>
      .twoPremise rule (left.commitRound term1Length) (right.commitRound term1Length)
  | _, .extend a b sub => .extend a b (sub.commitRound term1Length)

/-- Definition 5.5.1: Commit TERM₁ and its branch records to TERM₀, then
append the nonempty heads of AVAIL₀ through AVAIL_NUMACT in order, with empty
records. Tail only those streams; streams above NUMACT remain unchanged.
Input-pointer advancement is performed by the enclosing round driver. -/
@[blueprint "chap5__definition_5_5_1"]
def roundEndUpdate {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with
    TERM0 := st.TERM1 ++ (List.range (st.numact + 1)).filterMap (fun i => (st.avail i).head)
    avail := fun i => if i ≤ st.numact then (st.avail i).tail else st.avail i
    tree := st.tree.commitRound st.TERM1.length }

/-- Definition 5.5.1: A leaf is finished if it is an axiom, or both remaining
input streams are exhausted and every non-atomic antecedent formula is universal
and every non-atomic succedent formula is existential. Each such principal
formula must occur in this branch's FORM₀ record at every TERM₀ position.
The no-holes stream invariant makes an empty head equivalent to exhaustion. -/
@[blueprint "chap5__definition_5_5_1"]
def isFinishedLeaf {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (st : SearchState L root)
    (s : Sequent L) (records : BranchRecords L) : Prop :=
  isAxiom s ∨
    (st.remaining.antecedent 0 = none ∧ st.remaining.succedent 0 = none ∧
      (∀ A ∈ s.antecedent,
        A.isAtomic ∨
          ((∃ x B, A = FormulaN.all x B) ∧
            ∀ k, k < st.TERM0.length → A ∈ records.FORM0 k)) ∧
      (∀ A ∈ s.succedent,
        A.isAtomic ∨
          ((∃ x B, A = FormulaN.ex x B) ∧
            ∀ k, k < st.TERM0.length → A ∈ records.FORM0 k)))

end LCS.FirstOrder.Completeness.Search
end
