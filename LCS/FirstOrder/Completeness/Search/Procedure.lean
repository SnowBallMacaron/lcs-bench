import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.GrowLeftRight
import Attach
import LCS.FirstOrder.Completeness.Search.Procedure.ProofsStamp

/-! # Procedures expand and search of Definition 5.5.1

Intake of the next input formulae, expansion of the unfinished leaves, the search
rounds, and the output of procedure search.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen

/-- Definition 5.5.1: Carry the global term lists, availability streams and
input pointers into a local tree, or back into the enclosing tree. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchState.withTree {L : Language} {root s : Sequent L}
    (st : SearchState L root) (tree : SearchTree s) : SearchState L s :=
  { TERM0 := st.TERM0, TERM1 := st.TERM1, avail := st.avail,
    numact := st.numact, remaining := st.remaining, tree := tree }

/-- Definition 5.5.1: Add the single u₁ child at every leaf of the local
tree after its grow steps, retaining records and the input-introduction edge even
when both streams are exhausted (the resulting labels then coincide). -/
@[blueprint "chap5__definition_5_5_1"]
def intake {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  let a := st.remaining.antecedent 0
  let b := st.remaining.succedent 0
  { st with tree := st.tree.extendLeaves fun s r =>
      .extend a b (.leaf (extendSeq s a b) r) }

/-- Definition 5.5.1: Expand an unfinished leaf. Grow the original antecedent
formulae in order, then the original succedent formulae in order, and finally
create the u₁ child at each resulting leaf. All leaves in a round read the same
input heads; this operation does not advance the input pointers. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def expandLeaf {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (st : SearchState L root) (s : Sequent L)
    (records : BranchRecords L) : SearchState L s := by
  classical
  let localState := st.withTree (.leaf s records)
  exact if isFinishedLeaf hL st s records then localState else
    let leftGrown := s.antecedent.foldl (fun acc A => growLeft hL A acc) localState
    let bothGrown := s.succedent.foldl (fun acc A => growRight hL A acc) leftGrown
    intake bothGrown

/-- Definition 5.5.1: Substitute the expanded local tree at the designated
leaf address. Child 0 is used for unary and intake edges; binary children are
0 and 1. Invalid addresses and addresses of internal nodes leave the state
unchanged. Global term and availability updates are returned to the enclosing
tree, while untouched branches keep their own records. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def expand {L : Language} (hL : L.withoutEquality) :
    {root : Sequent L} → List Nat → SearchState L root → SearchState L root
  | _, [], st =>
    match st.tree with
    | .leaf s records => expandLeaf hL st s records
    | _ => st
  | _, 0 :: path, st =>
    match st.tree with
    | .leaf _ _ => st
    | .onePremise rule sub =>
      let result := expand hL path (st.withTree sub)
      result.withTree (.onePremise rule result.tree)
    | .twoPremise rule left right =>
      let result := expand hL path (st.withTree left)
      result.withTree (.twoPremise rule result.tree right)
    | .extend a b sub =>
      let result := expand hL path (st.withTree sub)
      result.withTree (.extend a b result.tree)
  | _, 1 :: path, st =>
    match st.tree with
    | .twoPremise rule left right =>
      let result := expand hL path (st.withTree right)
      result.withTree (.twoPremise rule left result.tree)
    | _ => st
  | _, _ :: _, st => st

/-- Definition 5.5.1: Advance L and R once, after all original leaves of the
round have been expanded. The no-holes invariants are preserved by taking tails. -/
@[blueprint "chap5__definition_5_5_1"]
def advanceInput {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with remaining := inputTail st.remaining }

/-- Definition 5.5.1: The admissible TERMS and AVAIL enumerations fixed
for a run of the search procedure. -/
@[blueprint "chap5__definition_5_5_1"]
structure SearchEnumeration {L : Language} (q : InfSequentN L) where
  terms : TermsEnum q
  avail : ∀ i, 0 < i → AvailEnum q i

/-- Definition 5.5.1: Leaf addresses in lexicographic order. Unary rule
and intake edges use child 0; binary rule edges use children 0 and 1. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.leafAddresses {L : Language} : {s : Sequent L} → SearchTree s → List (List Nat)
  | _, .leaf _ _ => [[]]
  | _, .onePremise _ sub => sub.leafAddresses.map (0 :: ·)
  | _, .twoPremise _ left right =>
      left.leafAddresses.map (0 :: ·) ++ right.leafAddresses.map (1 :: ·)
  | _, .extend _ _ sub => sub.leafAddresses.map (0 :: ·)

/-- Definition 5.5.1: All leaf labels paired with their own formula records. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.leaves {L : Language} :
    {s : Sequent L} → SearchTree s → List (Sequent L × BranchRecords L)
  | _, .leaf s records => [(s, records)]
  | _, .onePremise _ sub => sub.leaves
  | _, .twoPremise _ left right => left.leaves ++ right.leaves
  | _, .extend _ _ sub => sub.leaves

/-- Definition 5.5.1: The stopping condition uses each leaf's own FORM₀
records and the current global TERM₀ and input streams. -/
@[blueprint "chap5__definition_5_5_1"]
def allFinished {L : Language} (hL : L.withoutEquality) {root : Sequent L}
    (st : SearchState L root) : Prop :=
  ∀ leaf ∈ st.tree.leaves, isFinishedLeaf hL st leaf.1 leaf.2

/-- Definition 5.5.1: Copy FORM₀ into FORM₁ independently on every branch
at the start of a round, preserving all rule and intake edges. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.startRound {L : Language} : {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => .leaf s { records with FORM1 := records.FORM0 }
  | _, .onePremise rule sub => .onePremise rule sub.startRound
  | _, .twoPremise rule left right => .twoPremise rule left.startRound right.startRound
  | _, .extend a b sub => .extend a b sub.startRound

/-- Definition 5.5.1: Start a round by copying TERM₀ and its branch records
to the working TERM₁ and FORM₁ lists. -/
@[blueprint "chap5__definition_5_5_1"]
def startRound {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with TERM1 := st.TERM0, tree := st.tree.startRound }

/-- Definition 5.5.1: One round expands the original leaves in lexicographic
address order, then commits TERM₁, advances L/R once, and transfers active
AVAIL heads. A state whose leaves are all finished is left unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def searchRound {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (st : SearchState L root) : SearchState L root := by
  classical
  exact if allFinished hL st then st else
    let expanded := st.tree.leafAddresses.foldl (fun acc path => expand hL path acc) (startRound st)
    roundEndUpdate (advanceInput expanded)

/-- Definition 5.5.1: The round-k approximant of the search procedure for
an input built from the x-variables and satisfying the free/bound convention,
with fixed admissible TERMS and AVAIL enumerations. The returned state contains
the tree with all rule and intake edges and its branch-local records. -/
@[blueprint "chap5__definition_5_5_1" (main := true)]
noncomputable def search51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  match k with
  | 0 => SearchState.init hL q hq hFB enum.terms enum.avail
  | k + 1 => searchRound hL (search51 hL q hq hFB enum k)

/-- Definition 5.5.1: Search halts for its fixed admissible enumerations
when some finite-round approximant has every leaf finished. -/
@[blueprint "chap5__definition_5_5_1"]
def halts51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) : Prop :=
  ∃ k, allFinished hL (search51 hL q hq hFB enum k)

/-- Definition 5.5.1: The terminal messages, "T is a proof of Γ₀ → Δ₀"
and "Γ₀ → Δ₀ is falsifiable". A deduction tree all of whose leaves are
axioms is a proof (Definition 5.4.2). -/
@[blueprint "chap5__definition_5_5_1"]
inductive SearchOutput {L : Language} (root : Sequent L) : Type where
  | proof (T : InfGDeductionTreeExt root)
      (hClosed : ∀ leaf ∈ T.leaves, isAxiom leaf)
  | falsifiable

/-- Definition 5.5.1: While not all leaves are finished, there is no output.
After the loop, if all leaves are closed, write "T is a proof of Γ₀ → Δ₀";
otherwise, write "Γ₀ → Δ₀ is falsifiable". -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def output51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat) :
    Option (SearchOutput (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList)) := by
  classical
  let st := search51 hL q hq hFB enum k
  exact if allFinished hL st then
    if hClosed : ∀ leaf ∈ st.tree.forget.leaves, isAxiom leaf then
      some (.proof st.tree.forget hClosed)
    else some .falsifiable
  else none

end LCS.FirstOrder.Completeness.Search
end
