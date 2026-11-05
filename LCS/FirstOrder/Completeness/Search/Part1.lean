import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import Attach
import LCS.FirstOrder.Completeness.Search.Part1.ProofsStamp

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables

/-- Definition 5.5.1 (variable convention): The i-th input variable xᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def xVar {L : Language} (i : Nat) : Term L := .var (2 * i)

/-- Definition 5.5.1 (variable convention): The i-th reserved variable yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def yVar {L : Language} (i : Nat) : Term L := .var (2 * i + 1)

/-- Definition 5.5.1 (variable convention): An x-variable has an even index. -/
@[blueprint "chap5__definition_5_5_1"]
def isXIndex (n : Nat) : Prop := n % 2 = 0











-- retained: used by LCS.FirstOrder.Completeness.Search.Part2
/-- Every variable in an even-renamed term has an x index. -/
theorem evenTerm_isXIndex {L : Language} (t : Term L) :
    ∀ n, n ∈ termFV (InfiniteSearch.evenTerm t) → isXIndex n := by
  induction t with
  | var i =>
    intro n hn
    have heq : n = 2 * i := hn
    subst n
    simp [isXIndex]
  | const c => intro n hn; exact False.elim hn
  | func f ts ih =>
    intro n hn
    obtain ⟨i, hi⟩ := hn
    exact ih i n hi

end LCS.FirstOrder.Completeness.Search
end

section
namespace LCS.FirstOrder.SyntaxN.FormulaN
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.5.1 (variable convention): Every variable occurring in a
formula, free or bound, is an x variable; this includes vacuous binders. -/
@[blueprint "chap5__definition_5_5_1"]
def builtFromX {L : Language} (A : FormulaN L) : Prop :=
  ∀ n, n ∈ formulaFVN A ∨ n ∈ formulaBVN A → isXIndex n

-- retained: used by LCS.FirstOrder.Completeness.Search.Part2
/-- Even-index renaming produces a formula built entirely from x variables. -/
theorem builtFromX_evenFormula {L : Language} (A : FormulaN L) :
    (InfiniteSearch.evenFormula A).builtFromX := by
  induction A with
  | predN P ts =>
    intro n hn
    rcases hn with ⟨i, hi⟩ | hfalse
    · exact evenTerm_isXIndex (ts i) n hi
    · exact False.elim hfalse
  | eq_ h t u =>
    intro n hn
    rcases hn with (ht | hu) | hfalse
    · exact evenTerm_isXIndex t n ht
    · exact evenTerm_isXIndex u n hu
    · exact False.elim hfalse
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    intro n hn
    rcases hn with (ha | hb) | (ha | hb)
    · exact ihA n (Or.inl ha)
    · exact ihB n (Or.inl hb)
    · exact ihA n (Or.inr ha)
    · exact ihB n (Or.inr hb)
  | all x A ih | ex x A ih =>
    intro n hn
    rcases hn with ⟨ha, _⟩ | (ha | hx)
    · exact ih n (Or.inl ha)
    · exact ih n (Or.inr ha)
    · have heq : n = 2 * x := hx
      subst n
      simp [isXIndex]



end LCS.FirstOrder.SyntaxN.FormulaN
end

section
namespace LCS.FirstOrder.Gentzen.InfSequentN
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN

/-- Definition 5.5.1 (input convention): Every formula on either side of
a possibly infinite input sequent is built entirely from x variables. -/
@[blueprint "chap5__definition_5_5_1"]
def builtFromX {L : Language} (q : InfSequentN L) : Prop :=
  ∀ A, q.memAntecedent A ∨ q.memSuccedent A → A.builtFromX

end LCS.FirstOrder.Gentzen.InfSequentN
end

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae

/-- Definition 5.5.1: The signed formulae of the possibly infinite input. -/
@[blueprint "chap5__definition_5_5_1"]
def inputSignedSet {L : Language} (q : InfSequentN L) : Set (SignedFormula L)
  | .trueF A => q.memAntecedent A
  | .falseF A => q.memSuccedent A

/-- Definition 5.5.1: L′ contains exactly the symbols occurring in the input,
with their original ranks. -/
@[blueprint "chap5__definition_5_5_1"]
def inputLanguage {L : Language} (q : InfSequentN L) : Language :=
  reductLanguage L (inputSignedSet q)

/-- Definition 5.5.1: The input supplies a free variable or a constant as a
term generator. -/
@[blueprint "chap5__definition_5_5_1"]
def hasInputGenerators {L : Language} (q : InfSequentN L) : Prop :=
  (∃ x, x ∈ signedSetFreeVars (inputSignedSet q)) ∨
    ∃ c, c ∈ signedSetConstSyms (inputSignedSet q)

/-- Definition 5.5.1: Initial variable generators are the input's free
variables, with y₀ supplied exactly when there are no input generators. -/
@[blueprint "chap5__definition_5_5_1"]
def initialVar {L : Language} (q : InfSequentN L) (x : Nat) : Prop :=
  x ∈ signedSetFreeVars (inputSignedSet q) ∨ (¬ hasInputGenerators q ∧ x = 1)

/-- Definition 5.5.1: A term uses the function and constant symbols of L′. -/
@[blueprint "chap5__definition_5_5_1"]
def termOverInput {L : Language} (q : InfSequentN L) (t : Term L) : Prop :=
  termFunSyms t ⊆ signedSetFunSyms (inputSignedSet q) ∧
    termConstSyms t ⊆ signedSetConstSyms (inputSignedSet q)

/-- Definition 5.5.1: TERMS consists exactly of L′-terms over the input
free variables and constants, or over y₀ and the function symbols when
there are no input generators. -/
@[blueprint "chap5__definition_5_5_1"]
def termsTerm {L : Language} (q : InfSequentN L) (t : Term L) : Prop :=
  termOverInput q t ∧ ∀ x, x ∈ termFV t → initialVar q x

/-- Definition 5.5.1: AVAILᵢ variables are the initial generators together
with y₁, …, yᵢ; y₀ is included precisely in the fallback case. -/
@[blueprint "chap5__definition_5_5_1"]
def availVar {L : Language} (q : InfSequentN L) (i x : Nat) : Prop :=
  initialVar q x ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ x = 2 * j + 1

/-- Definition 5.5.1: AVAILᵢ contains exactly the L′-terms over its
allowed generators that actually contain yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def availTerm {L : Language} (q : InfSequentN L) (i : Nat) (t : Term L) : Prop :=
  termOverInput q t ∧ (∀ x, x ∈ termFV t → availVar q i x) ∧
    2 * i + 1 ∈ termFV t

/-- Definition 5.5.1: A finite or infinite term stream has no holes and
lists each present term at most once; trailing empty markers may repeat. -/
@[blueprint "chap5__definition_5_5_1"]
structure TermStream (L : Language) where
  entries : Nat → Option (Term L)
  noHoles : ∀ n, entries n = none → entries (n + 1) = none
  some_injective : ∀ n m t, entries n = some t → entries m = some t → n = m


/-- Definition 5.5.1: The head of an exhausted term stream is absent. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.head {L : Language} (s : TermStream L) : Option (Term L) := s.entries 0

/-- Definition 5.5.1: Removing the head preserves no holes and uniqueness. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.tail {L : Language} (s : TermStream L) : TermStream L where
  entries := fun n => s.entries (n + 1)
  noHoles := fun n => s.noHoles (n + 1)
  some_injective := by
    intro n m t hn hm
    have h := s.some_injective (n + 1) (m + 1) t hn hm
    omega

/-- Definition 5.5.1: An exhausted stream contributes no terms. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.empty (L : Language) : TermStream L where
  entries := fun _ => none
  noHoles := fun _ _ => rfl
  some_injective := by intro n m t h; cases h

/-- Definition 5.5.1: An admissible TERMS enumeration lists exactly the
initial term set; in the fallback case its first term is y₀. -/
@[blueprint "chap5__definition_5_5_1"]
structure TermsEnum {L : Language} (q : InfSequentN L) extends TermStream L where
  enumerates : ∀ t, (∃ n, entries n = some t) ↔ termsTerm q t
  fallback_head : ¬ hasInputGenerators q → entries 0 = some (yVar 0)

/-- Definition 5.5.1: An admissible AVAILᵢ enumeration, for i ≥ 1,
lists exactly the terms containing yᵢ over the prescribed generators,
and starts with yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
structure AvailEnum {L : Language} (q : InfSequentN L) (i : Nat)
    extends TermStream L where
  index_pos : 0 < i
  enumerates : ∀ t, (∃ n, entries n = some t) ↔ availTerm q i t
  starts_with : entries 0 = some (yVar i)

/-- Definition 5.5.1: The initial root has an empty formula record for
the head term; an absent head contributes no record. -/
@[blueprint "chap5__definition_5_5_1"]
def initialTermRecords {L : Language} (s : TermStream L) :
    List (Term L × List (FormulaN L)) :=
  match s.head with
  | none => []
  | some t => [(t, [])]

/-- Definition 5.5.1: Term bookkeeping at the unique initial root.
The formula lists are that root's records; AVAIL and NUMACT are global. -/
@[blueprint "chap5__definition_5_5_1"]
structure InitialTermState (L : Language) where
  term0 : List (Term L × List (FormulaN L))
  avail : Nat → TermStream L
  numact : Nat

/-- Definition 5.5.1: Initialize the root's TERM₀ from head(TERMS),
AVAIL₀ from tail(TERMS), each positive AVAILᵢ from its admissible
enumeration, and NUMACT to zero. -/
@[blueprint "chap5__definition_5_5_1"]
def initialTermState {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i) : InitialTermState L where
  term0 := initialTermRecords terms.toTermStream
  avail := fun i => match i with
    | 0 => terms.toTermStream.tail
    | j + 1 => (avail (j + 1) (by omega)).toTermStream
  numact := 0









end LCS.FirstOrder.Completeness.Search
end

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

/-- Definition 5.5.1: The two quantifier rules that activate a new variable. -/
@[blueprint "chap5__definition_5_5_1"]
inductive EigenRuleKind where
  | exLeft
  | allRight

/-- Definition 5.5.1: Extend an eligible nonaxiom leaf by the selected
quantifier rule using y. The flag is true exactly when a rule node is
constructed; membership, freshness and free-for side conditions are checked. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def activateAtLeaf {L : Language} (hL : L.withoutEquality)
    (kind : EigenRuleKind) (x : Nat) (A : FormulaN L) (y : Nat)
    (s : Sequent L) (records : BranchRecords L) : SearchTree s × Bool := by
  classical
  by_cases hax : isAxiom s
  · exact (.leaf s records, false)
  by_cases hfresh : ∀ F ∈ s.antecedent ++ s.succedent, y ∉ formulaFVN F
  · by_cases hfree : isFreeForN (.var y) x A
    · cases kind with
      | exLeft =>
        by_cases hA : FormulaN.ex x A ∈ s.antecedent
        · let split := Gentzen.Search.NoFunction.splitListAt s.antecedent (.ex x A) hA
          let Γ := split.val.1
          let Δ := split.val.2
          let conc := Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) s.succedent
          let prem := Sequent.mk (Γ ++ [formulaSubstN A (.var y) x] ++ Δ) s.succedent
          have hconc : conc = s := by
            cases s
            exact congrArg (fun ant => Sequent.mk ant _) split.property.symm
          have hfresh' : ∀ F ∈ conc.antecedent ++ conc.succedent, y ∉ formulaFVN F :=
            hconc.symm ▸ hfresh
          let tree : SearchTree conc := .onePremise
            (.exLeft y Γ Δ s.succedent x A hfresh' hfree) (.leaf prem records)
          exact (hconc ▸ tree, true)
        · exact (.leaf s records, false)
      | allRight =>
        by_cases hA : FormulaN.all x A ∈ s.succedent
        · let split := Gentzen.Search.NoFunction.splitListAt s.succedent (.all x A) hA
          let Δ := split.val.1
          let Λ := split.val.2
          let conc := Sequent.mk s.antecedent (Δ ++ [FormulaN.all x A] ++ Λ)
          let prem := Sequent.mk s.antecedent (Δ ++ [formulaSubstN A (.var y) x] ++ Λ)
          have hconc : conc = s := by
            cases s
            exact congrArg (fun succ => Sequent.mk _ succ) split.property.symm
          have hfresh' : ∀ F ∈ conc.antecedent ++ conc.succedent, y ∉ formulaFVN F :=
            hconc.symm ▸ hfresh
          let tree : SearchTree conc := .onePremise
            (.allRight y s.antecedent Δ Λ x A hfresh' hfree) (.leaf prem records)
          exact (hconc ▸ tree, true)
        · exact (.leaf s records, false)
    · exact (.leaf s records, false)
  · exact (.leaf s records, false)

/-- Definition 5.5.1: Apply the selected eigenvariable rule once at every
eligible current leaf, using the same variable throughout this traversal. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def activateTree {L : Language} (hL : L.withoutEquality)
    (kind : EigenRuleKind) (x : Nat) (A : FormulaN L) (y : Nat) :
    {s : Sequent L} → SearchTree s → SearchTree s × Bool
  | _, .leaf s records => activateAtLeaf hL kind x A y s records
  | _, .onePremise rule sub =>
    let result := activateTree hL kind x A y sub
    (.onePremise rule result.1, result.2)
  | _, .twoPremise rule left right =>
    let l := activateTree hL kind x A y left
    let r := activateTree hL kind x A y right
    (.twoPremise rule l.1 r.1, l.2 || r.2)
  | _, .extend a b sub =>
    let result := activateTree hL kind x A y sub
    (.extend a b result.1, result.2)

/-- Definition 5.5.1: Consume head(AVAIL_{NUMACT+1}) only when an actual
quantifier-rule application occurs. Append its variable to TERM₁ with an
empty FORM₁ record on each branch, tail only that availability stream, and
increment NUMACT once. TERM₀ and the input pointers remain unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def activateVariable {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (kind : EigenRuleKind) (x : Nat) (A : FormulaN L)
    (st : SearchState L root) : SearchState L root :=
  match (st.avail (st.numact + 1)).head with
  | some (.var y) =>
    let result := activateTree hL kind x A y st.tree
    if result.2 then
      { st with
        TERM1 := st.TERM1 ++ [.var y]
        avail := fun i => if i = st.numact + 1 then (st.avail i).tail else st.avail i
        numact := st.numact + 1
        tree := result.1.clearFORM1 st.TERM1.length }
    else st
  | _ => st

/-- Definition 5.5.1: The ∃:left grow case activates the next available variable. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growLeftEx {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root := activateVariable hL .exLeft x A st

/-- Definition 5.5.1: The ∀:right grow case activates the next available variable. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growRightAll {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root := activateVariable hL .allRight x A st

-- retained: used by LCS.FirstOrder.Equality.Search.Part1
/-- An exhausted next stream cannot activate a variable. -/
theorem activateVariable_of_empty {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (kind : EigenRuleKind) (x : Nat) (A : FormulaN L)
    (st : SearchState L root) (h : (st.avail (st.numact + 1)).head = none) :
    activateVariable hL kind x A st = st := by
  simp [activateVariable, h]

-- retained: used by LCS.FirstOrder.Equality.Search.Part1
/-- If no leaf admits the rule, all global and branch bookkeeping is unchanged. -/
theorem activateVariable_of_no_application {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (kind : EigenRuleKind) (x : Nat) (A : FormulaN L)
    (st : SearchState L root) (y : Nat)
    (hhead : (st.avail (st.numact + 1)).head = some (.var y))
    (hstep : (activateTree hL kind x A y st.tree).2 = false) :
    activateVariable hL kind x A st = st := by
  simp [activateVariable, hhead, hstep]

/-- Definition 5.5.1: Select the TERM₀ positions whose branch-local FORM₀
record does not contain the principal formula, preserving the term order. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def pendingTerms {L : Language} (terms : List (Term L))
    (records : BranchRecords L) (principal : FormulaN L) : List (Term L × Nat) := by
  classical
  exact (terms.mapIdx fun k t => (t, k)).filter fun p => principal ∉ records.FORM0 p.2

/-- Definition 5.5.1: Record the principal formula in FORM₁ at precisely
the positions used in an extended inference on this branch. -/
@[blueprint "chap5__definition_5_5_1"]
def BranchRecords.recordInstances {L : Language} (records : BranchRecords L)
    (positions : List Nat) (principal : FormulaN L) : BranchRecords L :=
  { records with FORM1 := fun k =>
      if k ∈ positions then records.FORM1 k ++ [principal] else records.FORM1 k }

/-- Definition 5.5.1: The two rules using all unused TERM₀ terms in one inference. -/
@[blueprint "chap5__definition_5_5_1"]
inductive InstanceRuleKind where
  | allLeft
  | exRight

/-- Definition 5.5.1: The principal formula tested in the branch records. -/
@[blueprint "chap5__definition_5_5_1"]
def InstanceRuleKind.principal {L : Language} (kind : InstanceRuleKind)
    (x : Nat) (A : FormulaN L) : FormulaN L :=
  match kind with
  | .allLeft => .all x A
  | .exRight => .ex x A

/-- Definition 5.5.1: At a nonaxiom leaf, use every TERM₀ entry whose FORM₀
record lacks the principal formula in one extended ∀:left or ∃:right inference.
The terms must all be free for substitution. A successful inference appends
the principal formula to the selected FORM₁ records of this branch. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def instantiateAtLeaf {L : Language} (hL : L.withoutEquality)
    (kind : InstanceRuleKind) (x : Nat) (A : FormulaN L) (terms : List (Term L))
    (s : Sequent L) (records : BranchRecords L) : SearchTree s := by
  classical
  by_cases hax : isAxiom s
  · exact .leaf s records
  let selected := pendingTerms terms records (kind.principal x A)
  let ts := selected.map Prod.fst
  by_cases hne : ts = []
  · exact .leaf s records
  by_cases hfree : ∀ t ∈ ts, isFreeForN t x A
  · let records' := records.recordInstances (selected.map Prod.snd) (kind.principal x A)
    cases kind with
    | allLeft =>
      by_cases hA : FormulaN.all x A ∈ s.antecedent
      · let split := Gentzen.Search.NoFunction.splitListAt s.antecedent (.all x A) hA
        let Γ := split.val.1
        let Δ := split.val.2
        let conc := Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) s.succedent
        let prem := Sequent.mk
          (Γ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.all x A] ++ Δ)
          s.succedent
        have hconc : conc = s := by
          cases s
          exact congrArg (fun ant => Sequent.mk ant _) split.property.symm
        let tree : SearchTree conc := .onePremise
          (.allLeft ts Γ Δ s.succedent x A hne hfree) (.leaf prem records')
        exact hconc ▸ tree
      · exact .leaf s records
    | exRight =>
      by_cases hA : FormulaN.ex x A ∈ s.succedent
      · let split := Gentzen.Search.NoFunction.splitListAt s.succedent (.ex x A) hA
        let Δ := split.val.1
        let Λ := split.val.2
        let conc := Sequent.mk s.antecedent (Δ ++ [FormulaN.ex x A] ++ Λ)
        let prem := Sequent.mk s.antecedent
          (Δ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.ex x A] ++ Λ)
        have hconc : conc = s := by
          cases s
          exact congrArg (fun succ => Sequent.mk _ succ) split.property.symm
        let tree : SearchTree conc := .onePremise
          (.exRight ts s.antecedent Δ Λ x A hne hfree) (.leaf prem records')
        exact hconc ▸ tree
      · exact .leaf s records
  · exact .leaf s records

/-- Definition 5.5.1: Traverse the current leaves using their individual
FORM₀ and FORM₁ records and the global TERM₀ snapshot. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def instantiateTree {L : Language} (hL : L.withoutEquality)
    (kind : InstanceRuleKind) (x : Nat) (A : FormulaN L) (terms : List (Term L)) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => instantiateAtLeaf hL kind x A terms s records
  | _, .onePremise rule sub => .onePremise rule (instantiateTree hL kind x A terms sub)
  | _, .twoPremise rule left right => .twoPremise rule
      (instantiateTree hL kind x A terms left) (instantiateTree hL kind x A terms right)
  | _, .extend a b sub => .extend a b (instantiateTree hL kind x A terms sub)

/-- Definition 5.5.1: The ∀:left grow case uses the extended rule with
all terms unused for this principal formula on each branch. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growLeftAll {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  { st with tree := instantiateTree hL .allLeft x A st.TERM0 st.tree }

/-- Definition 5.5.1: The ∃:right grow case uses the extended rule with
all terms unused for this principal formula on each branch. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growRightEx {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  { st with tree := instantiateTree hL .exRight x A st.TERM0 st.tree }

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

-- retained: used by LCS.FirstOrder.Equality.Search.Part1
/-- Availability streams above NUMACT are unchanged by round-end transfer. -/
theorem roundEndUpdate_avail_above {L : Language} {root : Sequent L}
    (st : SearchState L root) (i : Nat) (hi : st.numact < i) :
    (roundEndUpdate st).avail i = st.avail i := by
  simp [roundEndUpdate, Nat.not_le.mpr hi]

-- retained: used by LCS.FirstOrder.Equality.Search.Part1
/-- Each active stream is tailed exactly once at round end. -/
theorem roundEndUpdate_avail_active {L : Language} {root : Sequent L}
    (st : SearchState L root) (i : Nat) (hi : i ≤ st.numact) :
    (roundEndUpdate st).avail i = (st.avail i).tail := by
  simp [roundEndUpdate, hi]

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

/-- Definition 5.5.1: Apply the matching propositional left rule to a
nonaxiom leaf containing the principal formula on the antecedent. Each
resulting branch inherits this leaf's records. Atomic and quantified formulae
leave the leaf unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growLeftPropAtLeaf {L : Language} (hL : L.withoutEquality)
    (A : FormulaN L) (leaf : Sequent L) (records : BranchRecords L) :
    SearchTree leaf := by
  classical
  by_cases hax : isAxiom leaf
  · exact .leaf leaf records
  by_cases hA : A ∈ leaf.antecedent
  · exact
    match hAcase : A with
    | .conj B C =>
        have hAin : FormulaN.conj B C ∈ leaf.antecedent := hAcase ▸ hA
        let split := Gentzen.Search.NoFunction.splitListAt leaf.antecedent (FormulaN.conj B C) hAin
        let Γ := split.val.1
        let Δ := split.val.2
        let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.conj B C] ++ Δ) leaf.succedent
        let prem : Sequent L := Sequent.mk (Γ ++ [B, C] ++ Δ) leaf.succedent
        let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.conjLeft Γ Δ leaf.succedent B C
        let t' : SearchTree conc :=
          SearchTree.onePremise rule (SearchTree.leaf prem records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .disj B C =>
        have hAin : FormulaN.disj B C ∈ leaf.antecedent := hAcase ▸ hA
        let split := Gentzen.Search.NoFunction.splitListAt leaf.antecedent (FormulaN.disj B C) hAin
        let Γ := split.val.1
        let Δ := split.val.2
        let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.disj B C] ++ Δ) leaf.succedent
        let premL : Sequent L := Sequent.mk (Γ ++ [B] ++ Δ) leaf.succedent
        let premR : Sequent L := Sequent.mk (Γ ++ [C] ++ Δ) leaf.succedent
        let rule : GentzenStep2Ext premL premR conc :=
          GentzenStep2Ext.disjLeft Γ Δ leaf.succedent B C
        let t' : SearchTree conc :=
          SearchTree.twoPremise rule
            (SearchTree.leaf premL records) (SearchTree.leaf premR records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .impl B C =>
        have hAin : FormulaN.impl B C ∈ leaf.antecedent := hAcase ▸ hA
        let split := Gentzen.Search.NoFunction.splitListAt leaf.antecedent (FormulaN.impl B C) hAin
        let Γ := split.val.1
        let Δ := split.val.2
        let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.impl B C] ++ Δ) leaf.succedent
        let premL : Sequent L := Sequent.mk (Γ ++ Δ) ([B] ++ leaf.succedent)
        let premR : Sequent L := Sequent.mk ([C] ++ Γ ++ Δ) leaf.succedent
        let rule : GentzenStep2Ext premL premR conc :=
          GentzenStep2Ext.implLeft Γ Δ leaf.succedent B C
        let t' : SearchTree conc :=
          SearchTree.twoPremise rule
            (SearchTree.leaf premL records) (SearchTree.leaf premR records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .neg B =>
        have hAin : FormulaN.neg B ∈ leaf.antecedent := hAcase ▸ hA
        let split := Gentzen.Search.NoFunction.splitListAt leaf.antecedent (FormulaN.neg B) hAin
        let Γ := split.val.1
        let Δ := split.val.2
        let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.neg B] ++ Δ) leaf.succedent
        let prem : Sequent L := Sequent.mk (Γ ++ Δ) ([B] ++ leaf.succedent)
        let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.negLeft Γ Δ leaf.succedent B
        let t' : SearchTree conc :=
          SearchTree.onePremise rule (SearchTree.leaf prem records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .predN _ _ => SearchTree.leaf leaf records
    | .eq_ _ _ _ => SearchTree.leaf leaf records
    | .all _ _ => SearchTree.leaf leaf records
    | .ex _ _ => SearchTree.leaf leaf records
  · exact .leaf leaf records

/-- Definition 5.5.1: Apply the matching propositional right rule to a
nonaxiom leaf containing the principal formula on the succedent. Each
resulting branch inherits this leaf's records. Atomic and quantified formulae
leave the leaf unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growRightPropAtLeaf {L : Language} (hL : L.withoutEquality)
    (B : FormulaN L) (leaf : Sequent L) (records : BranchRecords L) :
    SearchTree leaf := by
  classical
  by_cases hax : isAxiom leaf
  · exact .leaf leaf records
  by_cases hB : B ∈ leaf.succedent
  · exact
    match hBcase : B with
    | .conj X Y =>
        have hBin : FormulaN.conj X Y ∈ leaf.succedent := hBcase ▸ hB
        let split := Gentzen.Search.NoFunction.splitListAt leaf.succedent (FormulaN.conj X Y) hBin
        let Δ := split.val.1
        let Λ := split.val.2
        let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.conj X Y] ++ Λ)
        let premL : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [X] ++ Λ)
        let premR : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [Y] ++ Λ)
        let rule : GentzenStep2Ext premL premR conc :=
          GentzenStep2Ext.conjRight leaf.antecedent Δ Λ X Y
        let t' : SearchTree conc :=
          SearchTree.twoPremise rule
            (SearchTree.leaf premL records) (SearchTree.leaf premR records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .disj X Y =>
        have hBin : FormulaN.disj X Y ∈ leaf.succedent := hBcase ▸ hB
        let split := Gentzen.Search.NoFunction.splitListAt leaf.succedent (FormulaN.disj X Y) hBin
        let Δ := split.val.1
        let Λ := split.val.2
        let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.disj X Y] ++ Λ)
        let prem : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [X, Y] ++ Λ)
        let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.disjRight leaf.antecedent Δ Λ X Y
        let t' : SearchTree conc :=
          SearchTree.onePremise rule (SearchTree.leaf prem records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .impl X Y =>
        have hBin : FormulaN.impl X Y ∈ leaf.succedent := hBcase ▸ hB
        let split := Gentzen.Search.NoFunction.splitListAt leaf.succedent (FormulaN.impl X Y) hBin
        let Δ := split.val.1
        let Λ := split.val.2
        let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.impl X Y] ++ Λ)
        let prem : Sequent L := Sequent.mk ([X] ++ leaf.antecedent) ([Y] ++ Δ ++ Λ)
        let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.implRight leaf.antecedent Δ Λ X Y
        let t' : SearchTree conc :=
          SearchTree.onePremise rule (SearchTree.leaf prem records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .neg X =>
        have hBin : FormulaN.neg X ∈ leaf.succedent := hBcase ▸ hB
        let split := Gentzen.Search.NoFunction.splitListAt leaf.succedent (FormulaN.neg X) hBin
        let Δ := split.val.1
        let Λ := split.val.2
        let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.neg X] ++ Λ)
        let prem : Sequent L := Sequent.mk ([X] ++ leaf.antecedent) (Δ ++ Λ)
        let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.negRight leaf.antecedent Δ Λ X
        let t' : SearchTree conc :=
          SearchTree.onePremise rule (SearchTree.leaf prem records)
        have hConc : conc = leaf := by
          show Sequent.mk _ _ = leaf
          congr 1
          exact split.property.symm
        hConc ▸ t'
    | .predN _ _ => SearchTree.leaf leaf records
    | .eq_ _ _ _ => SearchTree.leaf leaf records
    | .all _ _ => SearchTree.leaf leaf records
    | .ex _ _ => SearchTree.leaf leaf records
  · exact .leaf leaf records

/-- Definition 5.5.1: Extend each current leaf with its own branch records.
Newly created leaves are not visited again during this traversal. -/
@[blueprint "chap5__definition_5_5_1"]
def SearchTree.extendLeaves {L : Language}
    (extend : (s : Sequent L) → BranchRecords L → SearchTree s) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => extend s records
  | _, .onePremise rule sub => .onePremise rule (sub.extendLeaves extend)
  | _, .twoPremise rule left right =>
      .twoPremise rule (left.extendLeaves extend) (right.extendLeaves extend)
  | _, .extend a b sub => .extend a b (sub.extendLeaves extend)

/-- Definition 5.5.1: Grow every eligible nonaxiom leaf by the left rule for
the principal formula. Propositional rules preserve term and formula records;
∀:left uses the unused TERM₀ entries, and ∃:left activates one shared variable
only when an actual rule application occurs. Atomic formulae do nothing. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growLeft {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  match A with
  | .all x B => growLeftAll hL x B st
  | .ex x B => growLeftEx hL x B st
  | .predN _ _ => st
  | .eq_ _ _ _ => st
  | .conj _ _ | .disj _ _ | .impl _ _ | .neg _ =>
      { st with tree := st.tree.extendLeaves (growLeftPropAtLeaf hL A) }

/-- Definition 5.5.1: Grow every eligible nonaxiom leaf by the right rule for
the principal formula. Propositional rules preserve term and formula records;
∃:right uses the unused TERM₀ entries, and ∀:right activates one shared variable
only when an actual rule application occurs. Atomic formulae do nothing. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def growRight {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  match A with
  | .ex x B => growRightEx hL x B st
  | .all x B => growRightAll hL x B st
  | .predN _ _ => st
  | .eq_ _ _ _ => st
  | .conj _ _ | .disj _ _ | .impl _ _ | .neg _ =>
      { st with tree := st.tree.extendLeaves (growRightPropAtLeaf hL A) }

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

end LCS.FirstOrder.Completeness.Search
end

