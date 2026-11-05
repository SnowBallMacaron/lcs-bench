import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.FirstOrder.Equality.Search.Part1.ProofsStamp

section
namespace LCS.FirstOrder.Equality.MetaTheorems
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen

/-- Theorem 5.6.4 (companion): A set Gamma is G_=-consistent when some
normalized formula is unprovable from every finite list of members of Gamma. -/
@[blueprint "chap5__theorem_5_6_4"]
def isConsistentSetEq {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L)) : Prop :=
  ∃ B : FormulaN L, ∀ cs : List (FormulaN L),
    (∀ c ∈ cs, c ∈ Gamma) →
    ¬ sequentProvableEq hL (Sequent.mk cs [B])

end LCS.FirstOrder.Equality.MetaTheorems
end

section
namespace LCS.FirstOrder.Equality.Search
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.6.3: At level i the term domain is TERMS ∪ AVAIL₁ ∪ … ∪ AVAILᵢ,
using the initial enumerations, including the y₀ fallback in TERMS. -/
@[blueprint "chap5__definition_5_6_3"]
def levelTerm {L : Language} (q : InfSequentN L) (i : Nat) (t : Term L) : Prop :=
  termsTerm q t ∨ ∃ k, 0 < k ∧ k ≤ i ∧ availTerm q k t

/-- Definition 5.6.3: Every argument lies in the level domain, and a positive
level uses at least one term from its own AVAILᵢ (the mixed-term reading). -/
@[blueprint "chap5__definition_5_6_3"]
def levelArguments {L : Language} (q : InfSequentN L) (i : Nat)
    (ts : List (Term L)) : Prop :=
  (∀ t ∈ ts, levelTerm q i t) ∧ (i = 0 ∨ ∃ t ∈ ts, availTerm q i t)

/-- Definition 5.6.3: The EQ families over the input reduct. Function congruence
uses positive ranks; EQ₃ includes every predicate rank and equality congruence.
The axiom constructors implement the right-nested conjunctions. -/
@[blueprint "chap5__definition_5_6_3"]
def EqLevelInstance {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (j i : Nat) (A : FormulaN L) : Prop :=
  (j = 1 ∧ ∃ t, levelArguments q i [t] ∧ A = .eq_ hL t t) ∨
  (j = 2 ∧ ∃ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
    f ∈ signedSetFunSyms (inputSignedSet q) ∧ 0 < L.funArity f ∧
    levelArguments q i (List.ofFn ss ++ List.ofFn ts) ∧
    A = eqCongruenceImplFunc L hL f ss ts) ∨
  (j = 3 ∧ ∃ (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L),
    P ∈ signedSetPredSyms (inputSignedSet q) ∧
    levelArguments q i (List.ofFn ss ++ List.ofFn ts) ∧
    A = eqCongruenceImplPred L hL P ss ts) ∨
  (j = 3 ∧ ∃ s₁ s₂ t₁ t₂, levelArguments q i [s₁, s₂, t₁, t₂] ∧
    A = eqCongruenceImplEq hL s₁ s₂ t₁ t₂)

/-- Definition 5.6.3: An equality formula with its generalized-rule witness. -/
@[blueprint "chap5__definition_5_6_3"]
def EqEntry (L : Language) :=
  { A : FormulaN L // ∀ hL : L.hasEquality = true, isEqAxiomInstance hL A }

/-- Definition 5.6.3: An equality enumeration has no holes or repeated entries. -/
@[blueprint "chap5__definition_5_6_3"]
structure EqStream (L : Language) where
  entries : Nat → Option (EqEntry L)
  noHoles : ∀ n, entries n = none → entries (n + 1) = none
  some_injective : ∀ n m A, entries n = some A → entries m = some A → n = m

/-- Definition 5.6.3: Admissible initial EQ streams enumerate exactly the
level families for the occurrence language of the possibly infinite input. -/
@[blueprint "chap5__definition_5_6_3"]
structure EqEnumeration {L : Language} (hL : L.hasEquality = true) (q : InfSequentN L) where
  streams : Nat → Nat → EqStream L
  enumerates : ∀ j i A,
    (∃ n e, (streams j i).entries n = some e ∧ e.val = A) ↔ EqLevelInstance hL q j i A

/-- Definition 5.6.3: Append an equality packet after the rightmost antecedent formula. -/
@[blueprint "chap5__definition_5_6_3"]
def appendHeads {L : Language} (s : Sequent L) (heads : List (EqEntry L)) : Sequent L :=
  .mk (s.antecedent ++ heads.map Subtype.val) s.succedent



/-- Definition 5.6.3: Each branch records its own principal formulae used
with the globally indexed TERM₀ and TERM₁ entries. -/
@[blueprint "chap5__definition_5_6_3"]
structure BranchRecords (L : Language) where
  FORM0 : Nat → List (FormulaN L)
  FORM1 : Nat → List (FormulaN L)

/-- Definition 5.6.3: The initial root has empty formula records. -/
@[blueprint "chap5__definition_5_6_3"]
def BranchRecords.empty (L : Language) : BranchRecords L :=
  ⟨fun _ => [], fun _ => []⟩

/-- Definition 5.6.3: A newly appended TERM₁ entry has an empty FORM₁
record on each branch; other records remain unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
def BranchRecords.clearFORM1 {L : Language} (r : BranchRecords L) (k : Nat) :
    BranchRecords L :=
  { r with FORM1 := fun j => if j = k then [] else r.FORM1 j }

/-- Definition 5.6.3: Append the current input heads to a finite sequent;
an exhausted side contributes no formula. -/
@[blueprint "chap5__definition_5_6_3"]
def extendSeq {L : Language} (s : Sequent L)
    (newAnt newSuc : Option (FormulaN L)) : Sequent L :=
  Sequent.mk (s.antecedent ++ newAnt.toList) (s.succedent ++ newSuc.toList)

/-- Definition 5.6.3: A finite stage of first-order infinite search, with
G-rule edges and explicit input-introduction edges. -/
@[blueprint "chap5__definition_5_6_3"]
inductive InfGDeductionTreeExt {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) : InfGDeductionTreeExt s
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      (sub : InfGDeductionTreeExt prem) : InfGDeductionTreeExt conc
  | twoPremise {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (left : InfGDeductionTreeExt p1) (right : InfGDeductionTreeExt p2) :
      InfGDeductionTreeExt conc
  | extend {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (sub : InfGDeductionTreeExt (extendSeq s newAnt newSuc)) : InfGDeductionTreeExt s
  | extendEq {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (heads : List (EqEntry L)) (hne : heads ≠ [])
      (sub : InfGDeductionTreeExt (appendHeads (extendSeq s newAnt newSuc) heads)) : InfGDeductionTreeExt s

/-- Definition 5.6.3: The root sequent of a search-stage deduction tree. -/
@[blueprint "chap5__definition_5_6_3"]
def InfGDeductionTreeExt.conclusion {L : Language} {s : Sequent L}
    (_ : InfGDeductionTreeExt s) : Sequent L := s

/-- Definition 5.6.3: Leaf labels in lexicographic tree-address order. -/
@[blueprint "chap5__definition_5_6_3"]
def InfGDeductionTreeExt.leaves {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → List (Sequent L)
  | _, .leaf s => [s]
  | _, .onePremise _ sub => sub.leaves
  | _, .twoPremise _ left right => left.leaves ++ right.leaves
  | _, .extend _ _ sub => sub.leaves
  | _, .extendEq _ _ _ _ sub => sub.leaves

/-- Definition 5.6.3: Search trees carry independent formula records at
leaves, actual G-rule witnesses, and explicit input-introduction edges. The conclusion is
an index, so every extension preserves the root sequent. -/
@[blueprint "chap5__definition_5_6_3"]
inductive SearchTree {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) (records : BranchRecords L) : SearchTree s
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      (sub : SearchTree prem) : SearchTree conc
  | twoPremise {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (left : SearchTree p1) (right : SearchTree p2) : SearchTree conc
  | extend {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (sub : SearchTree (extendSeq s newAnt newSuc)) : SearchTree s
  | extendEq {s : Sequent L} (newAnt newSuc : Option (FormulaN L))
      (heads : List (EqEntry L)) (hne : heads ≠ [])
      (sub : SearchTree (appendHeads (extendSeq s newAnt newSuc) heads)) : SearchTree s

/-- Definition 5.6.3: Forget branch records while preserving every G-rule
and input-introduction edge. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.forget {L : Language} : {s : Sequent L} → SearchTree s → InfGDeductionTreeExt s
  | _, .leaf s _ => .leaf s
  | _, .onePremise rule sub => .onePremise rule sub.forget
  | _, .twoPremise rule left right => .twoPremise rule left.forget right.forget
  | _, .extend a b sub => .extend a b sub.forget
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn sub.forget

/-- Definition 5.6.3: Initialize the newly appended TERM₁ record on every
branch of the tree, leaving its deductions and FORM₀ records unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.clearFORM1 {L : Language} (k : Nat) : {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s r => .leaf s (r.clearFORM1 k)
  | _, .onePremise rule sub => .onePremise rule (sub.clearFORM1 k)
  | _, .twoPremise rule left right =>
    .twoPremise rule (left.clearFORM1 k) (right.clearFORM1 k)
  | _, .extend a b sub => .extend a b (sub.clearFORM1 k)
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn (sub.clearFORM1 k)

/-- Definition 5.6.3: Global term lists, availability streams and activation
counter, together with the remaining input and the tree's branch-local records.
TERM₀ is the round snapshot; TERM₁ is its in-progress update. -/
@[blueprint "chap5__definition_5_6_3"]
structure SearchState (L : Language) (root : Sequent L) where
  TERM0 : List (Term L)
  TERM1 : List (Term L)
  avail : Nat → TermStream L
  numact : Nat
  /-- L and R are the antecedent and succedent streams of the remaining input. -/
  remaining : InfSequentN L
  tree : SearchTree root
  eqStreams : Nat → Nat → EqStream L
  eqUsed : Nat → Nat → Nat
  roundCounter : Nat
  numact0 : Nat

/-- Definition 5.6.3: Initially the tree consists of the input heads;
L and R are their tails, and the term bookkeeping comes from the admissible
enumerations with empty formula records at the unique root. The input uses
the x-variables and satisfies the set-wide free/bound convention. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchState.init {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i)
    (eqEnum : EqEnumeration hL q) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  let initial : InitialTermState L :=
    { term0 := initialTermRecords terms.toTermStream
      avail := fun i => match i with
        | 0 => terms.toTermStream.tail
        | j + 1 => (avail (j + 1) (by omega)).toTermStream
      numact := 0 }
  { TERM0 := initial.term0.map Prod.fst
    TERM1 := initial.term0.map Prod.fst
    avail := initial.avail
    numact := 0
    remaining := inputTail q
    tree := .leaf _ (BranchRecords.empty L)
    eqStreams := eqEnum.streams
    eqUsed := fun _ _ => 0
    roundCounter := 0
    numact0 := 0 }

/-- Definition 5.6.3: The two quantifier rules that activate a new variable. -/
@[blueprint "chap5__definition_5_6_3"]
inductive EigenRuleKind where
  | exLeft
  | allRight

/-- Definition 5.6.3: Extend an eligible nonaxiom leaf by the selected
quantifier rule using y. The flag is true exactly when a rule node is
constructed; membership, freshness and free-for side conditions are checked. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def activateAtLeaf {L : Language} (hL : L.hasEquality = true)
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

/-- Definition 5.6.3: Apply the selected eigenvariable rule once at every
eligible current leaf, using the same variable throughout this traversal. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def activateTree {L : Language} (hL : L.hasEquality = true)
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
  | _, .extendEq a b hs hn sub =>
    let result := activateTree hL kind x A y sub
    (.extendEq a b hs hn result.1, result.2)

/-- Definition 5.6.3: Consume head(AVAIL_{NUMACT+1}) only when an actual
quantifier-rule application occurs. Append its variable to TERM₁ with an
empty FORM₁ record on each branch, tail only that availability stream, and
increment NUMACT once. TERM₀ and the input pointers remain unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def activateVariable {L : Language} (hL : L.hasEquality = true)
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

/-- Definition 5.6.3: The ∃:left grow case activates the next available variable. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growLeftEx {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root := activateVariable hL .exLeft x A st

/-- Definition 5.6.3: The ∀:right grow case activates the next available variable. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growRightAll {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root := activateVariable hL .allRight x A st





/-- Definition 5.6.3: Select the TERM₀ positions whose branch-local FORM₀
record does not contain the principal formula, preserving the term order. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def pendingTerms {L : Language} (terms : List (Term L))
    (records : BranchRecords L) (principal : FormulaN L) : List (Term L × Nat) := by
  classical
  exact (terms.mapIdx fun k t => (t, k)).filter fun p => principal ∉ records.FORM0 p.2

/-- Definition 5.6.3: Record the principal formula in FORM₁ at precisely
the positions used in an extended inference on this branch. -/
@[blueprint "chap5__definition_5_6_3"]
def BranchRecords.recordInstances {L : Language} (records : BranchRecords L)
    (positions : List Nat) (principal : FormulaN L) : BranchRecords L :=
  { records with FORM1 := fun k =>
      if k ∈ positions then records.FORM1 k ++ [principal] else records.FORM1 k }

/-- Definition 5.6.3: The two rules using all unused TERM₀ terms in one inference. -/
@[blueprint "chap5__definition_5_6_3"]
inductive InstanceRuleKind where
  | allLeft
  | exRight

/-- Definition 5.6.3: The principal formula tested in the branch records. -/
@[blueprint "chap5__definition_5_6_3"]
def InstanceRuleKind.principal {L : Language} (kind : InstanceRuleKind)
    (x : Nat) (A : FormulaN L) : FormulaN L :=
  match kind with
  | .allLeft => .all x A
  | .exRight => .ex x A

/-- Definition 5.6.3: At a nonaxiom leaf, use every TERM₀ entry whose FORM₀
record lacks the principal formula in one extended ∀:left or ∃:right inference.
The terms must all be free for substitution. A successful inference appends
the principal formula to the selected FORM₁ records of this branch. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def instantiateAtLeaf {L : Language} (hL : L.hasEquality = true)
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

/-- Definition 5.6.3: Traverse the current leaves using their individual
FORM₀ and FORM₁ records and the global TERM₀ snapshot. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def instantiateTree {L : Language} (hL : L.hasEquality = true)
    (kind : InstanceRuleKind) (x : Nat) (A : FormulaN L) (terms : List (Term L)) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => instantiateAtLeaf hL kind x A terms s records
  | _, .onePremise rule sub => .onePremise rule (instantiateTree hL kind x A terms sub)
  | _, .twoPremise rule left right => .twoPremise rule
      (instantiateTree hL kind x A terms left) (instantiateTree hL kind x A terms right)
  | _, .extend a b sub => .extend a b (instantiateTree hL kind x A terms sub)
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn (instantiateTree hL kind x A terms sub)

/-- Definition 5.6.3: The ∀:left grow case uses the extended rule with
all terms unused for this principal formula on each branch. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growLeftAll {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  { st with tree := instantiateTree hL .allLeft x A st.TERM0 st.tree }

/-- Definition 5.6.3: The ∃:right grow case uses the extended rule with
all terms unused for this principal formula on each branch. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growRightEx {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (x : Nat) (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  { st with tree := instantiateTree hL .exRight x A st.TERM0 st.tree }

/-- Definition 5.6.3: Commit this branch's FORM₁ records for the existing
TERM₁ positions to FORM₀; appended availability heads have empty FORM₀ records. -/
@[blueprint "chap5__definition_5_6_3"]
def BranchRecords.commitRound {L : Language} (records : BranchRecords L)
    (term1Length : Nat) : BranchRecords L :=
  { records with FORM0 := fun k => if k < term1Length then records.FORM1 k else [] }

/-- Definition 5.6.3: Commit the formula records separately on every branch. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.commitRound {L : Language} (term1Length : Nat) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => .leaf s (records.commitRound term1Length)
  | _, .onePremise rule sub => .onePremise rule (sub.commitRound term1Length)
  | _, .twoPremise rule left right =>
      .twoPremise rule (left.commitRound term1Length) (right.commitRound term1Length)
  | _, .extend a b sub => .extend a b (sub.commitRound term1Length)
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn (sub.commitRound term1Length)

/-- Definition 5.6.3: Commit TERM₁ and its branch records to TERM₀, then
append the nonempty heads of AVAIL₀ through AVAIL_NUMACT in order, with empty
records. Tail only those streams; streams above NUMACT remain unchanged.
Input-pointer advancement is performed by the enclosing round driver. -/
@[blueprint "chap5__definition_5_6_3"]
def roundEndUpdate {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with
    TERM0 := st.TERM1 ++ (List.range (st.numact + 1)).filterMap (fun i => (st.avail i).head)
    avail := fun i => if i ≤ st.numact then (st.avail i).tail else st.avail i
    tree := st.tree.commitRound st.TERM1.length }





/-- Definition 5.6.3: A finished leaf is an axiom. -/
@[blueprint "chap5__definition_5_6_3"]
def isFinishedLeaf {L : Language} (_hL : L.hasEquality = true)
    {root : Sequent L} (_st : SearchState L root)
    (s : Sequent L) (_records : BranchRecords L) : Prop := isAxiom s

/-- Definition 5.6.3: Apply the matching propositional left rule to a
nonaxiom leaf containing the principal formula on the antecedent. Each
resulting branch inherits this leaf's records. Atomic and quantified formulae
leave the leaf unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growLeftPropAtLeaf {L : Language} (hL : L.hasEquality = true)
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

/-- Definition 5.6.3: Apply the matching propositional right rule to a
nonaxiom leaf containing the principal formula on the succedent. Each
resulting branch inherits this leaf's records. Atomic and quantified formulae
leave the leaf unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growRightPropAtLeaf {L : Language} (hL : L.hasEquality = true)
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

/-- Definition 5.6.3: Extend each current leaf with its own branch records.
Newly created leaves are not visited again during this traversal. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.extendLeaves {L : Language}
    (extend : (s : Sequent L) → BranchRecords L → SearchTree s) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => extend s records
  | _, .onePremise rule sub => .onePremise rule (sub.extendLeaves extend)
  | _, .twoPremise rule left right =>
      .twoPremise rule (left.extendLeaves extend) (right.extendLeaves extend)
  | _, .extend a b sub => .extend a b (sub.extendLeaves extend)
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn (sub.extendLeaves extend)

/-- Definition 5.6.3: Grow every eligible nonaxiom leaf by the left rule for
the principal formula. Propositional rules preserve term and formula records;
∀:left uses the unused TERM₀ entries, and ∃:left activates one shared variable
only when an actual rule application occurs. Atomic formulae do nothing. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growLeft {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  match A with
  | .all x B => growLeftAll hL x B st
  | .ex x B => growLeftEx hL x B st
  | .predN _ _ => st
  | .eq_ _ _ _ => st
  | .conj _ _ | .disj _ _ | .impl _ _ | .neg _ =>
      { st with tree := st.tree.extendLeaves (growLeftPropAtLeaf hL A) }

/-- Definition 5.6.3: Grow every eligible nonaxiom leaf by the right rule for
the principal formula. Propositional rules preserve term and formula records;
∃:right uses the unused TERM₀ entries, and ∀:right activates one shared variable
only when an actual rule application occurs. Atomic formulae do nothing. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def growRight {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (A : FormulaN L) (st : SearchState L root) :
    SearchState L root :=
  match A with
  | .ex x B => growRightEx hL x B st
  | .all x B => growRightAll hL x B st
  | .predN _ _ => st
  | .eq_ _ _ _ => st
  | .conj _ _ | .disj _ _ | .impl _ _ | .neg _ =>
      { st with tree := st.tree.extendLeaves (growRightPropAtLeaf hL A) }

/-- Definition 5.6.3: Carry the global term lists, availability streams and
input pointers into a local tree, or back into the enclosing tree. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchState.withTree {L : Language} {root s : Sequent L}
    (st : SearchState L root) (tree : SearchTree s) : SearchState L s :=
  { TERM0 := st.TERM0, TERM1 := st.TERM1, avail := st.avail,
    numact := st.numact, remaining := st.remaining, tree := tree,
    eqStreams := st.eqStreams, eqUsed := st.eqUsed,
    roundCounter := st.roundCounter, numact0 := st.numact0 }

/-- Definition 5.6.3: The round's fixed heads, in increasing level order,
from EQ_{(RC mod 3)+1,i} for i = 0,…,NUMACT₀. -/
@[blueprint "chap5__definition_5_6_3"]
def equalityHeads {L : Language} {root : Sequent L} (st : SearchState L root) :
    List (EqEntry L) :=
  let j := (st.roundCounter % 3) + 1
  (List.range (st.numact0 + 1)).filterMap fun i =>
    (st.eqStreams j i).entries (st.eqUsed j i)

/-- Definition 5.6.3: Create one u₁ child per local leaf. Its antecedent is
Γ, head(L), followed by the fixed EQ heads; its succedent is Δ, head(R).
A nonempty equality packet carries one generalized-equality inference.
Empty packets contribute only the input-introduction edge. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def intake {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root := by
  classical
  let a := st.remaining.antecedent 0
  let b := st.remaining.succedent 0
  let heads := equalityHeads st
  exact { st with tree := st.tree.extendLeaves fun s r =>
    if hn : heads = [] then .extend a b (.leaf (extendSeq s a b) r)
    else .extendEq a b heads hn (.leaf (appendHeads (extendSeq s a b) heads) r) }

/-- Definition 5.6.3: Expand an unfinished leaf. Grow the original antecedent
formulae in order, then the original succedent formulae in order, and finally
create the u₁ child at each resulting leaf. All leaves in a round read the same
input heads; this operation does not advance the input pointers. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def expandLeaf {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (st : SearchState L root) (s : Sequent L)
    (records : BranchRecords L) : SearchState L s := by
  classical
  let localState := st.withTree (.leaf s records)
  exact if isFinishedLeaf hL st s records then localState else
    let leftGrown := s.antecedent.foldl (fun acc A => growLeft hL A acc) localState
    let bothGrown := s.succedent.foldl (fun acc A => growRight hL A acc) leftGrown
    intake bothGrown

/-- Definition 5.6.3: Substitute the expanded local tree at the designated
leaf address. Child 0 is used for unary and intake edges; binary children are
0 and 1. Invalid addresses and addresses of internal nodes leave the state
unchanged. Global term and availability updates are returned to the enclosing
tree, while untouched branches keep their own records. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def expand {L : Language} (hL : L.hasEquality = true) :
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
    | .extendEq a b hs hn sub =>
      let result := expand hL path (st.withTree sub)
      result.withTree (.extendEq a b hs hn result.tree)
  | _, 1 :: path, st =>
    match st.tree with
    | .twoPremise rule left right =>
      let result := expand hL path (st.withTree right)
      result.withTree (.twoPremise rule left result.tree)
    | _ => st
  | _, _ :: _, st => st

/-- Definition 5.6.3: Advance L and R once, after all original leaves of the
round have been expanded. The no-holes invariants are preserved by taking tails. -/
@[blueprint "chap5__definition_5_6_3"]
def advanceInput {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with remaining := inputTail st.remaining }

/-- Definition 5.6.3: Leaf addresses in lexicographic order. Unary rule
and intake edges use child 0; binary rule edges use children 0 and 1. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.leafAddresses {L : Language} : {s : Sequent L} → SearchTree s → List (List Nat)
  | _, .leaf _ _ => [[]]
  | _, .onePremise _ sub => sub.leafAddresses.map (0 :: ·)
  | _, .twoPremise _ left right =>
      left.leafAddresses.map (0 :: ·) ++ right.leafAddresses.map (1 :: ·)
  | _, .extend _ _ sub => sub.leafAddresses.map (0 :: ·)
  | _, .extendEq _ _ _ _ sub => sub.leafAddresses.map (0 :: ·)

/-- Definition 5.6.3: All leaf labels paired with their own formula records. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.leaves {L : Language} :
    {s : Sequent L} → SearchTree s → List (Sequent L × BranchRecords L)
  | _, .leaf s records => [(s, records)]
  | _, .onePremise _ sub => sub.leaves
  | _, .twoPremise _ left right => left.leaves ++ right.leaves
  | _, .extend _ _ sub => sub.leaves
  | _, .extendEq _ _ _ _ sub => sub.leaves

/-- Definition 5.6.3: All leaves are finished precisely when all are axioms. -/
@[blueprint "chap5__definition_5_6_3"]
def allFinished {L : Language} (hL : L.hasEquality = true) {root : Sequent L}
    (st : SearchState L root) : Prop :=
  ∀ leaf ∈ st.tree.leaves, isFinishedLeaf hL st leaf.1 leaf.2

/-- Definition 5.6.3: Copy FORM₀ into FORM₁ independently on every branch
at the start of a round, preserving all rule and intake edges. -/
@[blueprint "chap5__definition_5_6_3"]
def SearchTree.startRound {L : Language} : {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records => .leaf s { records with FORM1 := records.FORM0 }
  | _, .onePremise rule sub => .onePremise rule sub.startRound
  | _, .twoPremise rule left right => .twoPremise rule left.startRound right.startRound
  | _, .extend a b sub => .extend a b sub.startRound
  | _, .extendEq a b hs hn sub => .extendEq a b hs hn sub.startRound

/-- Definition 5.6.3: Start a round by copying TERM₀ and its branch records
to TERM₁ and FORM₁, and freeze NUMACT₀ before any activation. -/
@[blueprint "chap5__definition_5_6_3"]
def startRound {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with TERM1 := st.TERM0, tree := st.tree.startRound, numact0 := st.numact }

/-- Definition 5.6.3: One round expands the original leaves in lexicographic
address order. Every u₁ step uses the same EQ heads and NUMACT₀ snapshot.
At round end, commit TERM₁, advance L/R and the selected EQ streams once,
increment RC, and transfer the heads of all now-active AVAIL streams.
A state whose leaves are all axioms is left unchanged. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def searchRound {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (st : SearchState L root) : SearchState L root := by
  classical
  exact if allFinished hL st then st else
    let expanded := st.tree.leafAddresses.foldl (fun acc path => expand hL path acc) (startRound st)
    let committed := roundEndUpdate (advanceInput expanded)
    { committed with
      eqUsed := fun j i =>
        if j = (st.roundCounter % 3) + 1 ∧ i ≤ st.numact then st.eqUsed j i + 1
        else st.eqUsed j i
      roundCounter := st.roundCounter + 1 }

end LCS.FirstOrder.Equality.Search
end

