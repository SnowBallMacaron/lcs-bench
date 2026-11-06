import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.SearchState
import Attach
import LCS.FirstOrder.Completeness.Search.GrowLeftRight.ProofsStamp

/-! # Procedures grow-left and grow-right of Definition 5.5.1

Activation of a new variable (exists:left, for-all:right), instances with the
activated terms (for-all:left, exists:right), the propositional rules, and
grow-left and grow-right on every nonaxiom leaf.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen

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

end LCS.FirstOrder.Completeness.Search
end
