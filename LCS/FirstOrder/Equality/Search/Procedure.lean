import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.Expand
import Attach
import LCS.FirstOrder.Equality.Search.Procedure.ProofsStamp

section
namespace LCS.FirstOrder.Equality.Search
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search

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

/-- Definition 5.6.3: The round-k equality-search approximant for fixed
admissible TERMS, AVAIL and EQ enumerations of the input reduct. -/
@[blueprint "chap5__definition_5_6_3" (main := true)]
noncomputable def searchEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  match k with
  | 0 => SearchState.init hL q hq hFB enum.terms enum.avail eqEnum
  | k + 1 => searchRound hL (searchEq hL q hq hFB enum eqEnum k)

/-- Definition 5.6.3: Equality search halts exactly when all leaves of some
finite-round approximant are finished, that is, axioms. -/
@[blueprint "chap5__definition_5_6_3"]
def haltsEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) : Prop :=
  ∃ k, allFinished hL (searchEq hL q hq hFB enum eqEnum k)

/-- Definition 5.6.3: The terminal messages, "T is a proof of Γ₀ → Δ₀"
and "Γ₀ → Δ₀ is falsifiable". A deduction tree all of whose leaves are
axioms is a proof (Definition 5.4.2). -/
@[blueprint "chap5__definition_5_6_3"]
inductive SearchOutput {L : Language} (root : Sequent L) : Type where
  | proof (T : InfGDeductionTreeExt root)
      (hClosed : ∀ leaf ∈ T.leaves, isAxiom leaf)
  | falsifiable

/-- Definition 5.6.3: While not all leaves are finished, there is no output.
After the loop, if all leaves are closed, write "T is a proof of Γ₀ → Δ₀";
otherwise, write "Γ₀ → Δ₀ is falsifiable". -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def outputEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat) :
    Option (SearchOutput (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList)) := by
  classical
  let st := searchEq hL q hq hFB enum eqEnum k
  exact if allFinished hL st then
    if hClosed : ∀ leaf ∈ st.tree.forget.leaves, isAxiom leaf then
      some (.proof st.tree.forget hClosed)
    else some .falsifiable
  else none

/-- Definition 5.6.3: Tree extension preserves every existing label and
edge and adds nodes only below leaves. -/
inductive InfGDeductionTreeExt.Extension {L : Language} :
    {s t : Sequent L} → InfGDeductionTreeExt s → InfGDeductionTreeExt t → Prop where
  | leaf {s} (t : InfGDeductionTreeExt s) : Extension (.leaf s) t
  | one {s p} (rule : GentzenStep1Ext p s) {a b : InfGDeductionTreeExt p} :
      Extension a b → Extension (.onePremise rule a) (.onePremise rule b)
  | two {s p q} (rule : GentzenStep2Ext p q s)
      {a b : InfGDeductionTreeExt p} {c d : InfGDeductionTreeExt q} :
      Extension a b → Extension c d → Extension (.twoPremise rule a c) (.twoPremise rule b d)
  | intro {s} (a b) {t u : InfGDeductionTreeExt (extendSeq s a b)} :
      Extension t u → Extension (.extend a b t) (.extend a b u)
  | eqIntro {s} (a b) (heads : List (EqEntry L)) (hne : heads ≠ [])
      {t u : InfGDeductionTreeExt (appendHeads (extendSeq s a b) heads)} :
      Extension t u → Extension (.extendEq a b heads hne t) (.extendEq a b heads hne u)

/-- Definition 5.6.3: Every search-stage tree extends itself. -/
theorem InfGDeductionTreeExt.Extension.refl {L : Language} {s : Sequent L}
    (t : InfGDeductionTreeExt s) : Extension t t := by
  induction t with
  | leaf => exact .leaf _
  | onePremise r _ ih => exact .one r ih
  | twoPremise r _ _ ih₁ ih₂ => exact .two r ih₁ ih₂
  | extend a b _ ih => exact .intro a b ih
  | extendEq a b hs hn _ ih => exact .eqIntro a b hs hn ih

/-- Definition 5.6.3: Successive leaf extensions compose. -/
theorem InfGDeductionTreeExt.Extension.trans {L : Language} {s t u : Sequent L}
    {a : InfGDeductionTreeExt s} {b : InfGDeductionTreeExt t} {c : InfGDeductionTreeExt u}
    (h₁ : Extension a b) (h₂ : Extension b c) : Extension a c := by
  induction h₁ generalizing u with
  | leaf => cases h₂ <;> exact .leaf _
  | one r h ih => cases h₂ with | one _ h₂ => exact .one r (ih h₂)
  | two r h₁ h₂ ih₁ ih₂ =>
    cases h₂ with | two _ ha hb => exact .two r (ih₁ ha) (ih₂ hb)
  | intro a b h ih => cases h₂ with | intro _ _ h₂ => exact .intro a b (ih h₂)
  | eqIntro a b hs hn h ih => cases h₂ with | eqIntro _ _ _ _ h₂ => exact .eqIntro a b hs hn (ih h₂)

/-- Definition 5.6.3: Read a node label by its tree address, with child 0
for unary and intake edges and children 0 and 1 for binary edges. -/
@[blueprint "chap5__definition_5_6_3"]
def InfGDeductionTreeExt.labelAt {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → List Nat → Option (Sequent L)
  | s, _, [] => some s
  | _, .leaf _, _ :: _ => none
  | _, .onePremise _ t, 0 :: p => t.labelAt p
  | _, .onePremise _ _, (_ + 1) :: _ => none
  | _, .twoPremise _ l _, 0 :: p => l.labelAt p
  | _, .twoPremise _ _ r, 1 :: p => r.labelAt p
  | _, .twoPremise _ _ _, (_ + 2) :: _ => none
  | _, .extend _ _ t, 0 :: p => t.labelAt p
  | _, .extend _ _ _, (_ + 1) :: _ => none
  | _, .extendEq _ _ _ _ t, 0 :: p => t.labelAt p
  | _, .extendEq _ _ _ _ _, (_ + 1) :: _ => none

/-- Definition 5.6.3: The limit tree consists exactly of the labeled nodes
appearing in a finite round approximant of the fixed run. -/
@[blueprint "chap5__definition_5_6_3"]
def searchLimitEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (address : List Nat) (label : Sequent L) : Prop :=
  ∃ k, (searchEq hL q hq hFB enum eqEnum k).tree.forget.labelAt address = some label

end LCS.FirstOrder.Equality.Search
end
