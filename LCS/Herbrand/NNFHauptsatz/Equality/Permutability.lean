import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Equality.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Equality.PureVariable
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.Permutability.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.Permutability

Lemma 7.4.3: in a pure-variable G2nnf= proof without essential cuts every quantifier
rule can be permuted with a propositional rule, an inessential cut or a weakening.
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

/-- Exact one-premise applications for the equality calculus. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOnePremiseApplication {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | of (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfEqOnePremiseApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)

/-- Exact source premise of a selected quantifier application. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOnePremiseFrontier {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {rule : G2nnfRuleCore L} :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    {node : G2nnfEqProofTree hL Γnode Δnode} →
    G2nnfEqOnePremiseApplication rule node →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | of (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfEqOnePremiseFrontier
        (G2nnfEqOnePremiseApplication.of hAdmit hPrem hSC sub) sub

/-- The selected path contains only weakening steps, with no binary step. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqWeakeningOnlyPath {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfEqProofTree hL Γroot Δroot} →
    {node : G2nnfEqProofTree hL Γnode Δnode} →
    (path : G2nnfEqProofTree.RootToNodePath root node) → Type where
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfEqProofTree hL Γ Δ) :
      G2nnfEqWeakeningOnlyPath (.root T)
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfEqProofTree hL Γnode Δnode}
      {path : G2nnfEqProofTree.RootToNodePath sub node}
      (hWeak : rule.isWeakening)
      (rest : G2nnfEqWeakeningOnlyPath path) :
      G2nnfEqWeakeningOnlyPath
        (.onePremise rule hAdmit hPrem hSC sub path)

/-- An exact one/left/right lower-premise occurrence and its outside path. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqSelectedPremiseOccurrence {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot) (R₂ : G2nnfRuleCore L) :
    {Γprem Δprem : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γprem Δprem → Type where
  | one (hAdmit : True)
      (hPrem : (R₂.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.onePremise R₂ hAdmit hPrem hSC sub)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub
  | left (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub1
  | right (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub2

/-- The exact other sibling of a binary lower application; none for unary rules. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOtherPremiseFrontier {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L} :
    {Γselected Δselected : LCS.Finset (FormulaN L)} →
    {selectedTree : G2nnfEqProofTree hL Γselected Δselected} →
    G2nnfEqSelectedPremiseOccurrence root R₂ selectedTree →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | ofLeft (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqOtherPremiseFrontier
        (G2nnfEqSelectedPremiseOccurrence.left
          hAdmit hPrem hSC sub1 sub2 path) sub2
  | ofRight (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqOtherPremiseFrontier
        (G2nnfEqSelectedPremiseOccurrence.right
          hAdmit hPrem hSC sub1 sub2 path) sub1

namespace G2nnfEqSelectedPremiseOccurrence

@[blueprint "chap7__lemma_7_4_3"]
def choice {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp} :
    G2nnfEqSelectedPremiseOccurrence T r sub → G2nnfPremiseChoice
  | .one .. => .only
  | .left .. => .left
  | .right .. => .right

@[blueprint "chap7__lemma_7_4_3"]
def otherPremiseCount {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp}
    (selected : G2nnfEqSelectedPremiseOccurrence T r sub) : Nat :=
  match selected.choice with | .only => 0 | _ => 1

def node {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp} :
    G2nnfEqSelectedPremiseOccurrence T r sub →
      G2nnfEqProofTree hL r.conclusion.1 r.conclusion.2
  | .one ha hp hs sub _ => .onePremise r ha hp hs sub
  | .left ha hp hs sub₁ sub₂ _ => .twoPremise r ha hp hs sub₁ sub₂
  | .right ha hp hs sub₁ sub₂ _ => .twoPremise r ha hp hs sub₁ sub₂

def path {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp}
    (selected : G2nnfEqSelectedPremiseOccurrence T r sub) :
    G2nnfEqProofTree.RootToNodePath T selected.node :=
  match selected with
  | .one _ _ _ _ path => path
  | .left _ _ _ _ _ path => path
  | .right _ _ _ _ _ path => path

end G2nnfEqSelectedPremiseOccurrence

/-- Equality lower rules include only the existing propositional/weakening
schemas or a cut on an equation literal, with independent contexts. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationLowerView {L : Language} {hL : L.hasEquality = true} :
    G2nnfRuleCore L → Type where
  | ordinary {r : G2nnfRuleCore L} (view : G2nnfPermutationLowerRuleView r)
      (hScope : r.isPropositionalRule ∨ r.isWeakening) :
      G2nnfEqPermutationLowerView (hL := hL) r
  | cut (A : FormulaN L) (Λ Θ Γ Δ : LCS.Finset (FormulaN L))
      (literal : (G2nnfEqRule.base (.cut A Λ Θ Γ Δ) : G2nnfEqRule L hL).isInessentialCut) :
      G2nnfEqPermutationLowerView (.cut A Λ Θ Γ Δ)

/-- Raw contexts of the selected cut premise, or the common contexts of an
ordinary lower rule. No cut branch is identified with its sibling. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqSelectedContexts {L : Language} (r : G2nnfRuleCore L)
    (choice : G2nnfPremiseChoice) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  match r, choice with
  | .cut _ _ _ Γ Δ, .left => (Γ, Δ)
  | .cut _ Λ Θ _ _, .right => (Λ, Θ)
  | _, _ => g2nnfRuleSideContexts r

/-- One exact eligible equality-calculus occurrence pair, with only
weakening inferences between the selected premise and quantifier node. -/
@[blueprint "chap7__lemma_7_4_3"]
structure G2nnfEqPermutableOccurrence {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) (R₁ R₂ : G2nnfRuleCore L) where
  lowerView : G2nnfEqPermutationLowerView (hL := hL) R₂
  Γprem : LCS.Finset (FormulaN L)
  Δprem : LCS.Finset (FormulaN L)
  selectedPremise : G2nnfEqProofTree hL Γprem Δprem
  lowerApplication : G2nnfEqSelectedPremiseOccurrence T R₂ selectedPremise
  Γquant : LCS.Finset (FormulaN L)
  Δquant : LCS.Finset (FormulaN L)
  quantifierNode : G2nnfEqProofTree hL Γquant Δquant
  quantifierView : G2nnfQuantifierRuleView R₁
  quantifierApplication : G2nnfEqOnePremiseApplication R₁ quantifierNode
  pathFromSelectedPremise : G2nnfEqProofTree.RootToNodePath selectedPremise quantifierNode
  weakeningIntermediates : G2nnfEqWeakeningOnlyPath pathFromSelectedPremise

/-- Generated lower inferences retain the selected ordinary schema, its
focused instance, or exactly the selected equation-literal cut formula. -/
@[blueprint "chap7__lemma_7_4_3"]
def G2nnfEqLowerDescendant {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) (target : G2nnfRuleCore L) : Prop :=
  match redex.lowerView with
  | .ordinary view hScope => ∃ Γ Δ,
      target = view.withContexts Γ Δ ∨
      target = view.instantiateSelectedOfPropositional hScope redex.quantifierView redex.lowerApplication.choice Γ Δ
  | .cut A _ _ _ _ _ => ∃ Λ Θ Γ Δ, target = .cut A Λ Θ Γ Δ

/-- A moved quantifier retains its exact occurrence in a context formula,
or lifts it through the selected propositional side formula. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqQuantifierDescendant {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) : G2nnfRuleCore L → Type where
  | context
      (hMem : Membership.mem
        (redex.quantifierView.side.context
          (g2nnfEqSelectedContexts R₂ redex.lowerApplication.choice).1
          (g2nnfEqSelectedContexts R₂ redex.lowerApplication.choice).2)
        redex.quantifierView.principal)
      (Γ Δ : LCS.Finset (FormulaN L)) :
      G2nnfEqQuantifierDescendant redex
        (redex.quantifierView.reprincipalAt redex.quantifierView.occurrence rfl Γ Δ)
  | focused (lower : G2nnfPermutationLowerRuleView R₂)
      (hFocus : lower.selectedFocus redex.lowerApplication.choice =
        some (redex.quantifierView.side, redex.quantifierView.principal))
      (A : FormulaN L)
      (hPrincipal : lower.principal = some (redex.quantifierView.side, A))
      (lifted : G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift
        A redex.quantifierView.occurrence.selected)
      (hLift : lower.liftFocusedOccurrence redex.lowerApplication.choice hFocus hPrincipal
        redex.quantifierView.occurrence = some lifted)
      (Γ Δ : LCS.Finset (FormulaN L)) :
      G2nnfEqQuantifierDescendant redex
        (redex.quantifierView.reprincipalAt lifted.occurrence lifted.selected_eq Γ Δ)

/-- Local equality fragment body; only exact source frontiers, lower descendants and weakenings. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationBody {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Nat → Nat → Nat → Type where
  | quantifierFrontier {Γ Δ} {tree : G2nnfEqProofTree hL Γ Δ}
      (frontier : G2nnfEqOnePremiseFrontier redex.quantifierApplication tree) :
      G2nnfEqPermutationBody redex tree 1 0 0
  | otherFrontier {Γ Δ} {tree : G2nnfEqProofTree hL Γ Δ}
      (frontier : G2nnfEqOtherPremiseFrontier redex.lowerApplication tree) :
      G2nnfEqPermutationBody redex tree 0 1 0
  | lowerOne {rule : G2nnfRuleCore L} {q o b : Nat}
      (lineage : G2nnfEqLowerDescendant redex rule)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfEqPermutationBody redex sub q o b) :
      G2nnfEqPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub)
        q o (b + q)
  | lowerTwo {rule : G2nnfRuleCore L} {q₁ q₂ o₁ o₂ b₁ b₂ : Nat}
      (lineage : G2nnfEqLowerDescendant redex rule)
      (hAdmit : True) (hPrem : rule.premises.length = 2)
      (hSC : rule.SideConditions)
      (sub₁ : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (sub₂ : G2nnfEqProofTree hL
        (rule.premises[1]'(by omega)).1 (rule.premises[1]'(by omega)).2)
      (body₁ : G2nnfEqPermutationBody redex sub₁ q₁ o₁ b₁)
      (body₂ : G2nnfEqPermutationBody redex sub₂ q₂ o₂ b₂) :
      G2nnfEqPermutationBody redex (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
        (q₁ + q₂) (o₁ + o₂) (b₁ + b₂ + q₁ + q₂)
  | weakening {rule : G2nnfRuleCore L} {q o b : Nat}
      (hWeak : rule.isWeakening)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfEqPermutationBody redex sub q o b) :
      G2nnfEqPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub) q o b

/-- A local Q with the source frontiers fixed. Exactly one moved quantifier
lies below all generated lower-schema copies, with only weakenings below it.
At least one lower descendant lies on the path to the source quantifier
premise. The other premise is retained, with duplication permitted. Unlike
an adjacent bounded exchange, Q admits an arbitrary weakening section. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationFragment {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfEqProofTree hL Γ Δ → Type where
  | quantifier {Γ Δ Γbody Δbody : LCS.Finset (FormulaN L)}
      {tree : G2nnfEqProofTree hL Γ Δ}
      (targetRule : G2nnfRuleCore L)
      (correspondence : G2nnfEqQuantifierDescendant redex targetRule)
      (application : G2nnfEqOnePremiseApplication targetRule tree)
      (body : G2nnfEqProofTree hL Γbody Δbody)
      (premise : G2nnfEqOnePremiseFrontier application body)
      (otherCount lowerCount : Nat)
      (shape : G2nnfEqPermutationBody redex body 1 otherCount lowerCount)
      (usesOther : redex.lowerApplication.otherPremiseCount ≤ otherCount)
      (reversesOrder : 0 < lowerCount) :
      G2nnfEqPermutationFragment redex tree
  | weakening {rule : G2nnfRuleCore L}
      (hWeak : rule.isWeakening)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (fragment : G2nnfEqPermutationFragment redex sub) :
      G2nnfEqPermutationFragment redex (.onePremise rule hAdmit hPrem hSC sub)

-- ===================================================================
-- Lemma 7.4.3 (required def): CanPermuteWith_G2nnfEq
-- ===================================================================

/-- Lemma 7.4.3 (required def): Every eligible exact inference pair admits
its own local Q, retaining the selected quantifier premise, the other lower
premise when present, and the lower conclusion. Only Q's generated nodes are
restricted to the moved quantifier, lower-schema copies and weakenings.
Reused frontier proofs and the outside continuation are unrestricted. -/
@[blueprint "chap7__lemma_7_4_3"]
def CanPermuteWith_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (R₁ R₂ : G2nnfEqRule L hL)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) : Prop :=
  match R₁, R₂ with
  | .base r₁, .base r₂ =>
    ∀ redex : G2nnfEqPermutableOccurrence T r₁ r₂,
      ∃ Q : G2nnfEqProofTree hL r₂.conclusion.1 r₂.conclusion.2,
        Nonempty (G2nnfEqPermutationFragment redex Q)
  | _, _ => True

-- ===================================================================
-- Lemma 7.4.3: g2nnfEq_permutability
-- ===================================================================

/-- Lemma 7.4.3: For every pure-variable proof T in G2nnf= without essential cuts, every quantifier rule R_1 of G2nnf= can be permuted with a propositional rule R_2, an inessential cut R_2, or a weakening R_2. This extends Lemma 7.4.2 (the equality-free case) by adding the case of permuting a quantifier rule with an inessential cut, which follows the argument of Lemma 7.3.3. The propositional rule case and weakening case follow directly from the parallel arguments in Lemma 7.4.2, since the propositional and weakening rules of G2nnf= are identical to those of G2nnf. The proof proceeds by case analysis on the type of R_2: - If R_2 is propositional: use g2nnfEq_permutability_with_propositional - If R_2 is an inessential cut: use g2nnfEq_permutability_with_inessential_cut - If R_2 is a weakening: use g2nnfEq_permutability_with_weakening -/
@[attach_debt, blueprint "chap7__lemma_7_4_3" (main := true)]
theorem g2nnfEq_permutability
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfEqRule L hL)
    (hPure : IsPureVariableProof_G2nnfEq T)
    (hNEC : T.hasNoEssentialCuts)
    (hQuant : R₁.isQuantifierRule)
    (hR₂ : R₂.isPropositionalOrInessentialCut ∨
            R₂.isWeakening) :
    CanPermuteWith_G2nnfEq R₁ R₂ T 
end LCS.Herbrand.NNFHauptsatz.Equality
end
