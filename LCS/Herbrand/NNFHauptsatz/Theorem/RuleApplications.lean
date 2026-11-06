import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.RuleApplications

Lemma 7.4.2: located rule applications, premise frontiers and selected premise
occurrences in G2nnf proof trees.
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Exact evidence that `node` is a one-premise application of `rule`, with
its stored contexts, bare admission, side conditions and premise tree
retained in the indexed rule and constructor data. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOnePremiseApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | of (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfOnePremiseApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)

namespace G2nnfOnePremiseApplication

/-- Raw antecedent context of the exact one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawGamma {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L} {Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γ Δ} :
    G2nnfOnePremiseApplication rule node →
      LCS.Finset (FormulaN L)
  | _ => (g2nnfRuleSideContexts rule).1

/-- Raw succedent context of the exact one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawDelta {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L} {Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γ Δ} :
    G2nnfOnePremiseApplication rule node →
      LCS.Finset (FormulaN L)
  | _ => (g2nnfRuleSideContexts rule).2

end G2nnfOnePremiseApplication

/-- Exact evidence that a node applies a fixed rule with its actual arity.
This is used for target lower-rule occurrences, which may have one or two
premises. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfRuleApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | one (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfRuleApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)
  | two (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub1 : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((rule.premises)[1]'(by omega)).1
        ((rule.premises)[1]'(by omega)).2) :
      G2nnfRuleApplication rule
        (.twoPremise rule hAdmit hPrem hSC sub1 sub2)

/-- The exact premise frontier hidden in a one-premise application witness. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOnePremiseFrontier {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {rule : G2nnfRuleCore L} :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    G2nnfOnePremiseApplication rule node →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | of (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfOnePremiseFrontier
        (G2nnfOnePremiseApplication.of hAdmit hPrem hSC sub) sub

namespace G2nnfOnePremiseFrontier

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact one-step path from an application to the premise frontier exposed
by its witness. -/
def path {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L}
    {Γnode Δnode Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γnode Δnode}
    {application : G2nnfOnePremiseApplication rule node}
    {sub : G2nnfProofTree hL Γ Δ}
    (frontier : G2nnfOnePremiseFrontier application sub) :
    RootToNodePath node sub :=
  match frontier with
  | .of hAdmit hPrem hSC sub =>
    .onePremise rule hAdmit hPrem hSC sub (.root sub)

end G2nnfOnePremiseFrontier

/-- Proof-relevant evidence that every rule strictly between the start and
target nodes of an exact path is a weakening.  A root path has no intermediate
rules.  There are intentionally no two-premise constructors: every G2nnf
weakening is one-premise, so a binary node cannot lie in the structural section
`ST`. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfWeakeningOnlyPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfProofTree hL Γroot Δroot} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    (path : RootToNodePath root node) → Type where
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfProofTree hL Γ Δ) :
      G2nnfWeakeningOnlyPath (.root T)
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfProofTree hL Γnode Δnode}
      {path : RootToNodePath sub node}
      (hWeak : rule.isWeakening)
      (rest : G2nnfWeakeningOnlyPath path) :
      G2nnfWeakeningOnlyPath
        (.onePremise rule hAdmit hPrem hSC sub path)

/-- An exact occurrence of a lower `R₂` application together with the selected
premise occurrence through which the upper quantifier `R₁` is reached.  The
constructors use `R₂` directly, rather than storing a node whose rule is merely
equal to `R₂`. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfSelectedPremiseOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) (R₂ : G2nnfRuleCore L) :
    {Γprem Δprem : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γprem Δprem → Type where
  | one (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (path : RootToNodePath root
        (.onePremise R₂ hAdmit hPrem hSC sub)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub
  | left (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub1
  | right (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub2

/-- The exact non-selected frontier of a binary lower application.  There is
no constructor for a one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOtherPremiseFrontier {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L} :
    {Γselected Δselected : LCS.Finset (FormulaN L)} →
    {selectedTree : G2nnfProofTree hL Γselected Δselected} →
    G2nnfSelectedPremiseOccurrence root R₂ selectedTree →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | ofLeft (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfOtherPremiseFrontier
        (G2nnfSelectedPremiseOccurrence.left
          hAdmit hPrem hSC sub1 sub2 path) sub2
  | ofRight (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfOtherPremiseFrontier
        (G2nnfSelectedPremiseOccurrence.right
          hAdmit hPrem hSC sub1 sub2 path) sub1

namespace G2nnfOtherPremiseFrontier

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact ambient path to the non-selected binary frontier.  The constructor
choice is complementary to the selected premise and remains
occurrence-sensitive even when both subtree values are equal. -/
def path {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other) :
    RootToNodePath root other :=
  match frontier with
  | .ofLeft hAdmit hPrem hSC sub1 sub2 applicationPath =>
      applicationPath.trans
        (.rightPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub2))
  | .ofRight hAdmit hPrem hSC sub1 sub2 applicationPath =>
      applicationPath.trans
        (.leftPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub1))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact node occurrence of the non-selected binary frontier. -/
def occurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other) :
    NodeOccurrence root Gamma Delta :=
  ⟨other, frontier.path⟩

end G2nnfOtherPremiseFrontier

/-- An exact located application of a fixed rule. -/
@[blueprint "chap7__lemma_7_4_2"]
structure G2nnfLocatedRuleApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) (rule : G2nnfRuleCore L) where
  Γ : LCS.Finset (FormulaN L)
  Δ : LCS.Finset (FormulaN L)
  node : G2nnfProofTree hL Γ Δ
  path : RootToNodePath root node
  application : G2nnfRuleApplication rule node

namespace G2nnfSelectedPremiseOccurrence

/-- Raw antecedent context of the exact lower-rule application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawGamma {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      LCS.Finset (FormulaN L)
  | .right .. =>
    match R₂ with
    | .cut _ Lambda Theta _ _ => Lambda
    | _ => (g2nnfRuleSideContexts R₂).1
  | _ => (g2nnfRuleSideContexts R₂).1

/-- Raw succedent context of the exact lower-rule application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawDelta {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      LCS.Finset (FormulaN L)
  | .right .. =>
    match R₂ with
    | .cut _ Lambda Theta _ _ => Theta
    | _ => (g2nnfRuleSideContexts R₂).2
  | _ => (g2nnfRuleSideContexts R₂).2

/-- The exact premise choice retained by the occurrence constructor. -/
@[blueprint "chap7__lemma_7_4_2"]
def choice {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      G2nnfPremiseChoice
  | .one _ _ _ _ _ => .only
  | .left _ _ _ _ _ _ => .left
  | .right _ _ _ _ _ _ => .right

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
/-- The exact lower-rule application occurrence containing the selected
premise. -/
def applicationOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) :
    G2nnfLocatedRuleApplication root R₂ :=
  match selected with
  | .one hAdmit hPrem hSC sub path =>
    ⟨_, _,
      .onePremise R₂ hAdmit hPrem hSC sub,
      path, .one hAdmit hPrem hSC sub⟩
  | .left hAdmit hPrem hSC sub1 sub2 path =>
    ⟨_, _,
      .twoPremise R₂ hAdmit hPrem hSC sub1 sub2,
      path, .two hAdmit hPrem hSC sub1 sub2⟩
  | .right hAdmit hPrem hSC sub1 sub2 path =>
    ⟨_, _,
      .twoPremise R₂ hAdmit hPrem hSC sub1 sub2,
      path, .two hAdmit hPrem hSC sub1 sub2⟩

/-- A one-premise lower application has no other frontier; a binary lower
application has exactly one. -/
@[blueprint "chap7__lemma_7_4_2"]
def otherPremiseCount {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) : Nat :=
  match selected with
  | .one .. => 0
  | .left .. => 1
  | .right .. => 1
end G2nnfSelectedPremiseOccurrence
end LCS.Herbrand.NNFHauptsatz.Theorem
end
