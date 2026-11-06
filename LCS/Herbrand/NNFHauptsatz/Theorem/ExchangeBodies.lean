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
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences

/-! # Herbrand.NNFHauptsatz.Theorem.ExchangeBodies

Lemma 7.4.2: the exchanged fragment above the moved quantifier rule, the positions
of its generated nodes (direct and contraction cases) and their located applications.
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

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Fixed weakening schemas which may occur in the bounded simulation.  The
weakened formula is computed from a source principal or its exact quantifier
image; no arbitrary formula can be injected into the exchanged fragment. -/
inductive G2nnfExchangeWeakening {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    G2nnfRuleCore L → Type where
  | quantifierPrincipal (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (redex.quantifierRule.side.weakeningRule
          redex.quantifierRule.principal Gamma Delta)
  | quantifierPremise (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (redex.quantifierRule.side.weakeningRule
          redex.quantifierRule.premisePrincipal Gamma Delta)
  | lowerPrincipal (side : G2nnfSequentSide) (F : FormulaN L)
      (hPrincipal : redex.lowerRule.principal = some (side, F))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex (side.weakeningRule F Gamma Delta)
  | instantiatedLowerPrincipal
      (side : G2nnfSequentSide) (F : FormulaN L)
      (hPrincipal :
        redex.lowerRule.instantiatedPrincipal
          redex.quantifierRule redex.lowerApplication.choice =
            some (side, F))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (side.weakeningRule F Gamma Delta)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Exact-shape grammar for the part of the exchanged fragment above the
moved quantifier.  Leaves are only the original quantifier premise and the
original non-selected lower premise.  Internal nodes are only lower-schema
descendants or one of the fixed weakening simulations above.  In particular,
there is no cut constructor and no constructor accepting the old selected
premise, quantifier node, or an arbitrary proof tree. -/
inductive G2nnfExchangeBody {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | quantifierFrontier
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOnePremiseFrontier
        redex.quantifierApplication tree) :
      G2nnfExchangeBody redex tree
  | otherFrontier
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOtherPremiseFrontier
        redex.lowerApplication tree) :
      G2nnfExchangeBody redex tree
  | lowerOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub) :
      G2nnfExchangeBody redex
        (.onePremise targetRule hAdmit hPrem hSC sub)
  | lowerTwo {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2) :
      G2nnfExchangeBody redex
        (.twoPremise targetRule hAdmit hPrem hSC sub1 sub2)
  | weakening {targetRule : G2nnfRuleCore L}
      (allowed : G2nnfExchangeWeakening redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub) :
      G2nnfExchangeBody redex
        (.onePremise targetRule hAdmit hPrem hSC sub)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A grammar-derived path to the exact source quantifier-premise frontier.
It may cross only nodes generated by `G2nnfExchangeBody`; the sole stopping
constructor is the exact quantifier frontier itself. -/
inductive G2nnfExchangeBodyQuantifierPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    {tree : G2nnfProofTree hL Γ Δ} →
    G2nnfExchangeBody redex tree → Type where
  | here
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOnePremiseFrontier
        redex.quantifierApplication tree) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.quantifierFrontier frontier)
  | underLowerOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerOne lineage hAdmit hPrem hSC sub body)
  | underLowerTwoLeft {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyQuantifierPosition redex body1) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerTwoRight {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyQuantifierPosition redex body2) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underWeakening {targetRule : G2nnfRuleCore L}
      (allowed : G2nnfExchangeWeakening redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.weakening allowed hAdmit hPrem hSC sub body)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A position of a lower-schema node generated by `G2nnfExchangeBody`
itself.  The `here` constructors stop only at `.lowerOne` or `.lowerTwo`;
recursive constructors cross only generated lower/weakening nodes.  There is
intentionally no constructor which descends through either frontier, so a
stale application inside a reused source subtree cannot be selected. -/
inductive G2nnfExchangeBodyLowerPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    (targetRule : G2nnfRuleCore L) →
    G2nnfLowerRuleDescendant redex targetRule →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    {tree : G2nnfProofTree hL Γ Δ} →
    G2nnfExchangeBody redex tree → Type where
  | hereOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerOne lineage hAdmit hPrem hSC sub body)
  | hereTwoLeft {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body1) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | hereTwoRight {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body2) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerOne {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerOne outerLineage hAdmit hPrem hSC sub body)
  | underLowerTwoLeft {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body1) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerTwoRight {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body2) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underWeakening {targetRule weakeningRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (allowed : G2nnfExchangeWeakening redex weakeningRule)
      (hAdmit : weakeningRule.BareAtomicAxiom)
      (hPrem : (weakeningRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions weakeningRule)
      (sub : G2nnfProofTree hL
        ((weakeningRule.premises)[0]'(by omega)).1
        ((weakeningRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.weakening allowed hAdmit hPrem hSC sub body)

/-- A focused lower-schema instance is a nonaxiom and is admitted by the
bare-axiom predicate, independently of its output contexts. -/
private theorem instantiatedLower_bare {L : Language}
    {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (hLower : R₂.isPropositionalRule ∨ R₂.isWeakening)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice) (Gamma Delta : LCS.Finset (FormulaN L)) :
    (lower.instantiateSelectedOfPropositional hLower quantifier choice Gamma Delta).BareAtomicAxiom := by
  cases lower <;> cases choice <;> first
  | trivial
  | exact False.elim (by
      simpa [G2nnfRuleCore.isPropositionalRule, G2nnfRuleCore.isWeakening] using hLower)

/-- The two nested lower applications required by the textbook contraction
simulation.  The instantiated descendant is outermost on the selected body
branch; an original-lineage descendant occurs strictly inside its selected
premise on the same path to the exact quantifier frontier. The two nested
applications retain their separate output contexts. -/
inductive G2nnfExchangeBodyContractionPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    {tree : G2nnfProofTree hL Γ Δ} →
    G2nnfExchangeBody redex tree → Type where
  | hereOne
      (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : ((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta))
      (sub : G2nnfProofTree hL
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).1
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (originalGamma originalDelta : LCS.Finset (FormulaN L))
      (originalPosition :
        G2nnfExchangeBodyLowerPosition redex
          (redex.lowerRule.withContexts originalGamma originalDelta)
          (.original originalGamma originalDelta) body) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerOne (.instantiated Gamma Delta)
          (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
            redex.lowerApplication.choice Gamma Delta) hPrem hSC sub body)
  | hereTwoLeft
      (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : ((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta))
      (sub1 : G2nnfProofTree hL
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).1
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[1]'(by omega)).1
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (originalGamma originalDelta : LCS.Finset (FormulaN L))
      (originalPosition :
        G2nnfExchangeBodyLowerPosition redex
          (redex.lowerRule.withContexts originalGamma originalDelta)
          (.original originalGamma originalDelta) body1) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo (.instantiated Gamma Delta)
          (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
            redex.lowerApplication.choice Gamma Delta) hPrem hSC
          sub1 sub2 body1 body2)
  | hereTwoRight
      (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : ((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta))
      (sub1 : G2nnfProofTree hL
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).1
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[1]'(by omega)).1
        (((redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta).premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (originalGamma originalDelta : LCS.Finset (FormulaN L))
      (originalPosition :
        G2nnfExchangeBodyLowerPosition redex
          (redex.lowerRule.withContexts originalGamma originalDelta)
          (.original originalGamma originalDelta) body2) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo (.instantiated Gamma Delta)
          (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
            redex.lowerApplication.choice Gamma Delta) hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerOne {outerRule : G2nnfRuleCore L}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyContractionPosition redex body) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerOne outerLineage hAdmit hPrem hSC sub body)
  | underLowerTwoLeft {outerRule : G2nnfRuleCore L}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyContractionPosition redex body1) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerTwoRight {outerRule : G2nnfRuleCore L}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyContractionPosition redex body2) :
      G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underWeakening {weakeningRule : G2nnfRuleCore L}
      (allowed : G2nnfExchangeWeakening redex weakeningRule)
      (hAdmit : weakeningRule.BareAtomicAxiom)
      (hPrem : (weakeningRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions weakeningRule)
      (sub : G2nnfProofTree hL
        ((weakeningRule.premises)[0]'(by omega)).1
        ((weakeningRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyContractionPosition redex body) :
      G2nnfExchangeBodyContractionPosition redex
        (.weakening allowed hAdmit hPrem hSC sub body)

/-- Case-indexed exchange simulation.  Direct/context and direct/focused
cases select one original or instantiated lower descendant respectively.
The contraction constructor is available only for a focused principal and
contains the strictly nested two-lower simulation above. -/
inductive G2nnfExchangeCasePosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    {tree : G2nnfProofTree hL Γ Δ}
    (body : G2nnfExchangeBody redex tree) :
    G2nnfPrincipalOccurrenceRole redex.quantifierRule.side
        redex.quantifierRule.principal
        redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
        (redex.lowerRule.selectedFocus redex.lowerApplication.choice) →
      G2nnfQuantifierPrincipalCase redex.quantifierRule.side
        redex.quantifierRule.principal
        redex.quantifierApplication.rawGamma
        redex.quantifierApplication.rawDelta
        redex.lowerApplication.rawGamma
        redex.lowerApplication.rawDelta →
      Type where
  | directContext
      (hMem : Membership.mem
        (redex.quantifierRule.side.context
          redex.lowerApplication.rawGamma
          redex.lowerApplication.rawDelta)
        redex.quantifierRule.principal)
      (hDirect :
        Membership.mem
          (redex.quantifierRule.side.context
            redex.lowerApplication.rawGamma
            redex.lowerApplication.rawDelta)
          redex.quantifierRule.principal ∨
        ¬ Membership.mem
          (redex.quantifierRule.side.context
            redex.quantifierApplication.rawGamma
            redex.quantifierApplication.rawDelta)
          redex.quantifierRule.principal)
      (targetGamma targetDelta : LCS.Finset (FormulaN L))
      (position :
        G2nnfExchangeBodyLowerPosition redex
          (redex.lowerRule.withContexts targetGamma targetDelta)
          (.original targetGamma targetDelta) body) :
      G2nnfExchangeCasePosition redex body
        (.context hMem) (.direct hDirect)
  | directFocused
      (hNotMem : ¬ Membership.mem
        (redex.quantifierRule.side.context
          redex.lowerApplication.rawGamma
          redex.lowerApplication.rawDelta)
        redex.quantifierRule.principal)
      (hFocus : redex.lowerRule.selectedFocus
        redex.lowerApplication.choice =
          some (redex.quantifierRule.side,
            redex.quantifierRule.principal))
      (hDirect :
        Membership.mem
          (redex.quantifierRule.side.context
            redex.lowerApplication.rawGamma
            redex.lowerApplication.rawDelta)
          redex.quantifierRule.principal ∨
        ¬ Membership.mem
          (redex.quantifierRule.side.context
            redex.quantifierApplication.rawGamma
            redex.quantifierApplication.rawDelta)
          redex.quantifierRule.principal)
      (targetGamma targetDelta : LCS.Finset (FormulaN L))
      (position :
        G2nnfExchangeBodyLowerPosition redex
          (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice targetGamma targetDelta)
          (.instantiated targetGamma targetDelta) body) :
      G2nnfExchangeCasePosition redex body
        (.focused hNotMem hFocus) (.direct hDirect)
  | withContraction
      (hNotMem : ¬ Membership.mem
        (redex.quantifierRule.side.context
          redex.lowerApplication.rawGamma
          redex.lowerApplication.rawDelta)
        redex.quantifierRule.principal)
      (hFocus : redex.lowerRule.selectedFocus
        redex.lowerApplication.choice =
          some (redex.quantifierRule.side,
            redex.quantifierRule.principal))
      (hLower : ¬ Membership.mem
        (redex.quantifierRule.side.context
          redex.lowerApplication.rawGamma
          redex.lowerApplication.rawDelta)
        redex.quantifierRule.principal)
      (hTop : Membership.mem
        (redex.quantifierRule.side.context
          redex.quantifierApplication.rawGamma
          redex.quantifierApplication.rawDelta)
        redex.quantifierRule.principal)
      (position : G2nnfExchangeBodyContractionPosition redex body) :
      G2nnfExchangeCasePosition redex body
        (.focused hNotMem hFocus) (.withContraction hLower hTop)

/-- The exact source quantifier frontier and its grammar-derived path inside
an exchange body. -/
structure G2nnfGeneratedQuantifierFrontier {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    {Γbody Δbody : LCS.Finset (FormulaN L)}
    (body : G2nnfProofTree hL Γbody Δbody) where
  Γ : LCS.Finset (FormulaN L)
  Δ : LCS.Finset (FormulaN L)
  tree : G2nnfProofTree hL Γ Δ
  frontier :
    G2nnfOnePremiseFrontier redex.quantifierApplication tree
  path : RootToNodePath body tree

/-- The ordinary located rule application computed from a generated body
position.  Its path is output data, never an input to the certificate. -/
structure G2nnfGeneratedLowerApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (targetRule : G2nnfRuleCore L)
    (_lineage : G2nnfLowerRuleDescendant redex targetRule)
    {Γbody Δbody : LCS.Finset (FormulaN L)}
    (body : G2nnfProofTree hL Γbody Δbody) where
  Γ : LCS.Finset (FormulaN L)
  Δ : LCS.Finset (FormulaN L)
  node : G2nnfProofTree hL Γ Δ
  application : G2nnfRuleApplication targetRule node
  path : RootToNodePath body node
  Γfrontier : LCS.Finset (FormulaN L)
  Δfrontier : LCS.Finset (FormulaN L)
  quantifierFrontier : G2nnfProofTree hL Γfrontier Δfrontier
  exactQuantifierFrontier :
    G2nnfOnePremiseFrontier
      redex.quantifierApplication quantifierFrontier
  pathToQuantifierFrontier :
    RootToNodePath node quantifierFrontier

/-- Both nested lower applications and the exact frontier path computed from
one contraction-position witness. -/
structure G2nnfGeneratedContractionSimulation {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    {Γbody Δbody : LCS.Finset (FormulaN L)}
    (body : G2nnfProofTree hL Γbody Δbody) where
  outerGamma : LCS.Finset (FormulaN L)
  outerDelta : LCS.Finset (FormulaN L)
  outer : G2nnfGeneratedLowerApplication redex
    (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice outerGamma outerDelta)
    (.instantiated outerGamma outerDelta) body
  Γinner : LCS.Finset (FormulaN L)
  Δinner : LCS.Finset (FormulaN L)
  innerNode : G2nnfProofTree hL Γinner Δinner
  innerGamma : LCS.Finset (FormulaN L)
  innerDelta : LCS.Finset (FormulaN L)
  innerApplication : G2nnfRuleApplication
    (redex.lowerRule.withContexts innerGamma innerDelta) innerNode
  pathFromOuterToInner : RootToNodePath outer.node innerNode
  Γfrontier : LCS.Finset (FormulaN L)
  Δfrontier : LCS.Finset (FormulaN L)
  quantifierFrontier : G2nnfProofTree hL Γfrontier Δfrontier
  exactQuantifierFrontier :
    G2nnfOnePremiseFrontier
      redex.quantifierApplication quantifierFrontier
  pathFromInnerToQuantifierFrontier :
    RootToNodePath innerNode quantifierFrontier

namespace G2nnfExchangeBodyLowerPosition

/-- The exact quantifier-frontier branch retained inside a generated lower
position. -/
def quantifierPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {targetRule : G2nnfRuleCore L}
    {lineage : G2nnfLowerRuleDescendant redex targetRule}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    (position :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage body) :
    G2nnfExchangeBodyQuantifierPosition redex body :=
  match position with
  | .hereOne lineage hAdmit hPrem hSC sub body quantifierPosition =>
    .underLowerOne lineage hAdmit hPrem hSC
      sub body quantifierPosition
  | .hereTwoLeft lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition =>
    .underLowerTwoLeft lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition
  | .hereTwoRight lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition =>
    .underLowerTwoRight lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition
  | .underLowerOne outerLineage hAdmit hPrem hSC
      sub body position =>
    .underLowerOne outerLineage hAdmit hPrem hSC
      sub body position.quantifierPosition
  | .underLowerTwoLeft outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    .underLowerTwoLeft outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position.quantifierPosition
  | .underLowerTwoRight outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    .underLowerTwoRight outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position.quantifierPosition
  | .underWeakening allowed hAdmit hPrem hSC sub body position =>
    .underWeakening allowed hAdmit hPrem hSC
      sub body position.quantifierPosition

end G2nnfExchangeBodyLowerPosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end
