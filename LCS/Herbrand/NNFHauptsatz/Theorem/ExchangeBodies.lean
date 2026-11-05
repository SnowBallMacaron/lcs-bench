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
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths
import LCS.Herbrand.NNFHauptsatz.Theorem.Purity
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences

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

end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeBodyQuantifierPosition

/-- Compute the exact source frontier and path selected by a grammar-derived
quantifier position. -/
def located {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    (position : G2nnfExchangeBodyQuantifierPosition redex body) :
    G2nnfGeneratedQuantifierFrontier redex tree :=
  match position with
  | .here frontier =>
    { Γ := _
      Δ := _
      tree := _
      frontier := frontier
      path := .root _ }
  | .underLowerOne lineage hAdmit hPrem hSC sub body position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      tree := inner.tree
      frontier := inner.frontier
      path := .onePremise _ hAdmit hPrem hSC sub inner.path }
  | .underLowerTwoLeft lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      tree := inner.tree
      frontier := inner.frontier
      path := .leftPremise _ hAdmit hPrem hSC
        sub1 sub2 inner.path }
  | .underLowerTwoRight lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      tree := inner.tree
      frontier := inner.frontier
      path := .rightPremise _ hAdmit hPrem hSC
        sub1 sub2 inner.path }
  | .underWeakening allowed hAdmit hPrem hSC sub body position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      tree := inner.tree
      frontier := inner.frontier
      path := .onePremise _ hAdmit hPrem hSC sub inner.path }

end G2nnfExchangeBodyQuantifierPosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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

end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeBodyContractionPosition

/-- Output contexts of the outer instantiated node retained by the position. -/
def outputContexts {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    (position : G2nnfExchangeBodyContractionPosition redex body) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  match position with
  | .hereOne Gamma Delta _ _ _ _ _ _ _ => (Gamma, Delta)
  | .hereTwoLeft Gamma Delta _ _ _ _ _ _ _ _ _ => (Gamma, Delta)
  | .hereTwoRight Gamma Delta _ _ _ _ _ _ _ _ _ => (Gamma, Delta)
  | .underLowerOne _ _ _ _ _ _ position => position.outputContexts
  | .underLowerTwoLeft _ _ _ _ _ _ _ _ position => position.outputContexts
  | .underLowerTwoRight _ _ _ _ _ _ _ _ position => position.outputContexts
  | .underWeakening _ _ _ _ _ _ position => position.outputContexts

/-- The outer instantiated lower node of a contraction simulation, as a
generated lower position on the exact quantifier-frontier branch. -/
def outerPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    (position : G2nnfExchangeBodyContractionPosition redex body) :
    G2nnfExchangeBodyLowerPosition redex
      (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice position.outputContexts.1 position.outputContexts.2)
      (.instantiated position.outputContexts.1 position.outputContexts.2) body :=
  match position with
  | .hereOne Gamma Delta hPrem hSC sub body originalGamma originalDelta originalPosition =>
    .hereOne (.instantiated Gamma Delta)
      (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
        redex.lowerApplication.choice Gamma Delta) hPrem hSC sub body
      originalPosition.quantifierPosition
  | .hereTwoLeft Gamma Delta hPrem hSC
      sub1 sub2 body1 body2 originalGamma originalDelta originalPosition =>
    .hereTwoLeft (.instantiated Gamma Delta)
      (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
        redex.lowerApplication.choice Gamma Delta) hPrem hSC
      sub1 sub2 body1 body2 originalPosition.quantifierPosition
  | .hereTwoRight Gamma Delta hPrem hSC
      sub1 sub2 body1 body2 originalGamma originalDelta originalPosition =>
    .hereTwoRight (.instantiated Gamma Delta)
      (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule
        redex.lowerApplication.choice Gamma Delta) hPrem hSC
      sub1 sub2 body1 body2 originalPosition.quantifierPosition
  | .underLowerOne outerLineage hAdmit hPrem hSC
      sub body position =>
    .underLowerOne outerLineage hAdmit hPrem hSC
      sub body position.outerPosition
  | .underLowerTwoLeft outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    .underLowerTwoLeft outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position.outerPosition
  | .underLowerTwoRight outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    .underLowerTwoRight outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position.outerPosition
  | .underWeakening allowed hAdmit hPrem hSC sub body position =>
    .underWeakening allowed hAdmit hPrem hSC
      sub body position.outerPosition

end G2nnfExchangeBodyContractionPosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeCasePosition

/-- Output contexts selected by the actual direct or contraction witness. -/
def outputContexts {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  match position with
  | .directContext _ _ Gamma Delta _ => (Gamma, Delta)
  | .directFocused _ _ _ Gamma Delta _ => (Gamma, Delta)
  | .withContraction _ _ _ _ position => position.outputContexts

/-- The one required lower descendant exported by every case.  In a
contraction case this is the outer instantiated node; the nested original node
remains available from the same case-position witness. -/
def targetLowerPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) :
    G2nnfExchangeBodyLowerPosition redex
      (role.requiredLowerRule redex.quantifierRule redex.lowerRule redex.lowerScope
        redex.lowerApplication.choice position.outputContexts.1 position.outputContexts.2)
      (role.requiredLowerLineage redex position.outputContexts.1 position.outputContexts.2) body :=
  match position with
  | .directContext _ _ Gamma Delta position => position
  | .directFocused _ _ _ Gamma Delta position => position
  | .withContraction _ _ _ _ position => position.outerPosition

end G2nnfExchangeCasePosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeBodyLowerPosition

/-- Compute the exact located application selected by a generated lower
position. -/
def located {L : Language} {hL : L.withoutEquality}
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
    G2nnfGeneratedLowerApplication redex targetRule lineage tree :=
  match position with
  | .hereOne lineage hAdmit hPrem hSC sub body
      quantifierPosition =>
    let exactFrontier := quantifierPosition.located
    { Γ := (targetRule.conclusion).1
      Δ := (targetRule.conclusion).2
      node := .onePremise targetRule hAdmit hPrem hSC sub
      application := .one hAdmit hPrem hSC sub
      path := .root
        (.onePremise targetRule hAdmit hPrem hSC sub)
      Γfrontier := exactFrontier.Γ
      Δfrontier := exactFrontier.Δ
      quantifierFrontier := exactFrontier.tree
      exactQuantifierFrontier := exactFrontier.frontier
      pathToQuantifierFrontier :=
        .onePremise targetRule hAdmit hPrem hSC
          sub exactFrontier.path }
  | .hereTwoLeft lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition =>
    let exactFrontier := quantifierPosition.located
    { Γ := (targetRule.conclusion).1
      Δ := (targetRule.conclusion).2
      node := .twoPremise targetRule hAdmit hPrem hSC sub1 sub2
      application := .two hAdmit hPrem hSC sub1 sub2
      path := .root
        (.twoPremise targetRule hAdmit hPrem hSC sub1 sub2)
      Γfrontier := exactFrontier.Γ
      Δfrontier := exactFrontier.Δ
      quantifierFrontier := exactFrontier.tree
      exactQuantifierFrontier := exactFrontier.frontier
      pathToQuantifierFrontier :=
        .leftPremise targetRule hAdmit hPrem hSC
          sub1 sub2 exactFrontier.path }
  | .hereTwoRight lineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 quantifierPosition =>
    let exactFrontier := quantifierPosition.located
    { Γ := (targetRule.conclusion).1
      Δ := (targetRule.conclusion).2
      node := .twoPremise targetRule hAdmit hPrem hSC sub1 sub2
      application := .two hAdmit hPrem hSC sub1 sub2
      path := .root
        (.twoPremise targetRule hAdmit hPrem hSC sub1 sub2)
      Γfrontier := exactFrontier.Γ
      Δfrontier := exactFrontier.Δ
      quantifierFrontier := exactFrontier.tree
      exactQuantifierFrontier := exactFrontier.frontier
      pathToQuantifierFrontier :=
        .rightPremise targetRule hAdmit hPrem hSC
          sub1 sub2 exactFrontier.path }
  | .underLowerOne outerLineage hAdmit hPrem hSC sub body position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      node := inner.node
      application := inner.application
      path := .onePremise _ hAdmit hPrem hSC sub inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .underLowerTwoLeft outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      node := inner.node
      application := inner.application
      path := .leftPremise _ hAdmit hPrem hSC
        sub1 sub2 inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .underLowerTwoRight outerLineage hAdmit hPrem hSC
      sub1 sub2 body1 body2 position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      node := inner.node
      application := inner.application
      path := .rightPremise _ hAdmit hPrem hSC
        sub1 sub2 inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .underWeakening allowed hAdmit hPrem hSC sub body position =>
    let inner := position.located
    { Γ := inner.Γ
      Δ := inner.Δ
      node := inner.node
      application := inner.application
      path := .onePremise _ hAdmit hPrem hSC sub inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathToQuantifierFrontier := inner.pathToQuantifierFrontier }

end G2nnfExchangeBodyLowerPosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeBodyContractionPosition

/-- Compute both strictly nested lower applications and their path to the
exact quantifier frontier from one contraction-position witness. -/
def located {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    (position : G2nnfExchangeBodyContractionPosition redex body) :
    G2nnfGeneratedContractionSimulation redex tree :=
  match position with
  | .hereOne Gamma Delta hPrem hSC sub body
      originalGamma originalDelta originalPosition =>
    let whole : G2nnfExchangeBodyContractionPosition redex
        (.lowerOne (.instantiated Gamma Delta) (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta)
          hPrem hSC sub body) :=
      .hereOne Gamma Delta hPrem hSC sub body
        originalGamma originalDelta originalPosition
    let outer := whole.outerPosition.located
    let inner := originalPosition.located
    { outerGamma := Gamma
      outerDelta := Delta
      outer := outer
      Γinner := inner.Γ
      Δinner := inner.Δ
      innerNode := inner.node
      innerGamma := originalGamma
      innerDelta := originalDelta
      innerApplication := inner.application
      pathFromOuterToInner :=
        .onePremise _ (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta) hPrem hSC sub inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .hereTwoLeft Gamma Delta hPrem hSC sub1 sub2 body1 body2
      originalGamma originalDelta originalPosition =>
    let whole : G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo (.instantiated Gamma Delta) (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta)
          hPrem hSC sub1 sub2 body1 body2) :=
      .hereTwoLeft Gamma Delta hPrem hSC sub1 sub2 body1 body2
        originalGamma originalDelta originalPosition
    let outer := whole.outerPosition.located
    let inner := originalPosition.located
    { outerGamma := Gamma
      outerDelta := Delta
      outer := outer
      Γinner := inner.Γ
      Δinner := inner.Δ
      innerNode := inner.node
      innerGamma := originalGamma
      innerDelta := originalDelta
      innerApplication := inner.application
      pathFromOuterToInner :=
        .leftPremise _ (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta) hPrem hSC sub1 sub2 inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .hereTwoRight Gamma Delta hPrem hSC sub1 sub2 body1 body2
      originalGamma originalDelta originalPosition =>
    let whole : G2nnfExchangeBodyContractionPosition redex
        (.lowerTwo (.instantiated Gamma Delta) (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta)
          hPrem hSC sub1 sub2 body1 body2) :=
      .hereTwoRight Gamma Delta hPrem hSC sub1 sub2 body1 body2
        originalGamma originalDelta originalPosition
    let outer := whole.outerPosition.located
    let inner := originalPosition.located
    { outerGamma := Gamma
      outerDelta := Delta
      outer := outer
      Γinner := inner.Γ
      Δinner := inner.Δ
      innerNode := inner.node
      innerGamma := originalGamma
      innerDelta := originalDelta
      innerApplication := inner.application
      pathFromOuterToInner :=
        .rightPremise _ (instantiatedLower_bare redex.lowerRule redex.lowerScope redex.quantifierRule redex.lowerApplication.choice Gamma Delta) hPrem hSC sub1 sub2 inner.path
      Γfrontier := inner.Γfrontier
      Δfrontier := inner.Δfrontier
      quantifierFrontier := inner.quantifierFrontier
      exactQuantifierFrontier := inner.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := inner.pathToQuantifierFrontier }
  | .underLowerOne outerLineage hAdmit hPrem hSC sub body position =>
    let nested := position.located
    let outer : G2nnfGeneratedLowerApplication redex
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice nested.outerGamma nested.outerDelta)
        (.instantiated nested.outerGamma nested.outerDelta)
        (.onePremise _ hAdmit hPrem hSC sub) :=
      { Γ := nested.outer.Γ
        Δ := nested.outer.Δ
        node := nested.outer.node
        application := nested.outer.application
        path := .onePremise _ hAdmit hPrem hSC sub nested.outer.path
        Γfrontier := nested.outer.Γfrontier
        Δfrontier := nested.outer.Δfrontier
        quantifierFrontier := nested.outer.quantifierFrontier
        exactQuantifierFrontier := nested.outer.exactQuantifierFrontier
        pathToQuantifierFrontier := nested.outer.pathToQuantifierFrontier }
    { outerGamma := nested.outerGamma
      outerDelta := nested.outerDelta
      outer := outer
      Γinner := nested.Γinner
      Δinner := nested.Δinner
      innerNode := nested.innerNode
      innerGamma := nested.innerGamma
      innerDelta := nested.innerDelta
      innerApplication := nested.innerApplication
      pathFromOuterToInner := nested.pathFromOuterToInner
      Γfrontier := nested.Γfrontier
      Δfrontier := nested.Δfrontier
      quantifierFrontier := nested.quantifierFrontier
      exactQuantifierFrontier := nested.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := nested.pathFromInnerToQuantifierFrontier }
  | .underLowerTwoLeft outerLineage hAdmit hPrem hSC sub1 sub2 body1 body2 position =>
    let nested := position.located
    let outer : G2nnfGeneratedLowerApplication redex
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice nested.outerGamma nested.outerDelta)
        (.instantiated nested.outerGamma nested.outerDelta)
        (.twoPremise _ hAdmit hPrem hSC sub1 sub2) :=
      { Γ := nested.outer.Γ
        Δ := nested.outer.Δ
        node := nested.outer.node
        application := nested.outer.application
        path := .leftPremise _ hAdmit hPrem hSC sub1 sub2 nested.outer.path
        Γfrontier := nested.outer.Γfrontier
        Δfrontier := nested.outer.Δfrontier
        quantifierFrontier := nested.outer.quantifierFrontier
        exactQuantifierFrontier := nested.outer.exactQuantifierFrontier
        pathToQuantifierFrontier := nested.outer.pathToQuantifierFrontier }
    { outerGamma := nested.outerGamma
      outerDelta := nested.outerDelta
      outer := outer
      Γinner := nested.Γinner
      Δinner := nested.Δinner
      innerNode := nested.innerNode
      innerGamma := nested.innerGamma
      innerDelta := nested.innerDelta
      innerApplication := nested.innerApplication
      pathFromOuterToInner := nested.pathFromOuterToInner
      Γfrontier := nested.Γfrontier
      Δfrontier := nested.Δfrontier
      quantifierFrontier := nested.quantifierFrontier
      exactQuantifierFrontier := nested.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := nested.pathFromInnerToQuantifierFrontier }
  | .underLowerTwoRight outerLineage hAdmit hPrem hSC sub1 sub2 body1 body2 position =>
    let nested := position.located
    let outer : G2nnfGeneratedLowerApplication redex
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice nested.outerGamma nested.outerDelta)
        (.instantiated nested.outerGamma nested.outerDelta)
        (.twoPremise _ hAdmit hPrem hSC sub1 sub2) :=
      { Γ := nested.outer.Γ
        Δ := nested.outer.Δ
        node := nested.outer.node
        application := nested.outer.application
        path := .rightPremise _ hAdmit hPrem hSC sub1 sub2 nested.outer.path
        Γfrontier := nested.outer.Γfrontier
        Δfrontier := nested.outer.Δfrontier
        quantifierFrontier := nested.outer.quantifierFrontier
        exactQuantifierFrontier := nested.outer.exactQuantifierFrontier
        pathToQuantifierFrontier := nested.outer.pathToQuantifierFrontier }
    { outerGamma := nested.outerGamma
      outerDelta := nested.outerDelta
      outer := outer
      Γinner := nested.Γinner
      Δinner := nested.Δinner
      innerNode := nested.innerNode
      innerGamma := nested.innerGamma
      innerDelta := nested.innerDelta
      innerApplication := nested.innerApplication
      pathFromOuterToInner := nested.pathFromOuterToInner
      Γfrontier := nested.Γfrontier
      Δfrontier := nested.Δfrontier
      quantifierFrontier := nested.quantifierFrontier
      exactQuantifierFrontier := nested.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := nested.pathFromInnerToQuantifierFrontier }
  | .underWeakening allowed hAdmit hPrem hSC sub body position =>
    let nested := position.located
    let outer : G2nnfGeneratedLowerApplication redex
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice nested.outerGamma nested.outerDelta)
        (.instantiated nested.outerGamma nested.outerDelta)
        (.onePremise _ hAdmit hPrem hSC sub) :=
      { Γ := nested.outer.Γ
        Δ := nested.outer.Δ
        node := nested.outer.node
        application := nested.outer.application
        path := .onePremise _ hAdmit hPrem hSC sub nested.outer.path
        Γfrontier := nested.outer.Γfrontier
        Δfrontier := nested.outer.Δfrontier
        quantifierFrontier := nested.outer.quantifierFrontier
        exactQuantifierFrontier := nested.outer.exactQuantifierFrontier
        pathToQuantifierFrontier := nested.outer.pathToQuantifierFrontier }
    { outerGamma := nested.outerGamma
      outerDelta := nested.outerDelta
      outer := outer
      Γinner := nested.Γinner
      Δinner := nested.Δinner
      innerNode := nested.innerNode
      innerGamma := nested.innerGamma
      innerDelta := nested.innerDelta
      innerApplication := nested.innerApplication
      pathFromOuterToInner := nested.pathFromOuterToInner
      Γfrontier := nested.Γfrontier
      Δfrontier := nested.Δfrontier
      quantifierFrontier := nested.quantifierFrontier
      exactQuantifierFrontier := nested.exactQuantifierFrontier
      pathFromInnerToQuantifierFrontier := nested.pathFromInnerToQuantifierFrontier }

end G2nnfExchangeBodyContractionPosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeCasePosition

/-- Exact multiplicity of the reused non-selected source frontier.  A direct
exchange retains one copy for each source other premise.  The contraction
simulation contains two lower applications, so it retains two copies.  The
case is eliminated from the structural simulation witness itself; no caller
can supply an unrelated multiplier or count. -/
def expectedOtherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) : Nat :=
  match position with
  | .directContext _ _ _ _ _ =>
    redex.lowerApplication.otherPremiseCount
  | .directFocused _ _ _ _ _ _ =>
    redex.lowerApplication.otherPremiseCount
  | .withContraction _ _ _ _ _ =>
    2 * redex.lowerApplication.otherPremiseCount

/-- Result type computed from the exact case-position witness.  Indexing by
the witness itself avoids asking opaque structure projections to reduce a
separate principal-case match. -/
def contractionSimulationResult {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) : Type :=
  match position with
  | .directContext _ _ _ _ _ => Unit
  | .directFocused _ _ _ _ _ _ => Unit
  | .withContraction _ _ _ _ _ =>
    G2nnfGeneratedContractionSimulation redex tree

/-- Mandatory nested simulation evidence in the contraction case; direct
cases carry no second lower application. -/
def contractionSimulation {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) :
    position.contractionSimulationResult :=
  match position with
  | .directContext _ _ _ _ _ => ()
  | .directFocused _ _ _ _ _ _ => ()
  | .withContraction _ _ _ _ position => position.located

end G2nnfExchangeCasePosition
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeBody

/-- Number of exact source quantifier-premise frontier occurrences. -/
def quantifierFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → Nat
  | .quantifierFrontier _ => 1
  | .otherFrontier _ => 0
  | .lowerOne _ _ _ _ _ body => body.quantifierFrontierCount
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    body1.quantifierFrontierCount + body2.quantifierFrontierCount
  | .weakening _ _ _ _ _ body => body.quantifierFrontierCount

/-- Number of exact non-selected lower-premise frontier occurrences. -/
def otherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → Nat
  | .quantifierFrontier _ => 0
  | .otherFrontier _ => 1
  | .lowerOne _ _ _ _ _ body => body.otherFrontierCount
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    body1.otherFrontierCount + body2.otherFrontierCount
  | .weakening _ _ _ _ _ body => body.otherFrontierCount

/-- For every branch ending at the source quantifier premise, count the
propositional/weakening (`b`) nodes below the moved quantifier. -/
def quantifierBranchLengths {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → List Nat
  | .quantifierFrontier _ => [0]
  | .otherFrontier _ => []
  | .lowerOne _ _ _ _ _ body =>
    body.quantifierBranchLengths.map Nat.succ
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    (body1.quantifierBranchLengths ++
      body2.quantifierBranchLengths).map Nat.succ
  | .weakening _ _ _ _ _ body =>
    body.quantifierBranchLengths.map Nat.succ

/-- Count admitted `b` nodes on every branch ending at either exact source
frontier.  This prevents an unbounded auxiliary branch from hiding beside the
selected quantifier branch. -/
def allBranchLengths {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → List Nat
  | .quantifierFrontier _ => [0]
  | .otherFrontier _ => [0]
  | .lowerOne _ _ _ _ _ body =>
    body.allBranchLengths.map Nat.succ
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    (body1.allBranchLengths ++ body2.allBranchLengths).map Nat.succ
  | .weakening _ _ _ _ _ body =>
    body.allBranchLengths.map Nat.succ

end G2nnfExchangeBody
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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

/-- The exact textbook principal subcase retained by a redex. -/
inductive G2nnfPrincipalCaseKind where
  | direct
  | withContraction
deriving DecidableEq

end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfQuantifierPrincipalCase

/-- Forget proof fields while retaining the direct/contraction distinction. -/
def kind {L : Language}
    {side : G2nnfSequentSide} {A : FormulaN L}
    {quantGamma quantDelta lowerGamma lowerDelta :
      LCS.Finset (FormulaN L)} :
    G2nnfQuantifierPrincipalCase side A
      quantGamma quantDelta lowerGamma lowerDelta →
      G2nnfPrincipalCaseKind
  | .direct _ => .direct
  | .withContraction _ _ => .withContraction

end G2nnfQuantifierPrincipalCase
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfPrincipalCaseKind

/-- A direct exchange has at least one residual `b` node; the simulated
contraction case has at least two.  Both retain the global upper bound three. -/
def minimumBranchLength : G2nnfPrincipalCaseKind → Nat
  | .direct => 1
  | .withContraction => 2

end G2nnfPrincipalCaseKind
end LCS.Herbrand.NNFHauptsatz.Theorem
end

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

/-- A bounded, exact local replacement for one adjacent occurrence.

The target is an exact reprincipalized quantifier application whose premise
is generated by `G2nnfExchangeBody`.  Frontier counts enforce exact source
reuse with case-indexed contraction multiplicity, and the branch bound records
precisely the textbook
`ba ↦ ab | abb | abbb` effect.  The located lower descendant supplies the
exact target occurrence used by the order certificate. -/
structure G2nnfExchangeKernel {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (replacement : G2nnfProofTree hL Γ Δ) where
  targetPrincipal : FormulaN L
  principalCorrespondence :
    G2nnfExchangePrincipalCorrespondence
      redex.quantifierRule redex.lowerRule
      redex.lowerApplication.choice redex.principalOccurrence
      targetPrincipal
  Γbody : LCS.Finset (FormulaN L)
  Δbody : LCS.Finset (FormulaN L)
  body : G2nnfProofTree hL Γbody Δbody
  quantifierGamma : LCS.Finset (FormulaN L)
  quantifierDelta : LCS.Finset (FormulaN L)
  quantifierApplication :
    G2nnfOnePremiseApplication
      (principalCorrespondence.reprincipalizedRule quantifierGamma quantifierDelta) replacement
  quantifierPremise :
    G2nnfOnePremiseFrontier quantifierApplication body
  bodyShape : G2nnfExchangeBody redex body
  simulationPosition :
    G2nnfExchangeCasePosition redex bodyShape
      redex.principalOccurrence redex.principalCase
  quantifierFrontierLinear :
    bodyShape.quantifierFrontierCount = 1
  otherFrontierMultiplicity :
    bodyShape.otherFrontierCount =
      simulationPosition.expectedOtherFrontierCount
  quantifierBranchBound :
    ∀ n : Nat, n ∈ bodyShape.quantifierBranchLengths →
      redex.principalCase.kind.minimumBranchLength ≤ n
  allBranchBound :
    ∀ n : Nat, n ∈ bodyShape.allBranchLengths → n ≤ 3

end LCS.Herbrand.NNFHauptsatz.Theorem
end

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
namespace G2nnfExchangeKernel

/-- Case-indexed expected multiplicity exported from the exact simulation
position retained by the kernel. -/
def expectedOtherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {replacement : G2nnfProofTree hL Γ Δ}
    (kernel : G2nnfExchangeKernel redex replacement) : Nat :=
  kernel.simulationPosition.expectedOtherFrontierCount

end G2nnfExchangeKernel
end LCS.Herbrand.NNFHauptsatz.Theorem
end

