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
import LCS.Herbrand.NNFHauptsatz.Theorem.CutFree
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Theorem.PureVariable
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeKernel
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Permutability.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.Permutability

Lemma 7.4.2: in a pure-variable, cut-free G2nnf proof every quantifier rule can be
permuted with a propositional rule or a weakening.
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

-- ATTACH-BLOCKER: unsupported untagged structure
/-- Exact target occurrences witnessing that the moved quantifier is closer
to the root and a lower-schema descendant occurs inside its exact premise.
The two paths compose without any rule-value equality search. -/
structure G2nnfLocalExchangeOrderCertificate {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) where
  targetPrincipal : FormulaN L
  principalCorrespondence :
    G2nnfExchangePrincipalCorrespondence
      redex.quantifierRule redex.lowerRule
      redex.lowerApplication.choice redex.principalOccurrence
      targetPrincipal
  Γquant : LCS.Finset (FormulaN L)
  Δquant : LCS.Finset (FormulaN L)
  quantifierNode : G2nnfProofTree hL Γquant Δquant
  quantifierGamma : LCS.Finset (FormulaN L)
  quantifierDelta : LCS.Finset (FormulaN L)
  quantifierApplication :
    G2nnfOnePremiseApplication
      (principalCorrespondence.reprincipalizedRule quantifierGamma quantifierDelta) quantifierNode
  quantifierPath : RootToNodePath output quantifierNode
  Γbody : LCS.Finset (FormulaN L)
  Δbody : LCS.Finset (FormulaN L)
  quantifierPremise : G2nnfProofTree hL Γbody Δbody
  quantifierPremiseFrontier :
    G2nnfOnePremiseFrontier quantifierApplication quantifierPremise
  bodyShape : G2nnfExchangeBody redex quantifierPremise
  simulationPosition :
    G2nnfExchangeCasePosition redex bodyShape
      redex.principalOccurrence redex.principalCase
  otherFrontierMultiplicity :
    bodyShape.otherFrontierCount =
      simulationPosition.expectedOtherFrontierCount

namespace G2nnfLocalExchangeOrderCertificate

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Case-indexed expected multiplicity retained by the exported order
certificate. -/
def expectedOtherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) : Nat :=
  certificate.simulationPosition.expectedOtherFrontierCount

end G2nnfLocalExchangeOrderCertificate

-- ===================================================================
-- Lemma 7.4.2 (helper): RuleAppearsBelow
-- ===================================================================

/-- The upper part of a local permutation fragment. Its only leaves are the
exact source quantifier premise and the exact non-selected lower premise.
The indices count quantifier-frontier uses, other-frontier uses, and lower
inferences on paths to the quantifier frontier. Lower-schema copies and
arbitrary legal weakenings are allowed; no other inference is generated. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPermutationBody {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutationRedex T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Nat → Nat → Nat → Type where
  | quantifierFrontier {Γ Δ} {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOnePremiseFrontier redex.quantifierApplication tree) :
      G2nnfPermutationBody redex tree 1 0 0
  | otherFrontier {Γ Δ} {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOtherPremiseFrontier redex.lowerApplication tree) :
      G2nnfPermutationBody redex tree 0 1 0
  | lowerOne {rule : G2nnfRuleCore L} {q o b : Nat}
      (lineage : G2nnfPermutationLowerInstance redex rule)
      (hAdmit : rule.BareAtomicAxiom) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfPermutationBody redex sub q o b) :
      G2nnfPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub)
        q o (b + q)
  | lowerTwo {rule : G2nnfRuleCore L} {q₁ q₂ o₁ o₂ b₁ b₂ : Nat}
      (lineage : G2nnfPermutationLowerInstance redex rule)
      (hAdmit : rule.BareAtomicAxiom) (hPrem : rule.premises.length = 2)
      (hSC : rule.SideConditions)
      (sub₁ : G2nnfProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (sub₂ : G2nnfProofTree hL
        (rule.premises[1]'(by omega)).1 (rule.premises[1]'(by omega)).2)
      (body₁ : G2nnfPermutationBody redex sub₁ q₁ o₁ b₁)
      (body₂ : G2nnfPermutationBody redex sub₂ q₂ o₂ b₂) :
      G2nnfPermutationBody redex (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
        (q₁ + q₂) (o₁ + o₂) (b₁ + b₂ + q₁ + q₂)
  | weakening {rule : G2nnfRuleCore L} {q o b : Nat}
      (hWeak : rule.isWeakening)
      (hAdmit : rule.BareAtomicAxiom) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfPermutationBody redex sub q o b) :
      G2nnfPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub) q o b

/-- A local Q with the source frontiers fixed. Exactly one moved quantifier
lies below all generated lower-schema copies, with only weakenings below it.
At least one lower descendant lies on the path to the source quantifier
premise. The other premise is retained, with duplication permitted. Unlike
an adjacent bounded exchange, Q admits an arbitrary weakening section. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPermutationFragment {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutationRedex T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfProofTree hL Γ Δ → Type where
  | quantifier {Γ Δ Γbody Δbody : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (targetPrincipal : FormulaN L)
      (role : G2nnfPrincipalOccurrenceRole redex.quantifierRule.side
        redex.quantifierRule.principal redex.lowerApplication.rawGamma
        redex.lowerApplication.rawDelta
        (redex.lowerRule.selectedFocus redex.lowerApplication.choice))
      (correspondence : G2nnfExchangePrincipalCorrespondence
        redex.quantifierRule redex.lowerRule redex.lowerApplication.choice
        role targetPrincipal)
      (quantifierGamma quantifierDelta : LCS.Finset (FormulaN L))
      (application : G2nnfOnePremiseApplication
        (correspondence.reprincipalizedRule quantifierGamma quantifierDelta) tree)
      (body : G2nnfProofTree hL Γbody Δbody)
      (premise : G2nnfOnePremiseFrontier application body)
      (otherCount lowerCount : Nat)
      (shape : G2nnfPermutationBody redex body 1 otherCount lowerCount)
      (usesOther : redex.lowerApplication.otherPremiseCount ≤ otherCount)
      (reversesOrder : 0 < lowerCount) :
      G2nnfPermutationFragment redex tree
  | weakening {rule : G2nnfRuleCore L}
      (hWeak : rule.isWeakening)
      (hAdmit : rule.BareAtomicAxiom) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (fragment : G2nnfPermutationFragment redex sub) :
      G2nnfPermutationFragment redex (.onePremise rule hAdmit hPrem hSC sub)

-- ===================================================================
-- Lemma 7.4.2 (required def): CanPermuteWithG2nnf
-- ===================================================================

/-- Lemma 7.4.2 (required def): Each eligible pair of inference occurrences
with a weakening-only intervening path admits a local Q. Its frontier proofs
are the original selected quantifier premise and non-selected lower premise;
its root is the exact lower conclusion. Replugging Q through that occurrence's
path preserves the outside continuation. Q contains the moved quantifier,
copies of the selected lower schema and weakening-only extras, in reversed
order. The lower rule ranges over all rules with premises, including quantifier rules
and cut. Lemma 7.4.2 asserts this relation only for propositional or weakening
lower rules; that theorem does not restrict the definition itself. -/
@[blueprint "chap7__lemma_7_4_2"]
def CanPermuteWithG2nnf {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (R₁ R₂ : G2nnfRule L hL)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) : Prop :=
  ∀ redex : G2nnfPermutationRedex T R₁.val R₂.val,
    ∃ Q : G2nnfProofTree hL redex.lowerOccurrence.Γ redex.lowerOccurrence.Δ,
      Nonempty (G2nnfPermutationFragment redex Q)

-- ===================================================================
-- Lemma 7.4.2: g2nnf_permutability
-- ===================================================================

/-- Lemma 7.4.2: In every pure-variable, cut-free G2nnf proof, each
quantifier inference can be locally permuted with a propositional inference
or weakening. Every eligible occurrence pair has its own boundary-preserving
Q, including focused side-formula cases and weakening-only intermediate
paths. The only extra inferences in Q are weakenings; lower-schema copies
are permitted. -/
@[attach_debt, blueprint "chap7__lemma_7_4_2" (main := true)]
theorem g2nnf_permutability
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfRule L hL)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree)
    (hQuant : R₁.isQuantifierRule)
    (hR₂ : R₂.isPropositionalRule ∨ R₂.isWeakening) :
    CanPermuteWithG2nnf R₁ R₂ T 
end LCS.Herbrand.NNFHauptsatz.Theorem
end
