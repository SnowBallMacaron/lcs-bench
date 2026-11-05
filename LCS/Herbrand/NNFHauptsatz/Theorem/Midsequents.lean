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
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents.ProofsStamp

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The target lower application is computed from the grammar-generated
position and therefore cannot lie inside a reused frontier. -/
def targetLowerOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {replacement : G2nnfProofTree hL Γ Δ}
    (kernel : G2nnfExchangeKernel redex replacement) :
    G2nnfGeneratedLowerApplication redex
      (redex.requiredLowerRule kernel.simulationPosition.outputContexts.1
        kernel.simulationPosition.outputContexts.2)
      (redex.requiredLowerLineage kernel.simulationPosition.outputContexts.1
        kernel.simulationPosition.outputContexts.2) kernel.body :=
  kernel.simulationPosition.targetLowerPosition.located

end G2nnfExchangeKernel
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
namespace G2nnfPermutableOccurrence

/-- The exact lower application occurrence selected by a redex. -/
@[blueprint "chap7__lemma_7_4_2"]
def lowerOccurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    G2nnfLocatedRuleApplication T R₂ :=
  redex.lowerApplication.applicationOccurrence

end G2nnfPermutableOccurrence
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

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Ambient result of one bounded local exchange.  The constructor output is
definitionally the exact lower-node replacement replugged through the source
path; no output tree or conclusion equality can be pasted in independently.
The preservation implications are proof obligations tied to that exact
structural edit and are exposed for the case proof in Step 3. -/
inductive G2nnfLocalExchangeAt {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    G2nnfProofTree hL Γroot Δroot → Type where
  | rebuild
      (adjacent : G2nnfRootPath redex.pathFromSelectedPremise)
      (replacement : G2nnfProofTree hL
        redex.lowerOccurrence.Γ redex.lowerOccurrence.Δ)
      (kernel : G2nnfExchangeKernel redex replacement)
      (preservesCutFree :
        T.isCutFree →
          (redex.lowerOccurrence.path.replace replacement).isCutFree)
      (preservesPure :
        T.isCutFree → IsPureVariableProofG2nnf T →
          IsPureVariableProofG2nnf
            (redex.lowerOccurrence.path.replace replacement)) :
      G2nnfLocalExchangeAt redex
        (redex.lowerOccurrence.path.replace replacement)

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The generated target lower application exported by the order
certificate. -/
def targetLowerOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    G2nnfGeneratedLowerApplication redex
      (redex.requiredLowerRule certificate.simulationPosition.outputContexts.1
        certificate.simulationPosition.outputContexts.2)
      (redex.requiredLowerLineage certificate.simulationPosition.outputContexts.1
        certificate.simulationPosition.outputContexts.2) certificate.quantifierPremise :=
  certificate.simulationPosition.targetLowerPosition.located

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- In the contraction case, expose the strictly nested original/instantiated
lower applications and their common exact-frontier branch. -/
def contractionSimulation {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    certificate.simulationPosition.contractionSimulationResult :=
  certificate.simulationPosition.contractionSimulation

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact relative path from the moved quantifier premise to the generated
lower node. -/
def lowerPathFromQuantifierPremise {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    RootToNodePath certificate.quantifierPremise
      certificate.targetLowerOccurrence.node :=
  certificate.targetLowerOccurrence.path

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The generated lower node is an ancestor of the exact reused source
quantifier frontier on the same body branch. -/
def sourceFrontierPathFromLower {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    RootToNodePath certificate.targetLowerOccurrence.node
      certificate.targetLowerOccurrence.quantifierFrontier :=
  certificate.targetLowerOccurrence.pathToQuantifierFrontier





end G2nnfLocalExchangeOrderCertificate
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
namespace G2nnfLocalExchangeAt









end G2nnfLocalExchangeAt
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
-- Theorem 7.4.1 (helper): AllRulesPropOrWeakening
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Predicate asserting that every rule applied in a G2nnf proof tree is either propositional or a weakening (not a quantifier rule). Used for the upper part of the midsequent splitting. -/
@[blueprint "chap7__theorem_7_4_1"]
def AllRulesPropOrWeakening {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    (rule.isPropositionalRule ∨ rule.isWeakening) ∧
    AllRulesPropOrWeakening (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (rule.isPropositionalRule ∨ rule.isWeakening) ∧
    AllRulesPropOrWeakening (hL := hL) sub1 ∧
    AllRulesPropOrWeakening (hL := hL) sub2

-- ===================================================================
-- Theorem 7.4.1 (helper): AllRulesQuantifier
-- ===================================================================



-- ===================================================================
-- Theorem 7.4.1 (helper): occurrence-indexed lower paths
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Every inference strictly below the
target occurrence selected by `path` is a quantifier-for-subformulae
inference.  The target node's own inference belongs to the upper subtree and
is therefore not inspected here. -/
@[blueprint "chap7__theorem_7_4_1"]
def AllRulesQuantifierOnPath {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath
  | .leftPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath
  | .rightPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A quantifier-only path from an empty-succedent root reaches a node with
empty succedent.  Left quantifier rules preserve the succedent, while right
quantifier rules cannot have an empty conclusion succedent. -/
theorem _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree.succedent_eq_empty_of_quantifierPath
    {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hRoot : Δroot = LCS.Finset.empty) :
    Δnode = LCS.Finset.empty := by
  induction path with
  | root _ =>
    exact hRoot
  | onePremise rule hAdmit hPrem hSC sub path ih =>
    rcases hQuantifier with ⟨hRule, hPath⟩
    cases rule <;>
      simp only [G2nnfRuleCore.isQuantifierRule] at hRule
    · exact ih hPath hRoot
    · rename_i A occurrence x B y hSelected Gamma Delta
      change LCS.Finset.insert A Delta = LCS.Finset.empty at hRoot
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRoot] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
    · exact ih hPath hRoot
    · rename_i A occurrence x B t hSelected Gamma Delta
      change LCS.Finset.insert A Delta = LCS.Finset.empty at hRoot
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRoot] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule, G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule, G2nnfRuleCore.premises] at hRule hPrem

/-- A prenex formula whose quantifier prefix is entirely universal.  This
Chapter-7 predicate avoids importing the Chapter-8 clause-form API. -/
@[blueprint "chap7__theorem_7_6_1"]
def UniversalPrenexFormula {L : Language} (A : FormulaN L) : Prop :=
  isPrenex A ∧
  ∀ p, p ∈ prenexPrefix A →
    p.1 = QuantifierKind.universal

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- The selected lower path consists only of universal-left
quantifier-for-subformulae steps. -/
def AllRulesAllSubLeftOnPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    match rule with
    | .allSubLeft _ _ _ _ _ _ _ _ =>
      AllRulesAllSubLeftOnPath subpath
    | _ => False
  | .leftPremise _ _ _ _ _ _ _ => False
  | .rightPremise _ _ _ _ _ _ _ => False

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves quantifier-freeness. -/
theorem qf_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree (formulaSubstN A t x) := by
  induction A <;>
    simp_all [formulaSubstN,
      FirstOrder.SemanticsN.isQuantifierFree]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution does not change a prenex formula's quantifier prefix. -/
theorem prenexPrefix_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    prenexPrefix (formulaSubstN A t x) = prenexPrefix A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ _ _ => rfl
  | disj _ _ _ _ => rfl
  | impl _ _ _ _ => rfl
  | all y A ih =>
    by_cases hxy : x = y <;>
      simp [formulaSubstN, hxy, prenexPrefix, ih]
  | ex y A ih =>
    by_cases hxy : x = y <;>
      simp [formulaSubstN, hxy, prenexPrefix, ih]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves prenex form. -/
theorem isPrenex_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hPrenex : isPrenex A) :
    isPrenex (formulaSubstN A t x) := by
  cases A with
  | all y A =>
    change isPrenex A at hPrenex
    by_cases hxy : x = y
    · simpa [formulaSubstN, hxy, isPrenex] using hPrenex
    · simpa [formulaSubstN, hxy, isPrenex] using
        isPrenex_formulaSubstN A t x hPrenex
  | ex y A =>
    change isPrenex A at hPrenex
    by_cases hxy : x = y
    · simpa [formulaSubstN, hxy, isPrenex] using hPrenex
    · simpa [formulaSubstN, hxy, isPrenex] using
        isPrenex_formulaSubstN A t x hPrenex
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact qf_formulaSubstN _ _ _ hPrenex

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A quantifier-free formula has no maximal quantified subformula. -/
theorem not_mem_maxQuantSubformulae_of_qf {L : Language}
    (A C : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    ¬ Membership.mem (maxQuantSubformulaeCore A) C := by
  induction A with
  | predN _ _ | eq_ _ _ _ | neg _ _ | impl _ _ _ _ =>
    exact id
  | conj A B ihA ihB | disj A B ihA ihB =>
    intro hMem
    rcases hMem with hMem | hMem
    · exact ihA hQF.1 hMem
    · exact ihB hQF.2 hMem
  | all _ _ | ex _ _ =>
    exact hQF.elim

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A maximal quantified subformula of a prenex formula is the whole
formula. -/
theorem eq_of_mem_maxQuantSubformulae_of_isPrenex {L : Language}
    (A C : FormulaN L)
    (hPrenex : isPrenex A)
    (hMem : Membership.mem (maxQuantSubformulaeCore A) C) :
    C = A := by
  cases A with
  | all _ _ => exact hMem
  | ex _ _ => exact hMem
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact (not_mem_maxQuantSubformulae_of_qf _ _ hPrenex hMem).elim

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves the universal-prenex invariant. -/
theorem universalPrenexFormula_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hUniversal : UniversalPrenexFormula A) :
    UniversalPrenexFormula (formulaSubstN A t x) := by
  refine ⟨isPrenex_formulaSubstN A t x hUniversal.1, ?_⟩
  intro p hp
  apply hUniversal.2 p
  rw [← prenexPrefix_formulaSubstN A t x]
  exact hp

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Removing one leading universal quantifier preserves the
universal-prenex invariant. -/
theorem universalPrenexFormula_body_of_all {L : Language}
    (B : FormulaN L) (x : Nat)
    (hUniversal :
      UniversalPrenexFormula (FormulaN.all x B)) :
    UniversalPrenexFormula B := by
  refine ⟨hUniversal.1, ?_⟩
  intro p hp
  exact hUniversal.2 p (List.mem_cons.mpr (Or.inr hp))

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- The principal premise formula of a universal-left
quantifier-for-subformulae step remains universal-prenex. -/
theorem universalPrenexFormula_allSubLeft_premise
    {L : Language} [DecidableEq (FormulaN L)]
    (A B : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hUniversal : UniversalPrenexFormula A)
    (hSelected : occurrence.selected = FormulaN.all x B) :
    UniversalPrenexFormula
      (occurrence.replace (formulaSubstN B t x)) := by
  have hSelectedA :=
    eq_of_mem_maxQuantSubformulae_of_isPrenex
      A occurrence.selected hUniversal.1 occurrence.selected_mem
  have hA : A = FormulaN.all x B :=
    hSelectedA.symm.trans hSelected
  subst A
  cases occurrence
  simp only [MaxQuantifierOccurrence.replace]
  exact universalPrenexFormula_formulaSubstN B t x
    (universalPrenexFormula_body_of_all B x hUniversal)

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- An empty-succedent quantifier path starting from a
universal-prenex antecedent can contain only universal-left steps, and
every antecedent formula at its target remains universal-prenex. -/
theorem allSubLeftOnPath_and_universalPrenexAntecedent
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hRootSuccedent : Δroot = LCS.Finset.empty)
    (hRootAntecedent :
      ∀ A, A ∈ Γroot → UniversalPrenexFormula A) :
    AllRulesAllSubLeftOnPath path ∧
    ∀ A, A ∈ Γnode → UniversalPrenexFormula A := by
  induction path with
  | root _ =>
    exact ⟨trivial, hRootAntecedent⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
    rcases hQuantifier with ⟨hRule, hPath⟩
    cases rule <;>
      simp only [G2nnfRuleCore.isQuantifierRule] at hRule
    · rename_i A occurrence x B t hSelected Gamma Delta
      change Delta = LCS.Finset.empty at hRootSuccedent
      change
        (∀ F, F ∈ LCS.Finset.insert A Gamma →
          UniversalPrenexFormula F)
        at hRootAntecedent
      have hUniversalA : UniversalPrenexFormula A :=
        hRootAntecedent A
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hPremiseAntecedent :
          ∀ F,
            F ∈ LCS.Finset.insert
              (occurrence.replace
                (formulaSubstN B t x)) Gamma →
            UniversalPrenexFormula F := by
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with hPrincipal | hRetained
        · subst F
          exact universalPrenexFormula_allSubLeft_premise
            A B occurrence x t hUniversalA hSelected
        · exact hRootAntecedent F
            (LCS.Finset.mem_insert.mpr (Or.inr hRetained))
      exact ih hPath hRootSuccedent hPremiseAntecedent
    · rename_i A occurrence x B y hSelected Gamma Delta
      change LCS.Finset.insert A Delta =
        LCS.Finset.empty at hRootSuccedent
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRootSuccedent] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
    · rename_i A occurrence x B y hSelected Gamma Delta
      change
        (∀ F, F ∈ LCS.Finset.insert A Gamma →
          UniversalPrenexFormula F)
        at hRootAntecedent
      have hUniversalA : UniversalPrenexFormula A :=
        hRootAntecedent A
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hSelectedA : occurrence.selected = A :=
        eq_of_mem_maxQuantSubformulae_of_isPrenex
          A occurrence.selected hUniversalA.1 occurrence.selected_mem
      have hA : A = FormulaN.ex x B :=
        hSelectedA.symm.trans hSelected
      have hExistential :
          (QuantifierKind.existential, x) ∈ prenexPrefix A := by
        rw [hA]
        exact List.Mem.head _
      have hKind :=
        hUniversalA.2 (QuantifierKind.existential, x) hExistential
      cases hKind
    · rename_i A occurrence x B t hSelected Gamma Delta
      change LCS.Finset.insert A Delta =
        LCS.Finset.empty at hRootSuccedent
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRootSuccedent] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule,
        G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule,
        G2nnfRuleCore.premises] at hRule hPrem

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- Specialization of the lower-path invariant to a singleton
universal-prenex antecedent and empty succedent. -/
theorem singletonUniversalPrenex_quantifierPath
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    {Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      (LCS.Finset.singleton source) LCS.Finset.empty}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path) :
    Δnode = LCS.Finset.empty ∧
    AllRulesAllSubLeftOnPath path ∧
    ∀ A, A ∈ Γnode → UniversalPrenexFormula A := by
  have hRootAntecedent :
      ∀ A, A ∈ LCS.Finset.singleton source →
        UniversalPrenexFormula A := by
    intro A hA
    rw [LCS.Finset.mem_singleton] at hA
    subst A
    exact hSource
  have hPath :=
    allSubLeftOnPath_and_universalPrenexAntecedent path
      hQuantifier rfl hRootAntecedent
  exact
    ⟨G2nnfProofTree.succedent_eq_empty_of_quantifierPath
        path hQuantifier rfl,
      hPath⟩



-- ===================================================================
-- Theorem 7.4.1 (companion structure): IsMidsequentG2nnf
-- ===================================================================

/-- Theorem 7.4.1 (companion structure): A sequent `mid` is the midsequent
of `T` when it is quantifier-free and there is one occurrence-identified node
whose upper subtree contains only propositional/weakening inferences and whose
root-to-node path contains only quantifier-for-subformulae inferences.  The
single `NodeOccurrence` witness prevents equal sequents at different nodes
from supplying the upper and lower conditions independently. -/
@[blueprint "chap7__theorem_7_4_1"]
structure IsMidsequentG2nnf {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop where
  /-- Every formula in the midsequent antecedent and succedent is
      quantifier-free -/
  midIsQuantifierFree :
    (∀ A, Membership.mem mid.1 A →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, Membership.mem mid.2 A →
      FirstOrder.SemanticsN.isQuantifierFree A)
  /-- One occurrence supplies the target subtree, its exact position in `T`,
      the upper-rule condition, and the lower-path condition together. -/
  midOccurrence :
    ∃ occurrence : NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening (hL := hL) occurrence.node ∧
      AllRulesQuantifierOnPath occurrence.path



-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A genuine midsequent occurrence below a singleton
universal-prenex antecedent has empty succedent, and the same occurrence
carries the upper-tree and universal-left lower-path invariants. -/
theorem universalPrenexSingleton_midsequentSpecialization
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    {T : G2nnfProofTree hL
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ occurrence : NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening (hL := hL) occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      ∀ A, A ∈ mid.1 → UniversalPrenexFormula A := by
  rcases hMid.midOccurrence with
    ⟨occurrence, hAbove, hQuantifier⟩
  rcases singletonUniversalPrenex_quantifierPath source hSource
      occurrence.path hQuantifier with
    ⟨hSuccedent, hAllSubLeft, hAntecedent⟩
  exact
    ⟨hSuccedent,
      ⟨occurrence, hAbove, hAllSubLeft, hAntecedent⟩⟩



-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExPred
-- ===================================================================

/-- Example 7.4.4 (companion type): Predicate symbols for the NNF sharpened Hauptsatz example: P (unary), Q (unary), R (unary). These predicates are used to construct the sequent (P(a) or forall x(Q(x) or forall y R(y))) -> P(a), Q(a), R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExPred : Type where
  /-- Unary predicate P -/
  | P : NNFHauptExPred
  /-- Unary predicate Q -/
  | Q : NNFHauptExPred
  /-- Unary predicate R -/
  | R : NNFHauptExPred

-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExFunc
-- ===================================================================

/-- Example 7.4.4 (companion type): Function symbols for the NNF sharpened Hauptsatz example: f (unary). The function f is used in the terms f(a) and f(b) appearing in the succedent. -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExFunc : Type where
  /-- Unary function f -/
  | f : NNFHauptExFunc

-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExConst
-- ===================================================================

/-- Example 7.4.4 (companion type): Constant symbols for the NNF sharpened Hauptsatz example: a and b. The constants a and b appear in the ground terms P(a), Q(a), f(a), and f(b). -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExConst : Type where
  /-- Constant a -/
  | a : NNFHauptExConst
  /-- Constant b -/
  | b : NNFHauptExConst

-- ===================================================================
-- Example 7.4.4 (companion def): nnfHauptExLang
-- ===================================================================

/-- Example 7.4.4 (companion def): A language with unary predicates P, Q, R; unary function f; and constants a, b. This language is used to construct the sequent and proof trees for the NNF sharpened Hauptsatz example. -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptExLang : Language where
  hasEquality := false
  funSymbols := NNFHauptExFunc
  funArity := fun | .f => 1
  constSymbols := NNFHauptExConst
  predSymbols := NNFHauptExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 1

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptExVec1
-- ===================================================================

/-- Example 7.4.4 (companion def): Build a Fin 1 -> Term from a single term in nnfHauptExLang. Used to construct unary predicate applications P(t), Q(t), R(t). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptExVec1 (t : Term nnfHauptExLang) :
    Fin 1 → Term nnfHauptExLang
  | ⟨0, _⟩ => t

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptEx_fa
-- ===================================================================

/-- Example 7.4.4 (companion def): The term f(a) used in the succedent
formulae R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_fa : Term nnfHauptExLang :=
  Term.func NNFHauptExFunc.f
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptEx_fb
-- ===================================================================

/-- Example 7.4.4 (companion def): The term f(b) used in the succedent
formula R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_fb : Term nnfHauptExLang :=
  Term.func NNFHauptExFunc.f
    (nnfHauptExVec1 (Term.const NNFHauptExConst.b))

-- ===================================================================
-- Example 7.4.4 (companion def): nnfHauptsatzExSequent
-- ===================================================================

/-- Example 7.4.4 (companion def): The sequent (P(a) or forall x(Q(x) or forall y R(y))) -> P(a), Q(a), R(f(a)) and R(f(b)). Variables: x = 0, y = 1. The antecedent contains a single NNF formula with nested quantifiers. The succedent contains ground formulae: P(a), Q(a), and the conjunction R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptsatzExSequent :
    LCS.FirstOrder.Gentzen.Sequent nnfHauptExLang :=
  let pa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.P
      (nnfHauptExVec1 (Term.const NNFHauptExConst.a))
  let qa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.Q
      (nnfHauptExVec1 (Term.const NNFHauptExConst.a))
  let rfa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 nnfHauptEx_fa)
  let rfb : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 nnfHauptEx_fb)
  -- forall y R(y), y = 1
  let forallYRy : FormulaN nnfHauptExLang :=
    FormulaN.all 1
      (FormulaN.predN NNFHauptExPred.R
        (nnfHauptExVec1 (Term.var 1)))
  -- Q(x) or forall y R(y), x = 0
  let qxOrForallYRy : FormulaN nnfHauptExLang :=
    FormulaN.disj
      (FormulaN.predN NNFHauptExPred.Q
        (nnfHauptExVec1 (Term.var 0)))
      forallYRy
  -- forall x(Q(x) or forall y R(y))
  let forallXBody : FormulaN nnfHauptExLang :=
    FormulaN.all 0 qxOrForallYRy
  -- P(a) or forall x(Q(x) or forall y R(y))
  let antFormula : FormulaN nnfHauptExLang :=
    FormulaN.disj pa forallXBody
  { antecedent := [antFormula]
    succedent := [pa, qa, FormulaN.conj rfa rfb] }

-- ===================================================================
-- Example 7.4.4 (helper): formula abbreviations
-- ===================================================================

/-- Example 7.4.4 (companion abbrev): P(a) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Pa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.P
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

/-- Example 7.4.4 (companion abbrev): Q(a) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Qa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.Q
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

/-- Example 7.4.4 (companion abbrev): R(f(a)) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Rfa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 nnfHauptEx_fa)

/-- Example 7.4.4 (companion abbrev): R(f(b)) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Rfb : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 nnfHauptEx_fb)

/-- Example 7.4.4 (companion abbrev): R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_RfaAndRfb : FormulaN nnfHauptExLang :=
  FormulaN.conj nnfHauptEx_Rfa nnfHauptEx_Rfb

/-- Example 7.4.4 (companion abbrev): forall y R(y) (y = 1). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_forallYRy : FormulaN nnfHauptExLang :=
  FormulaN.all 1
    (FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 (Term.var 1)))

/-- Example 7.4.4 (companion abbrev): Q(x) or forall y R(y) (x = 0). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_QxOrForallYRy :
    FormulaN nnfHauptExLang :=
  FormulaN.disj
    (FormulaN.predN NNFHauptExPred.Q
      (nnfHauptExVec1 (Term.var 0)))
    nnfHauptEx_forallYRy

/-- Example 7.4.4 (companion abbrev): forall x(Q(x) or forall y R(y)) (x=0).
The maximal quantified subformula of the antecedent formula. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_forallXBody : FormulaN nnfHauptExLang :=
  FormulaN.all 0 nnfHauptEx_QxOrForallYRy

/-- Example 7.4.4 (companion abbrev): The antecedent formula
P(a) or forall x(Q(x) or forall y R(y)). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_antFormula : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa nnfHauptEx_forallXBody

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or R(f(a))).
An antecedent formula of the midsequent. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_midAnt1 : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfa)

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or R(f(b))).
An antecedent formula of the midsequent. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_midAnt2 : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfb)

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or forall y R(y)). Intermediate formula after first allSubLeft instantiation (x := a). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_afterFirstInst :
    FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_forallYRy)

-- ===================================================================
-- Example 7.4.4 (companion def): nnfHauptsatzExMidsequent
-- ===================================================================

/-- Example 7.4.4 (companion def): The midsequent P(a) or (Q(a) or R(f(a))), P(a) or (Q(a) or R(f(b))) -> P(a), Q(a), R(f(a)) and R(f(b)). This midsequent is obtained by applying the normalization process of Theorem 7.4.1 to the non-normal proof tree. Every formula in the midsequent is quantifier-free, demonstrating property (1) of Theorem 7.4.1. The midsequent formulae are obtained by instantiating the quantified subformulae of the antecedent formula P(a) or forall x(Q(x) or forall y R(y)) with the ground terms a and f(a) (resp. f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptsatzExMidsequent :
    LCS.FirstOrder.Gentzen.Sequent nnfHauptExLang :=
  let pa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.P
      (nnfHauptExVec1 (Term.const NNFHauptExConst.a))
  let qa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.Q
      (nnfHauptExVec1 (Term.const NNFHauptExConst.a))
  let rfa : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 nnfHauptEx_fa)
  let rfb : FormulaN nnfHauptExLang :=
    FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 nnfHauptEx_fb)
  -- P(a) or (Q(a) or R(f(a)))
  let midAnt1 : FormulaN nnfHauptExLang :=
    FormulaN.disj pa (FormulaN.disj qa rfa)
  -- P(a) or (Q(a) or R(f(b)))
  let midAnt2 : FormulaN nnfHauptExLang :=
    FormulaN.disj pa (FormulaN.disj qa rfb)
  { antecedent := [midAnt1, midAnt2]
    succedent := [pa, qa, FormulaN.conj rfa rfb] }

/-- Example 7.4.4 (final displayed sequent):
`(P(a) ∨ Q(a)) ∨ (R(f(a)) ∧ R(f(b))) → P(a), Q(a), R(f(a)) ∧ R(f(b))`.
The two antecedent formulae of the midsequent combine by distributivity;
the succedent retains its displayed order. -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptsatzExFinalSequent : LCS.FirstOrder.Gentzen.Sequent nnfHauptExLang where
  antecedent := [FormulaN.disj (FormulaN.disj nnfHauptEx_Pa nnfHauptEx_Qa)
    nnfHauptEx_RfaAndRfb]
  succedent := [nnfHauptEx_Pa, nnfHauptEx_Qa, nnfHauptEx_RfaAndRfb]

/-- Example 7.4.4: at each structure and assignment, truth of both
midsequent antecedents is equivalent to truth of the final antecedent.
This is the distributive step in the final displayed equivalence. -/
@[blueprint "chap7__example_7_4_4"]
theorem nnfHauptsatzExFinalAntecedent_equiv
    (M : Structure nnfHauptExLang) (s : Assignment M) :
    (∀ A ∈ nnfHauptsatzExMidsequent.antecedent, formulaEvalN M A s) ↔
      (∀ A ∈ nnfHauptsatzExFinalSequent.antecedent, formulaEvalN M A s) 

/-- Example 7.4.4: the displayed midsequent and final sequent have the same
truth value at every structure and assignment, interpreting a sequent as
truth of all antecedents implying truth of some succedent. -/
@[blueprint "chap7__example_7_4_4"]
theorem nnfHauptsatzExFinalSequent_equiv
    (M : Structure nnfHauptExLang) (s : Assignment M) :
    ((∀ A ∈ nnfHauptsatzExMidsequent.antecedent, formulaEvalN M A s) →
      ∃ B ∈ nnfHauptsatzExMidsequent.succedent, formulaEvalN M B s) ↔
    ((∀ A ∈ nnfHauptsatzExFinalSequent.antecedent, formulaEvalN M A s) →
      ∃ B ∈ nnfHauptsatzExFinalSequent.succedent, formulaEvalN M B s) 

-- ===================================================================
-- Example 7.4.4 (helper): succedent set
-- ===================================================================

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- Example 7.4.4 (companion abbrev): The succedent set {P(a), Q(a),
R(f(a)) and R(f(b))} as a Set (FormulaN nnfHauptExLang). -/
abbrev nnfHauptEx_succSet : Set (FormulaN nnfHauptExLang) :=
  LCS.Herbrand.NNFHauptsatz.sng nnfHauptEx_Pa ∪
    LCS.Herbrand.NNFHauptsatz.sng nnfHauptEx_Qa ∪
    LCS.Herbrand.NNFHauptsatz.sng nnfHauptEx_RfaAndRfb

@[blueprint "chap7__example_7_4_4"]
abbrev NNFHauptExFormula := FormulaN nnfHauptExLang

@[blueprint "chap7__example_7_4_4"]
abbrev NNFHauptExFormulaSet :=
  LCS.Finset NNFHauptExFormula

-- ATTACH-BLOCKER: unsupported untagged abbrev
noncomputable abbrev nnfHauptExDeltaBase : NNFHauptExFormulaSet :=
  LCS.Finset.insert nnfHauptEx_Pa
    (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty)

@[blueprint "chap7__example_7_4_4"]
noncomputable abbrev nnfHauptExDelta : NNFHauptExFormulaSet :=
  LCS.Finset.insert nnfHauptEx_Pa
    (LCS.Finset.insert nnfHauptEx_Qa
      (LCS.Finset.insert nnfHauptEx_RfaAndRfb LCS.Finset.empty))

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev nnfHauptEx_Ry : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 (Term.var 1))

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_forallYOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_forallYRy :=
  .all 1 nnfHauptEx_Ry

@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_forallXOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_forallXBody :=
  .all 0 nnfHauptEx_QxOrForallYRy

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_afterFirstYOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_afterFirstInst :=
  .disjRight nnfHauptEx_Pa
    (.disjRight nnfHauptEx_Qa nnfHauptEx_forallYOccurrence)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_antXOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_antFormula :=
  .disjRight nnfHauptEx_Pa nnfHauptEx_forallXOccurrence

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
noncomputable section

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_PaRectified :
    isRectified nnfHauptEx_Pa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_QaRectified :
    isRectified nnfHauptEx_Qa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfaRectified :
    isRectified nnfHauptEx_Rfa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfbRectified :
    isRectified nnfHauptEx_Rfb :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfaAndRfbRectified :
    isRectified nnfHauptEx_RfaAndRfb :=
  AllRectified.isRectified_of_isQuantifierFree _ ⟨trivial, trivial⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_midAnt1Rectified :
    isRectified nnfHauptEx_midAnt1 :=
  AllRectified.isRectified_of_isQuantifierFree _
    ⟨trivial, ⟨trivial, trivial⟩⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_midAnt2Rectified :
    isRectified nnfHauptEx_midAnt2 :=
  AllRectified.isRectified_of_isQuantifierFree _
    ⟨trivial, ⟨trivial, trivial⟩⟩

end
end LCS.Herbrand.NNFHauptsatz.Theorem
end

