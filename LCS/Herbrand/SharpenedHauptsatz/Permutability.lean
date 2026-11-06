import LCS.Item
import LCS.Util
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.PrenexForm
import Attach
import LCS.Herbrand.SharpenedHauptsatz.Permutability.ProofsStamp

/-! # Herbrand.SharpenedHauptsatz.Permutability
    Formalization of Chapter 7, Section 3.2: The Permutability Lemma.

    Covers Lemma 7.3.3 (permutability of quantifier rules with
    logical, structural, and cut rules in pure-variable proofs).

    Inference occurrences are tied to addresses in indexed LK and LKₑ
    proof trees. Boundary data retain their actual ordered premise proofs.
    Rule classifiers use the indexed `FOLKStep1` / `FOLKStep2` families.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN

-- ===================================================================
-- Definition 7.3.2 (companion def): FOLKStep1.isStructural /
-- Definition 7.3.2 (companion def): FOLKStep2.isStructural
-- ===================================================================

namespace LCS.CutElim.LK.FOLKStep1

/-- Definition 7.3.2 (companion def): Returns True for structural one-premise rules: weakenLeft, weakenRight, contractLeft, contractRight, exchangeLeft, exchangeRight. Returns False for logical and quantifier one-premise rules. The baseline unified `FOLKRule.isStructural` predicate is split here across the indexed step types; see also `FOLKStep2.isStructural`. -/
@[blueprint "chap7__definition_7_3_2"]
def isStructural {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .weakenLeft _ _ _ => True
  | .weakenRight _ _ _ => True
  | .contractLeft _ _ _ => True
  | .contractRight _ _ _ => True
  | .exchangeLeft _ _ _ _ _ => True
  | .exchangeRight _ _ _ _ _ => True
  | .andLeftL _ _ _ _ => False
  | .andLeftR _ _ _ _ => False
  | .orRightL _ _ _ _ => False
  | .orRightR _ _ _ _ => False
  | .implRight _ _ _ _ => False
  | .negLeft _ _ _ => False
  | .negRight _ _ _ => False
  | .allLeft _ _ _ _ _ _ => False
  | .allRight _ _ _ _ _ _ _ => False
  | .exLeft _ _ _ _ _ _ _ => False
  | .exRight _ _ _ _ _ _ => False

end LCS.CutElim.LK.FOLKStep1

namespace LCS.CutElim.LK.FOLKStep2

/-- Definition 7.3.2 (companion def): No two-premise rule in LK is structural — cut, andRight, orLeft, implLeft are all non-structural. This predicate always returns False. -/
@[blueprint "chap7__definition_7_3_2"]
def isStructural {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | .cut _ _ _ _ _ => False
  | .andRight _ _ _ _ => False
  | .orLeft _ _ _ _ => False
  | .implLeft _ _ _ _ _ _ => False

end LCS.CutElim.LK.FOLKStep2

-- ===================================================================
-- Definition 7.3.2 (companion type): AnyFOLKStep
-- ===================================================================

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability

/-- Definition 7.3.2 (companion type): An existentially-packaged LK rule step. Since the indexed API splits rules across two families (one-premise vs two-premise), the textbook's free-floating "rule" concept is expressed as a sum type wrapping either a `FOLKStep1` or a `FOLKStep2` with their premises/conclusions hidden. This is NOT a unified `FOLKRule` shim: the underlying constructors are the indexed `FOLKStep1 prem conc` / `FOLKStep2 prem1 prem2 conc` types, and the premise/conclusion sequents are recovered from the type indices (not from any placeholder). -/
@[blueprint "chap7__definition_7_3_2"]
inductive AnyFOLKStep (L : Language) : Type where
  /-- One-premise step application wrapper -/
  | one {prem conc : Sequent L} (rule : FOLKStep1 prem conc) :
      AnyFOLKStep L
  /-- Two-premise step application wrapper -/
  | two {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc) :
      AnyFOLKStep L

namespace AnyFOLKStep

/-- Definition 7.3.2 (companion def): Extract the list of premises of an existentially-packaged step. Since the indexed step type captures premises in the type indices, we extract them here. -/
@[blueprint "chap7__definition_7_3_2"]
def premises {L : Language} : AnyFOLKStep L → List (Sequent L)
  | .one (prem := p) _ => [p]
  | .two (prem1 := p1) (prem2 := p2) _ => [p1, p2]

/-- Definition 7.3.2 (companion def): Extract the conclusion of an
    existentially-packaged step from its type index. -/
@[blueprint "chap7__definition_7_3_2"]
def conclusion {L : Language} : AnyFOLKStep L → Sequent L
  | .one (conc := c) _ => c
  | .two (conc := c) _ => c

end AnyFOLKStep

end LCS.Herbrand.SharpenedHauptsatz.Permutability

-- ===================================================================
-- Definition 7.3.2 (companion def): AnyFOLKStep.isOnePremise /
-- isStructural
-- ===================================================================

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep

/-- Definition 7.3.2 (companion def): Structural classification at the `AnyFOLKStep` level, delegating to the step-specific `isStructural` predicates. -/
@[blueprint "chap7__definition_7_3_2"]
def isStructural {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isStructural
  | .two r => r.isStructural

end LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep

-- ===================================================================
-- Path-local helpers for Definition 7.3.2
-- ===================================================================

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability

/-- Definition 7.3.2 (companion): The actual subtree at an address in the fixed proof. Unary and left premises use edge 0; right premises use edge 1. Invalid addresses return none. -/
@[blueprint "chap7__definition_7_3_2"]
def lkSubtreeAt {L : Language} :
    {s : Sequent L} → FOLKProofTree s → List Nat → Option (Σ c : Sequent L, FOLKProofTree c)
  | s, t, [] => some ⟨s, t⟩
  | _, .onePremise _ t, 0 :: p => lkSubtreeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkSubtreeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkSubtreeAt t p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): The indexed inference applied at an actual node. Axiom leaves, including equality leaves in LKₑ, have no one- or two-premise inference. -/
@[blueprint "chap7__definition_7_3_2"]
def lkInferenceAt {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (address : List Nat) : Option (AnyFOLKStep L) :=
  match lkSubtreeAt T address with
  | none => none
  | some ⟨_, t⟩ => match t with
    | .axiom_ _ _ => none
    | .onePremise rule _ => some (.one rule)
    | .twoPremise rule _ _ => some (.two rule)

/-- Definition 7.3.2 (companion): An inference occurrence in a fixed proof, identified by its address. The lookup certificate ties its indexed rule to that node; identical rules at different addresses are distinct occurrences. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKInferenceOccurrence {L : Language} {s : Sequent L} (T : FOLKProofTree s) where
  address : List Nat
  rule : AnyFOLKStep L
  atAddress : lkInferenceAt T address = some rule

/-- Definition 7.3.2 (companion): One-premise boundary at the selected inference: the actual premise proof, its sequent, and the conclusion sequent are tied to the ambient proof by address lookup. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKOnePremiseBoundary {L : Language} {s : Sequent L}
    {T : FOLKProofTree s} (o : LKInferenceOccurrence T) where
  premise : Sequent L
  conclusion : Sequent L
  rule : FOLKStep1 premise conclusion
  tree : FOLKProofTree premise
  atAddress : lkSubtreeAt T o.address = some ⟨conclusion, .onePremise rule tree⟩

/-- Definition 7.3.2 (companion): Two-premise boundary at the selected inference, retaining both actual premise proofs in their left/right order and their indexed sequents. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKTwoPremiseBoundary {L : Language} {s : Sequent L}
    {T : FOLKProofTree s} (o : LKInferenceOccurrence T) where
  leftSequent : Sequent L
  rightSequent : Sequent L
  conclusion : Sequent L
  rule : FOLKStep2 leftSequent rightSequent conclusion
  leftTree : FOLKProofTree leftSequent
  rightTree : FOLKProofTree rightSequent
  atAddress : lkSubtreeAt T o.address =
    some ⟨conclusion, .twoPremise rule leftTree rightTree⟩

/-- Definition 7.3.2 (companion): The actual subtree at an address in the fixed proof. Unary and left premises use edge 0; right premises use edge 1. Invalid addresses return none. -/
@[blueprint "chap7__definition_7_3_2"]
def lkeSubtreeAt {L : Language} :
    {s : Sequent L} → LKeProofTree s → List Nat → Option (Σ c : Sequent L, LKeProofTree c)
  | s, t, [] => some ⟨s, t⟩
  | _, .onePremise _ t, 0 :: p => lkeSubtreeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkeSubtreeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkeSubtreeAt t p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): The indexed inference applied at an actual node. Axiom leaves, including equality leaves in LKₑ, have no one- or two-premise inference. -/
@[blueprint "chap7__definition_7_3_2"]
def lkeInferenceAt {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (address : List Nat) : Option (AnyFOLKStep L) :=
  match lkeSubtreeAt T address with
  | none => none
  | some ⟨_, t⟩ => match t with
    | .axiom_ _ _ => none
    | .eqAxiom _ _ => none
    | .onePremise rule _ => some (.one rule)
    | .twoPremise rule _ _ => some (.two rule)

/-- Definition 7.3.2 (companion): An inference occurrence in a fixed proof, identified by its address. The lookup certificate ties its indexed rule to that node; identical rules at different addresses are distinct occurrences. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKeInferenceOccurrence {L : Language} {s : Sequent L} (T : LKeProofTree s) where
  address : List Nat
  rule : AnyFOLKStep L
  atAddress : lkeInferenceAt T address = some rule

/-- Definition 7.3.2 (companion): One-premise boundary at the selected inference: the actual premise proof, its sequent, and the conclusion sequent are tied to the ambient proof by address lookup. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKeOnePremiseBoundary {L : Language} {s : Sequent L}
    {T : LKeProofTree s} (o : LKeInferenceOccurrence T) where
  premise : Sequent L
  conclusion : Sequent L
  rule : FOLKStep1 premise conclusion
  tree : LKeProofTree premise
  atAddress : lkeSubtreeAt T o.address = some ⟨conclusion, .onePremise rule tree⟩

/-- Definition 7.3.2 (companion): Two-premise boundary at the selected inference, retaining both actual premise proofs in their left/right order and their indexed sequents. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKeTwoPremiseBoundary {L : Language} {s : Sequent L}
    {T : LKeProofTree s} (o : LKeInferenceOccurrence T) where
  leftSequent : Sequent L
  rightSequent : Sequent L
  conclusion : Sequent L
  rule : FOLKStep2 leftSequent rightSequent conclusion
  leftTree : LKeProofTree leftSequent
  rightTree : LKeProofTree rightSequent
  atAddress : lkeSubtreeAt T o.address =
    some ⟨conclusion, .twoPremise rule leftTree rightTree⟩

/-- Definition 7.3.2 (companion): Strict ancestry in the root-to-premise address convention. The upper node lies in a premise subtree of the lower node; the first edge selects that premise. -/
@[blueprint "chap7__definition_7_3_2"]
def premiseAddressDescendant (upper lower : List Nat) : Prop :=
  ∃ edge tail, upper = lower ++ edge :: tail

/-- Definition 7.3.2 (companion): The inference schema, independent of its particular formula/context parameters. Distinct constructor kinds retain distinct codes. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyFOLKStep.schemaKind {L : Language} : AnyFOLKStep L → Nat
  | .one rule => (lkStep1ReplacementData rule).1
  | .two rule => (lkStep2ReplacementData rule).1

/-- Definition 7.3.2 (companion): Ancestry of the two specified inference occurrences in the fixed proof. This tests addresses alone, independently of intermediate rule kinds. -/
@[blueprint "chap7__definition_7_3_2"]
def isDescendantOfPremise {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    (R₁ R₂ : LKInferenceOccurrence T) : Prop :=
  premiseAddressDescendant R₁.address R₂.address

/-- Definition 7.3.2 (companion): The selected upper inference lies above the selected lower inference, with only structural rules strictly between their addresses. Off-path branches are unrestricted. -/
@[blueprint "chap7__definition_7_3_2"]
def descendsWithStructuralIntermediates {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    (R₁ R₂ : LKInferenceOccurrence T) : Prop :=
  isDescendantOfPremise R₁ R₂ ∧
  ∀ middle : LKInferenceOccurrence T,
    premiseAddressDescendant middle.address R₂.address →
    premiseAddressDescendant R₁.address middle.address → middle.rule.isStructural

/-- Definition 7.3.2 (companion): Source boundaries of the selected local segment. The upper inference has one premise; the lower has one or two ordered premises. All boundary trees are actual subtrees of the same ambient proof. The chosen edge and tail identify the branch containing the upper inference. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKPermutationBoundary {L : Language} {s : Sequent L}
    {T : FOLKProofTree s} (upper lower : LKInferenceOccurrence T) where
  upperBoundary : LKOnePremiseBoundary upper
  lowerBoundary : Sum (LKOnePremiseBoundary lower) (LKTwoPremiseBoundary lower)
  branch : Nat
  branchInRange : branch < lower.rule.premises.length
  tail : List Nat
  upperAt : upper.address = lower.address ++ branch :: tail
  structuralPath : descendsWithStructuralIntermediates upper lower

/-- Definition 7.3.2 (companion): The non-context parameters of a named inference. Permutation may change side contexts, but retains its principal/auxiliary formulae, instantiating terms and variable annotations. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyFOLKStep.permutationPayload {L : Language} :
    AnyFOLKStep L → List (FormulaN L) × List (Term L) × List Nat
  | .one rule => match rule with
    | .weakenLeft A _ _ => ([A], [], [])
    | .weakenRight A _ _ => ([A], [], [])
    | .contractLeft A _ _ => ([A], [], [])
    | .contractRight A _ _ => ([A], [], [])
    | .exchangeLeft _ A B _ _ => ([A,B], [], [])
    | .exchangeRight _ _ A B _ => ([A,B], [], [])
    | .andLeftL A B _ _ => ([A,B], [], [])
    | .andLeftR A B _ _ => ([A,B], [], [])
    | .orRightL A B _ _ => ([A,B], [], [])
    | .orRightR A B _ _ => ([A,B], [], [])
    | .implRight A B _ _ => ([A,B], [], [])
    | .negLeft A _ _ => ([A], [], [])
    | .negRight A _ _ => ([A], [], [])
    | .allLeft t x A _ _ _ => ([A], [t], [x])
    | .exRight t x A _ _ _ => ([A], [t], [x])
    | .allRight y x A _ _ _ _ => ([A], [], [y,x])
    | .exLeft y x A _ _ _ _ => ([A], [], [y,x])
  | .two rule => match rule with
    | .cut A _ _ _ _ => ([A], [], [])
    | .andRight A B _ _ => ([A,B], [], [])
    | .orLeft A B _ _ => ([A,B], [], [])
    | .implLeft A B _ _ _ _ => ([A,B], [], [])

/-- Definition 7.3.2 (companion): The unchanged outside continuation T₀, with one sequent-indexed hole. Every rule on its spine and every off-spine proof is retained as data. -/
@[blueprint "chap7__definition_7_3_2"]
inductive LKProofContext {L : Language} (hole : Sequent L) : Sequent L → Type where
  | hole : LKProofContext hole hole
  | one {p c} (rule : FOLKStep1 p c) (rest : LKProofContext hole p) : LKProofContext hole c
  | left {p q c} (rule : FOLKStep2 p q c) (rest : LKProofContext hole p)
      (sibling : FOLKProofTree q) : LKProofContext hole c
  | right {p q c} (rule : FOLKStep2 p q c) (sibling : FOLKProofTree p)
      (rest : LKProofContext hole q) : LKProofContext hole c

/-- Definition 7.3.2 (companion): Reinsert a proof of S₀ into the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKProofContext.plug {L : Language} {hole : Sequent L} :
    {s : Sequent L} → LKProofContext hole s → FOLKProofTree hole → FOLKProofTree s
  | _, .hole, t => t
  | _, .one rule rest, t => .onePremise rule (rest.plug t)
  | _, .left rule rest sibling, t => .twoPremise rule (rest.plug t) sibling
  | _, .right rule sibling rest, t => .twoPremise rule sibling (rest.plug t)

/-- Definition 7.3.2 (companion): The address of the selected local segment in its outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKProofContext.address {L : Language} {hole : Sequent L} :
    {s : Sequent L} → LKProofContext hole s → List Nat
  | _, .hole => []
  | _, .one _ rest => 0 :: rest.address
  | _, .left _ rest _ => 0 :: rest.address
  | _, .right _ _ rest => 1 :: rest.address

/-- Definition 7.3.2 (companion): The local Q as a sequent-indexed open fragment. Its only leaves reference the supplied premise proof trees; it has no axiom constructor. -/
@[blueprint "chap7__definition_7_3_2"]
inductive LKLocalFragment {L : Language}
    (inputs : List (Σ c : Sequent L, FOLKProofTree c)) : Sequent L → Type where
  | input (i : Fin inputs.length) : LKLocalFragment inputs (inputs.get i).1
  | one {p c} (rule : FOLKStep1 p c) (sub : LKLocalFragment inputs p) : LKLocalFragment inputs c
  | two {p q c} (rule : FOLKStep2 p q c)
      (left : LKLocalFragment inputs p) (right : LKLocalFragment inputs q) : LKLocalFragment inputs c

/-- Definition 7.3.2 (companion): Plug the original premise proofs into Q, preserving their proof data exactly. -/
@[blueprint "chap7__definition_7_3_2"]
def LKLocalFragment.plug {L : Language} {inputs : List (Σ c : Sequent L, FOLKProofTree c)} :
    {s : Sequent L} → LKLocalFragment inputs s → FOLKProofTree s
  | _, .input i => (inputs.get i).2
  | _, .one rule sub => .onePremise rule sub.plug
  | _, .two rule left right => .twoPremise rule left.plug right.plug

/-- Definition 7.3.2 (companion): The ordered input occurrences in Q. Equality with the full index range requires every supplied premise tree exactly once, in source order. -/
@[blueprint "chap7__definition_7_3_2"]
def LKLocalFragment.inputOrder {L : Language} {inputs : List (Σ c : Sequent L, FOLKProofTree c)} :
    {s : Sequent L} → LKLocalFragment inputs s → List Nat
  | _, .input i => [i.val]
  | _, .one _ sub => sub.inputOrder
  | _, .two _ left right => left.inputOrder ++ right.inputOrder

/-- Definition 7.3.2 (companion): Inference lookup inside Q alone. Input proof trees are boundary leaves, so their internal rules cannot witness either permuted inference or violate the local structural-only condition. -/
@[blueprint "chap7__definition_7_3_2"]
def LKLocalFragment.inferenceAt {L : Language} {inputs : List (Σ c : Sequent L, FOLKProofTree c)} :
    {s : Sequent L} → LKLocalFragment inputs s → List Nat → Option (AnyFOLKStep L)
  | _, .one rule _, [] => some (.one rule)
  | _, .two rule _ _, [] => some (.two rule)
  | _, .one _ sub, 0 :: p => sub.inferenceAt p
  | _, .two _ left _, 0 :: p => left.inferenceAt p
  | _, .two _ _ right, 1 :: p => right.inferenceAt p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): A local replacement certificate: the source segment reconstructs T through the same T₀; Q has the same S₀, uses precisely the original ordered premise trees, retains both named inferences, reverses their ancestry, and has only structural additional inferences. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKLocalReplacement {L : Language} {s c : Sequent L}
    (T : FOLKProofTree s) (rootAddress : List Nat) (source : FOLKProofTree c)
    (inputs : List (Σ p : Sequent L, FOLKProofTree p)) (R₁ R₂ : AnyFOLKStep L) where
  continuation : LKProofContext c s
  atAddress : continuation.address = rootAddress
  sourceFixed : continuation.plug source = T
  replacement : LKLocalFragment inputs c
  inputOrder : replacement.inputOrder = List.range inputs.length
  firstAddress : List Nat
  secondAddress : List Nat
  firstRule : AnyFOLKStep L
  secondRule : AnyFOLKStep L
  firstAt : replacement.inferenceAt firstAddress = some firstRule
  secondAt : replacement.inferenceAt secondAddress = some secondRule
  firstSchema : firstRule.schemaKind = R₁.schemaKind
  secondSchema : secondRule.schemaKind = R₂.schemaKind
  firstPayload : firstRule.permutationPayload = R₁.permutationPayload
  secondPayload : secondRule.permutationPayload = R₂.permutationPayload
  distinct : firstAddress ≠ secondAddress
  reversed : ¬ premiseAddressDescendant firstAddress secondAddress
  otherStructural : ∀ p rule, replacement.inferenceAt p = some rule →
    p ≠ firstAddress → p ≠ secondAddress → rule.isStructural

/-- Definition 7.3.2 (companion): The resulting proof is computed by plugging Q through exactly the recorded outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKLocalReplacement.result {L : Language} {s c : Sequent L}
    {T : FOLKProofTree s} {rootAddress : List Nat} {source : FOLKProofTree c}
    {inputs : List (Σ p : Sequent L, FOLKProofTree p)} {R₁ R₂ : AnyFOLKStep L}
    (h : LKLocalReplacement T rootAddress source inputs R₁ R₂) : FOLKProofTree s :=
  h.continuation.plug h.replacement.plug

/-- Definition 7.3.2 (companion): The one-premise case fixes T₁, S₀ and the selected lower inference before specifying Q and the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKOnePremiseLocalReplacement {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    {upper lower : LKInferenceOccurrence T} (ub : LKOnePremiseBoundary upper) (lb : LKOnePremiseBoundary lower) : Type :=
  LKLocalReplacement T lower.address (.onePremise lb.rule lb.tree)
    [⟨ub.premise, ub.tree⟩] upper.rule lower.rule

/-- Definition 7.3.2 (companion): The two-premise case preserves the original
left-to-right frontier. On the selected branch its input is the upper rule's
premise tree; the other branch retains the lower rule's entire premise tree. -/
@[blueprint "chap7__definition_7_3_2"]
def LKTwoPremiseLocalReplacement {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    {upper lower : LKInferenceOccurrence T}
    (ub : LKOnePremiseBoundary upper) (lb : LKTwoPremiseBoundary lower)
    (rightBranch : Bool) : Type :=
  LKLocalReplacement T lower.address (.twoPremise lb.rule lb.leftTree lb.rightTree)
    (if rightBranch then [⟨lb.leftSequent, lb.leftTree⟩, ⟨ub.premise, ub.tree⟩]
     else [⟨ub.premise, ub.tree⟩, ⟨lb.rightSequent, lb.rightTree⟩]) upper.rule lower.rule

/-- Definition 7.3.2: Every selected source boundary admits a local Q with
the same ordered premise proof trees and conclusion S₀, plugged into the exact
same outside continuation T₀. Q retains the two named inference schemas and
their non-context parameters, removes the forbidden ancestry, and contains only
structural additional inferences. The principal/side-formula proviso is a
separate condition in the permutability lemma. -/
@[blueprint "chap7__definition_7_3_2" (main := true)]
def CanPermuteWith {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    (R₁ R₂ : LKInferenceOccurrence T) : Prop :=
  ∀ boundary : LKPermutationBoundary R₁ R₂,
    match boundary.lowerBoundary with
    | .inl lb => Nonempty (LKOnePremiseLocalReplacement boundary.upperBoundary lb)
    | .inr lb => match boundary.branch with
      | 0 => Nonempty (LKTwoPremiseLocalReplacement boundary.upperBoundary lb false)
      | 1 => Nonempty (LKTwoPremiseLocalReplacement boundary.upperBoundary lb true)
      | _ => False

/-- Definition 7.3.2 (companion): Ancestry of the two specified inference occurrences in the fixed proof. This tests addresses alone, independently of intermediate rule kinds. -/
@[blueprint "chap7__definition_7_3_2"]
def isDescendantOfPremiseLKe {L : Language} {s : Sequent L} {T : LKeProofTree s}
    (R₁ R₂ : LKeInferenceOccurrence T) : Prop :=
  premiseAddressDescendant R₁.address R₂.address

/-- Definition 7.3.2 (companion): The selected upper inference lies above the selected lower inference, with only structural rules strictly between their addresses. Off-path branches are unrestricted. -/
@[blueprint "chap7__definition_7_3_2"]
def descendsWithStructuralIntermediatesLKe {L : Language} {s : Sequent L} {T : LKeProofTree s}
    (R₁ R₂ : LKeInferenceOccurrence T) : Prop :=
  isDescendantOfPremiseLKe R₁ R₂ ∧
  ∀ middle : LKeInferenceOccurrence T,
    premiseAddressDescendant middle.address R₂.address →
    premiseAddressDescendant R₁.address middle.address → middle.rule.isStructural

/-- Definition 7.3.2 (companion): Source boundaries of the selected local segment. The upper inference has one premise; the lower has one or two ordered premises. All boundary trees are actual subtrees of the same ambient proof. The chosen edge and tail identify the branch containing the upper inference. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKePermutationBoundary {L : Language} {s : Sequent L}
    {T : LKeProofTree s} (upper lower : LKeInferenceOccurrence T) where
  upperBoundary : LKeOnePremiseBoundary upper
  lowerBoundary : Sum (LKeOnePremiseBoundary lower) (LKeTwoPremiseBoundary lower)
  branch : Nat
  branchInRange : branch < lower.rule.premises.length
  tail : List Nat
  upperAt : upper.address = lower.address ++ branch :: tail
  structuralPath : descendsWithStructuralIntermediatesLKe upper lower

/-- Definition 7.3.2 (companion): The unchanged outside continuation T₀, with one sequent-indexed hole. Every rule on its spine and every off-spine proof is retained as data. -/
@[blueprint "chap7__definition_7_3_2"]
inductive LKeProofContext {L : Language} (hole : Sequent L) : Sequent L → Type where
  | hole : LKeProofContext hole hole
  | one {p c} (rule : FOLKStep1 p c) (rest : LKeProofContext hole p) : LKeProofContext hole c
  | left {p q c} (rule : FOLKStep2 p q c) (rest : LKeProofContext hole p)
      (sibling : LKeProofTree q) : LKeProofContext hole c
  | right {p q c} (rule : FOLKStep2 p q c) (sibling : LKeProofTree p)
      (rest : LKeProofContext hole q) : LKeProofContext hole c

/-- Definition 7.3.2 (companion): Reinsert a proof of S₀ into the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeProofContext.plug {L : Language} {hole : Sequent L} :
    {s : Sequent L} → LKeProofContext hole s → LKeProofTree hole → LKeProofTree s
  | _, .hole, t => t
  | _, .one rule rest, t => .onePremise rule (rest.plug t)
  | _, .left rule rest sibling, t => .twoPremise rule (rest.plug t) sibling
  | _, .right rule sibling rest, t => .twoPremise rule sibling (rest.plug t)

/-- Definition 7.3.2 (companion): The address of the selected local segment in its outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeProofContext.address {L : Language} {hole : Sequent L} :
    {s : Sequent L} → LKeProofContext hole s → List Nat
  | _, .hole => []
  | _, .one _ rest => 0 :: rest.address
  | _, .left _ rest _ => 0 :: rest.address
  | _, .right _ _ rest => 1 :: rest.address

/-- Definition 7.3.2 (companion): The local Q as a sequent-indexed open fragment. Its only leaves reference the supplied premise proof trees; it has no axiom constructor. -/
@[blueprint "chap7__definition_7_3_2"]
inductive LKeLocalFragment {L : Language}
    (inputs : List (Σ c : Sequent L, LKeProofTree c)) : Sequent L → Type where
  | input (i : Fin inputs.length) : LKeLocalFragment inputs (inputs.get i).1
  | one {p c} (rule : FOLKStep1 p c) (sub : LKeLocalFragment inputs p) : LKeLocalFragment inputs c
  | two {p q c} (rule : FOLKStep2 p q c)
      (left : LKeLocalFragment inputs p) (right : LKeLocalFragment inputs q) : LKeLocalFragment inputs c

/-- Definition 7.3.2 (companion): Plug the original premise proofs into Q, preserving their proof data exactly. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeLocalFragment.plug {L : Language} {inputs : List (Σ c : Sequent L, LKeProofTree c)} :
    {s : Sequent L} → LKeLocalFragment inputs s → LKeProofTree s
  | _, .input i => (inputs.get i).2
  | _, .one rule sub => .onePremise rule sub.plug
  | _, .two rule left right => .twoPremise rule left.plug right.plug

/-- Definition 7.3.2 (companion): The ordered input occurrences in Q. Equality with the full index range requires every supplied premise tree exactly once, in source order. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeLocalFragment.inputOrder {L : Language} {inputs : List (Σ c : Sequent L, LKeProofTree c)} :
    {s : Sequent L} → LKeLocalFragment inputs s → List Nat
  | _, .input i => [i.val]
  | _, .one _ sub => sub.inputOrder
  | _, .two _ left right => left.inputOrder ++ right.inputOrder

/-- Definition 7.3.2 (companion): Inference lookup inside Q alone. Input proof trees are boundary leaves, so their internal rules cannot witness either permuted inference or violate the local structural-only condition. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeLocalFragment.inferenceAt {L : Language} {inputs : List (Σ c : Sequent L, LKeProofTree c)} :
    {s : Sequent L} → LKeLocalFragment inputs s → List Nat → Option (AnyFOLKStep L)
  | _, .one rule _, [] => some (.one rule)
  | _, .two rule _ _, [] => some (.two rule)
  | _, .one _ sub, 0 :: p => sub.inferenceAt p
  | _, .two _ left _, 0 :: p => left.inferenceAt p
  | _, .two _ _ right, 1 :: p => right.inferenceAt p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): A local replacement certificate: the source segment reconstructs T through the same T₀; Q has the same S₀, uses precisely the original ordered premise trees, retains both named inferences, reverses their ancestry, and has only structural additional inferences. -/
@[blueprint "chap7__definition_7_3_2"]
structure LKeLocalReplacement {L : Language} {s c : Sequent L}
    (T : LKeProofTree s) (rootAddress : List Nat) (source : LKeProofTree c)
    (inputs : List (Σ p : Sequent L, LKeProofTree p)) (R₁ R₂ : AnyFOLKStep L) where
  continuation : LKeProofContext c s
  atAddress : continuation.address = rootAddress
  sourceFixed : continuation.plug source = T
  replacement : LKeLocalFragment inputs c
  inputOrder : replacement.inputOrder = List.range inputs.length
  firstAddress : List Nat
  secondAddress : List Nat
  firstRule : AnyFOLKStep L
  secondRule : AnyFOLKStep L
  firstAt : replacement.inferenceAt firstAddress = some firstRule
  secondAt : replacement.inferenceAt secondAddress = some secondRule
  firstSchema : firstRule.schemaKind = R₁.schemaKind
  secondSchema : secondRule.schemaKind = R₂.schemaKind
  firstPayload : firstRule.permutationPayload = R₁.permutationPayload
  secondPayload : secondRule.permutationPayload = R₂.permutationPayload
  distinct : firstAddress ≠ secondAddress
  reversed : ¬ premiseAddressDescendant firstAddress secondAddress
  otherStructural : ∀ p rule, replacement.inferenceAt p = some rule →
    p ≠ firstAddress → p ≠ secondAddress → rule.isStructural

/-- Definition 7.3.2 (companion): The resulting proof is computed by plugging Q through exactly the recorded outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeLocalReplacement.result {L : Language} {s c : Sequent L}
    {T : LKeProofTree s} {rootAddress : List Nat} {source : LKeProofTree c}
    {inputs : List (Σ p : Sequent L, LKeProofTree p)} {R₁ R₂ : AnyFOLKStep L}
    (h : LKeLocalReplacement T rootAddress source inputs R₁ R₂) : LKeProofTree s :=
  h.continuation.plug h.replacement.plug

/-- Definition 7.3.2 (companion): The one-premise case fixes T₁, S₀ and the selected lower inference before specifying Q and the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeOnePremiseLocalReplacement {L : Language} {s : Sequent L} {T : LKeProofTree s}
    {upper lower : LKeInferenceOccurrence T} (ub : LKeOnePremiseBoundary upper) (lb : LKeOnePremiseBoundary lower) : Type :=
  LKeLocalReplacement T lower.address (.onePremise lb.rule lb.tree)
    [⟨ub.premise, ub.tree⟩] upper.rule lower.rule

/-- Definition 7.3.2 (companion): The two-premise case preserves the original
left-to-right frontier. On the selected branch its input is the upper rule's
premise tree; the other branch retains the lower rule's entire premise tree. -/
@[blueprint "chap7__definition_7_3_2"]
def LKeTwoPremiseLocalReplacement {L : Language} {s : Sequent L} {T : LKeProofTree s}
    {upper lower : LKeInferenceOccurrence T}
    (ub : LKeOnePremiseBoundary upper) (lb : LKeTwoPremiseBoundary lower)
    (rightBranch : Bool) : Type :=
  LKeLocalReplacement T lower.address (.twoPremise lb.rule lb.leftTree lb.rightTree)
    (if rightBranch then [⟨lb.leftSequent, lb.leftTree⟩, ⟨ub.premise, ub.tree⟩]
     else [⟨ub.premise, ub.tree⟩, ⟨lb.rightSequent, lb.rightTree⟩]) upper.rule lower.rule

/-- Definition 7.3.2: Every selected source boundary admits a local Q with
the same ordered premise proof trees and conclusion S₀, plugged into the exact
same outside continuation T₀. Q retains the two named inference schemas and
their non-context parameters, removes the forbidden ancestry, and contains only
structural additional inferences. The principal/side-formula proviso is a
separate condition in the permutability lemma. -/
@[blueprint "chap7__definition_7_3_2" (main := true)]
def CanPermuteWithLKe {L : Language} {s : Sequent L} {T : LKeProofTree s}
    (R₁ R₂ : LKeInferenceOccurrence T) : Prop :=
  ∀ boundary : LKePermutationBoundary R₁ R₂,
    match boundary.lowerBoundary with
    | .inl lb => Nonempty (LKeOnePremiseLocalReplacement boundary.upperBoundary lb)
    | .inr lb => match boundary.branch with
      | 0 => Nonempty (LKeTwoPremiseLocalReplacement boundary.upperBoundary lb false)
      | 1 => Nonempty (LKeTwoPremiseLocalReplacement boundary.upperBoundary lb true)
      | _ => False

end LCS.Herbrand.SharpenedHauptsatz.Permutability

-- ===================================================================
-- Lemma 7.3.3 (companion def): FOLKStep1.isQuantifier /
--                              FOLKStep2.isQuantifier
-- ===================================================================

namespace LCS.CutElim.LK.FOLKStep1

/-- Lemma 7.3.3 (companion def): Returns True for the four quantifier one-premise rules: allLeft, allRight, exLeft, exRight. Returns False for all other one-premise rules (structural, logical). -/
@[blueprint "chap7__lemma_7_3_3"]
def isQuantifier {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .allLeft _ _ _ _ _ _ => True
  | .allRight _ _ _ _ _ _ _ => True
  | .exLeft _ _ _ _ _ _ _ => True
  | .exRight _ _ _ _ _ _ => True
  | .weakenLeft _ _ _ => False
  | .weakenRight _ _ _ => False
  | .contractLeft _ _ _ => False
  | .contractRight _ _ _ => False
  | .exchangeLeft _ _ _ _ _ => False
  | .exchangeRight _ _ _ _ _ => False
  | .andLeftL _ _ _ _ => False
  | .andLeftR _ _ _ _ => False
  | .orRightL _ _ _ _ => False
  | .orRightR _ _ _ _ => False
  | .implRight _ _ _ _ => False
  | .negLeft _ _ _ => False
  | .negRight _ _ _ => False

/-- Lemma 7.3.3 (companion def): Returns True for the propositional and quantifier logical one-premise rules (andLeftL/R, orRightL/R, implRight, negLeft, negRight, allLeft, allRight, exLeft, exRight). Returns False for structural rules. -/
@[blueprint "chap7__lemma_7_3_3"]
def isLogical {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .andLeftL _ _ _ _ => True
  | .andLeftR _ _ _ _ => True
  | .orRightL _ _ _ _ => True
  | .orRightR _ _ _ _ => True
  | .implRight _ _ _ _ => True
  | .negLeft _ _ _ => True
  | .negRight _ _ _ => True
  | .allLeft _ _ _ _ _ _ => True
  | .allRight _ _ _ _ _ _ _ => True
  | .exLeft _ _ _ _ _ _ _ => True
  | .exRight _ _ _ _ _ _ => True
  | .weakenLeft _ _ _ => False
  | .weakenRight _ _ _ => False
  | .contractLeft _ _ _ => False
  | .contractRight _ _ _ => False
  | .exchangeLeft _ _ _ _ _ => False
  | .exchangeRight _ _ _ _ _ => False

/-- Lemma 7.3.3 (companion def): Returns True for weakenLeft and
    weakenRight. Returns False for all other rules. -/
@[blueprint "chap7__lemma_7_3_3"]
def isWeakening {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .weakenLeft _ _ _ => True
  | .weakenRight _ _ _ => True
  | _ => False

/-- Lemma 7.3.3 (companion def): Returns True for contractLeft and
    contractRight. Returns False for all other rules. -/
@[blueprint "chap7__lemma_7_3_3"]
def isContraction {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .contractLeft _ _ _ => True
  | .contractRight _ _ _ => True
  | _ => False

/-- Lemma 7.3.3 (companion def): Returns True for exchangeLeft and
    exchangeRight. Returns False for all other rules. -/
@[blueprint "chap7__lemma_7_3_3"]
def isExchange {L : Language} {prem conc : Sequent L} :
    FOLKStep1 prem conc → Prop
  | .exchangeLeft _ _ _ _ _ => True
  | .exchangeRight _ _ _ _ _ => True
  | _ => False

/-- Lemma 7.3.3 (companion def): Returns the principal formula of a logical or quantifier one-premise rule (the compound formula introduced by the rule in the conclusion). Returns `none` for structural rules. For quantifier and propositional logical rules the principal formula is a fixed position in the indexed conclusion sequent. -/
@[blueprint "chap7__lemma_7_3_3"]
def principalFormula {L : Language} : {prem conc : Sequent L} →
    FOLKStep1 prem conc → Option (FormulaN L)
  | _, _, .andLeftL A B _ _ => some (FormulaN.conj A B)
  | _, _, .andLeftR A B _ _ => some (FormulaN.conj A B)
  | _, _, .orRightL A B _ _ => some (FormulaN.disj A B)
  | _, _, .orRightR A B _ _ => some (FormulaN.disj A B)
  | _, _, .implRight A B _ _ => some (FormulaN.impl A B)
  | _, _, .negLeft A _ _ => some (FormulaN.neg A)
  | _, _, .negRight A _ _ => some (FormulaN.neg A)
  | _, _, .allLeft _ x A _ _ _ => some (FormulaN.all x A)
  | _, _, .allRight _ x A _ _ _ _ => some (FormulaN.all x A)
  | _, _, .exLeft _ x A _ _ _ _ => some (FormulaN.ex x A)
  | _, _, .exRight _ x A _ _ _ => some (FormulaN.ex x A)
  | _, _, .weakenLeft _ _ _ => none
  | _, _, .weakenRight _ _ _ => none
  | _, _, .contractLeft _ _ _ => none
  | _, _, .contractRight _ _ _ => none
  | _, _, .exchangeLeft _ _ _ _ _ => none
  | _, _, .exchangeRight _ _ _ _ _ => none

/-- Lemma 7.3.3 (companion def): Returns the list of side formulae of a one-premise rule per textbook §6.2.1 (iter13/docs/context/chap6/ sec2/6_2_1_Syntax_of_LK.md:44,52). A side formula is an IMMEDIATE SUBFORMULA of the principal formula (NOT the surrounding context Γ/Δ). Following the textbook: - ∧:left: principal A∧B, side = [A] (andLeftL) or [B] (andLeftR) - ∨:right: principal A∨B, side = [A] (orRightL) or [B] (orRightR) - ⊃:right: principal A⊃B, side = [A, B] - ¬:left / ¬:right: principal ¬A, side = [A] - ∀:left: principal ∀xA, side = [A[t/x]] - ∀:right: principal ∀xA, side = [A[y/x]] - ∃:left: principal ∃xA, side = [A[y/x]] - ∃:right: principal ∃xA, side = [A[t/x]] - Structural rules: no principal ⇒ no side formulae ⇒ []. -/
@[blueprint "chap7__lemma_7_3_3"]
def sideFormulae {L : Language} : {prem conc : Sequent L} →
    FOLKStep1 prem conc → List (FormulaN L)
  | _, _, .andLeftL A _ _ _ => [A]
  | _, _, .andLeftR _ B _ _ => [B]
  | _, _, .orRightL A _ _ _ => [A]
  | _, _, .orRightR _ B _ _ => [B]
  | _, _, .implRight A B _ _ => [A, B]
  | _, _, .negLeft A _ _ => [A]
  | _, _, .negRight A _ _ => [A]
  | _, _, .allLeft t x A _ _ _ => [formulaSubstN A t x]
  | _, _, .allRight y x A _ _ _ _ => [formulaSubstN A (Term.var y) x]
  | _, _, .exLeft y x A _ _ _ _ => [formulaSubstN A (Term.var y) x]
  | _, _, .exRight t x A _ _ _ => [formulaSubstN A t x]
  | _, _, .weakenLeft _ _ _ => []
  | _, _, .weakenRight _ _ _ => []
  | _, _, .contractLeft _ _ _ => []
  | _, _, .contractRight _ _ _ => []
  | _, _, .exchangeLeft _ _ _ _ _ => []
  | _, _, .exchangeRight _ _ _ _ _ => []

end LCS.CutElim.LK.FOLKStep1

namespace LCS.CutElim.LK.FOLKStep2

/-- Lemma 7.3.3 (companion def): Two-premise rules are never quantifier
    rules (all quantifier rules in LK are one-premise). -/
@[blueprint "chap7__lemma_7_3_3"]
def isQuantifier {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | _ => False

/-- Lemma 7.3.3 (companion def): Two-premise logical rules (andRight,
    orLeft, implLeft). The cut rule is not logical. -/
@[blueprint "chap7__lemma_7_3_3"]
def isLogical {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | .andRight _ _ _ _ => True
  | .orLeft _ _ _ _ => True
  | .implLeft _ _ _ _ _ _ => True
  | .cut _ _ _ _ _ => False

/-- Lemma 7.3.3 (companion def): Two-premise rules are never weakening
    rules (all weakening rules in LK are one-premise). -/
@[blueprint "chap7__lemma_7_3_3"]
def isWeakening {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | _ => False

/-- Lemma 7.3.3 (companion def): Two-premise rules are never
    contractions. -/
@[blueprint "chap7__lemma_7_3_3"]
def isContraction {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | _ => False

/-- Lemma 7.3.3 (companion def): Two-premise rules are never
    exchanges. -/
@[blueprint "chap7__lemma_7_3_3"]
def isExchange {L : Language} {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | _ => False

/-- Lemma 7.3.3 (companion def): Returns the principal formula of a two-premise rule. For andRight A/B returns A /\ B; for orLeft A/B returns A \/ B; for implLeft A/B returns A => B; for cut (which has no principal formula in the textbook sense) returns none. -/
@[blueprint "chap7__lemma_7_3_3"]
def principalFormula {L : Language} : {prem1 prem2 conc : Sequent L} →
    FOLKStep2 prem1 prem2 conc → Option (FormulaN L)
  | _, _, _, .andRight A B _ _ => some (FormulaN.conj A B)
  | _, _, _, .orLeft A B _ _ => some (FormulaN.disj A B)
  | _, _, _, .implLeft A B _ _ _ _ => some (FormulaN.impl A B)
  | _, _, _, .cut _ _ _ _ _ => none

/-- Lemma 7.3.3 (companion def): Side formulae of a two-premise rule per textbook §6.2.1 (iter13/docs/context/chap6/sec2/ 6_2_1_Syntax_of_LK.md:44). A side formula is an IMMEDIATE SUBFORMULA of the principal formula (NOT the surrounding context): - ∧:right: principal A∧B, side = [A, B] - ∨:left: principal A∨B, side = [A, B] - ⊃:left: principal A⊃B, side = [A, B] - cut: has no principal formula in the textbook sense; returns []. (The cut formula A is the cut formula, not a "side formula" in the §6.2.1 sense. Use `cutFormula` helper to extract it.) -/
@[blueprint "chap7__lemma_7_3_3"]
def sideFormulae {L : Language} : {prem1 prem2 conc : Sequent L} →
    FOLKStep2 prem1 prem2 conc → List (FormulaN L)
  | _, _, _, .andRight A B _ _ => [A, B]
  | _, _, _, .orLeft A B _ _ => [A, B]
  | _, _, _, .implLeft A B _ _ _ _ => [A, B]
  | _, _, _, .cut _ _ _ _ _ => []

/-- Lemma 7.3.3 (companion def): Returns `some A` where A is the cut formula
    for the cut rule, and `none` for all other two-premise rules. -/
@[blueprint "chap7__lemma_7_3_3"]
def cutFormula {L : Language} : {prem1 prem2 conc : Sequent L} →
    FOLKStep2 prem1 prem2 conc → Option (FormulaN L)
  | _, _, _, .cut A _ _ _ _ => some A
  | _, _, _, .andRight _ _ _ _ => none
  | _, _, _, .orLeft _ _ _ _ => none
  | _, _, _, .implLeft _ _ _ _ _ _ => none

end LCS.CutElim.LK.FOLKStep2

-- ===================================================================
-- Lemma 7.3.3 (companion def): AnyFOLKStep classifier lifts
-- ===================================================================

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep

/-- Lemma 7.3.3 (companion def): Quantifier classification at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def isQuantifier {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isQuantifier
  | .two r => r.isQuantifier

/-- Lemma 7.3.3 (companion def): Logical classification at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def isLogical {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isLogical
  | .two r => r.isLogical

/-- Lemma 7.3.3 (companion def): Weakening classification at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def isWeakening {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isWeakening
  | .two r => r.isWeakening

/-- Lemma 7.3.3 (companion def): Contraction classification at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def isContraction {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isContraction
  | .two r => r.isContraction

/-- Lemma 7.3.3 (companion def): Exchange classification at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def isExchange {L : Language} : AnyFOLKStep L → Prop
  | .one r => r.isExchange
  | .two r => r.isExchange

/-- Lemma 7.3.3 (companion def): The cut rule is always a two-premise step (`FOLKStep2.cut`), so this predicate is True iff the packaged step is a two-premise cut. -/
@[blueprint "chap7__lemma_7_3_3"]
def isCut {L : Language} : AnyFOLKStep L → Prop
  | .one _ => False
  | .two r =>
    match r with
    | .cut _ _ _ _ _ => True
    | _ => False

/-- Lemma 7.3.3 (companion def): Principal formula at the
    `AnyFOLKStep` level. -/
@[blueprint "chap7__lemma_7_3_3"]
def principalFormula {L : Language} : AnyFOLKStep L → Option (FormulaN L)
  | .one r => r.principalFormula
  | .two r => r.principalFormula

/-- Lemma 7.3.3 (companion def): Side formulae at the `AnyFOLKStep`
    level. -/
@[blueprint "chap7__lemma_7_3_3"]
def sideFormulae {L : Language} : AnyFOLKStep L → List (FormulaN L)
  | .one r => r.sideFormulae
  | .two r => r.sideFormulae

end LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep

-- ===================================================================
-- Lemma 7.3.3 (companion def): principalNotSideOf
-- ===================================================================

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability

/-- Lemma 7.3.3 (companion def): Predicate asserting that the principal formula of R_1 (if any) is not among the side formulae of R_2. This is the proviso in part (i) of the lemma: the principal formula of the quantifier rule must not be a side formula of the lower rule. -/
@[blueprint "chap7__lemma_7_3_3"]
def principalNotSideOf {L : Language}
    (R₁ R₂ : AnyFOLKStep L) : Prop :=
  match R₁.principalFormula with
  | none => True
  | some pf => pf ∉ R₂.sideFormulae





-- ===================================================================
-- Lemma 7.3.3 (helper): FOLKProofTree.hasOnlyAtomicCuts
-- ===================================================================

/-- Lemma 7.3.3 (companion def): Predicate on indexed `FOLKProofTree` asserting that every cut rule appearing in the tree has an atomic cut formula. Recurses through the tree structure, checking `FOLKStep2.cutFormula` at each two-premise node (which is `some A` only for the cut rule, `none` otherwise). For non-cut two-premise rules and all one-premise nodes the condition is vacuous. -/
@[blueprint "chap7__lemma_7_3_3"]
def FOLKProofTree.hasOnlyAtomicCuts {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ sub => FOLKProofTree.hasOnlyAtomicCuts sub
  | _, .twoPremise rule sub1 sub2 =>
    (∀ A, rule.cutFormula = some A → A.isAtomic = true) ∧
    FOLKProofTree.hasOnlyAtomicCuts sub1 ∧
    FOLKProofTree.hasOnlyAtomicCuts sub2

/-- Lemma 7.3.3 (companion): The upper inference is at the actual premise node of the lower unary inference. The weakening hypotheses in the lemma ensure the lower rule has one premise. -/
@[blueprint "chap7__lemma_7_3_3"]
def LKInferenceOccurrence.immediatelyAbove {L : Language} {s : Sequent L}
    {T : FOLKProofTree s} (upper lower : LKInferenceOccurrence T) : Prop :=
  upper.address = lower.address ++ [0]

/-- Lemma 7.3.3 (companion): The upper inference is at the actual premise node of the lower unary inference. The weakening hypotheses in the lemma ensure the lower rule has one premise. -/
@[blueprint "chap7__lemma_7_3_3"]
def LKeInferenceOccurrence.immediatelyAbove {L : Language} {s : Sequent L}
    {T : LKeProofTree s} (upper lower : LKeInferenceOccurrence T) : Prop :=
  upper.address = lower.address ++ [0]

/-- Lemma 7.3.3 (companion): An LKₑ proof has no essential cuts exactly when every cut formula is atomic. Ordinary and equality axioms are leaves; every ordinary-rule subtree is checked. -/
@[blueprint "chap7__lemma_7_3_3"]
def LKeProofTree.hasOnlyAtomicCuts {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ sub => LKeProofTree.hasOnlyAtomicCuts sub
  | _, .twoPremise rule left right =>
    (∀ A, rule.cutFormula = some A → A.isAtomic = true) ∧
    LKeProofTree.hasOnlyAtomicCuts left ∧ LKeProofTree.hasOnlyAtomicCuts right

-- ===================================================================
-- Lemma 7.3.3: permutability_quantifier_with_rule
-- ===================================================================

/-- Lemma 7.3.3: Both clauses for actual occurrences in a pure equality-free LK proof, retaining the atomic-cut generalization of the cut-free case. Clause (i) has the syntactic principal/side proviso; clause (ii) requires the upper node to be the actual premise of the selected weakening. -/
@[attach_debt, blueprint "chap7__lemma_7_3_3" (main := true)]
theorem permutability_quantifier_with_rule
    {L : Language} (_hL : L.withoutEquality) {s : Sequent L} (T : FOLKProofTree s)
    (R₁ R₂ : LKInferenceOccurrence T)
    (hpure : IsPureVariableProofLK T)
    /- STANDING ASSUMPTION #24 (§6.4.6): in LKe "without essential
       cuts" all cuts are atomic. This strictly generalizes the
       LK "cut-free" hypothesis (cut-free ⇒ hasOnlyAtomicCuts
       vacuously). -/
    (hatomic : FOLKProofTree.hasOnlyAtomicCuts T) :
    -- Part (i): quantifier rule permutes with logical/structural/cut
    -- under the principal/side formula proviso
    ((R₁.rule.isQuantifier →
      (R₂.rule.isLogical ∨ R₂.rule.isStructural ∨ R₂.rule.isCut) →
      principalNotSideOf R₁.rule R₂.rule →
      CanPermuteWith R₁ R₂) ∧
    -- Part (ii): quantifier/contraction/exchange rule permutes with
    -- weakening whose premise IS the conclusion of R_1
    ((R₁.rule.isQuantifier ∨ R₁.rule.isContraction ∨ R₁.rule.isExchange) →
      R₂.rule.isWeakening →
      R₁.immediatelyAbove R₂ →
      CanPermuteWith R₁ R₂)) 

-- ===================================================================
-- Lemma 7.3.3 (LKe version): permutability_quantifier_with_rule_LKe
-- ===================================================================

/-- Lemma 7.3.3 (companion): Both source clauses on genuine LKₑ proofs over an equality language, with corrected purity and no essential cuts. The selected occurrences and local replacement witnesses belong to that same LKₑ proof calculus. -/
@[attach_debt, blueprint "chap7__lemma_7_3_3" (main := true)]
theorem permutability_quantifier_with_rule_LKe
    {L : Language} (_hL : L.hasEquality = true) {s : Sequent L} (T : LKeProofTree s)
    (R₁ R₂ : LKeInferenceOccurrence T)
    (hpure : IsPureVariableProofLKe T)
    (hatomic : LKeProofTree.hasOnlyAtomicCuts T) :
    ((R₁.rule.isQuantifier →
      (R₂.rule.isLogical ∨ R₂.rule.isStructural ∨ R₂.rule.isCut) →
      principalNotSideOf R₁.rule R₂.rule → CanPermuteWithLKe R₁ R₂) ∧
    ((R₁.rule.isQuantifier ∨ R₁.rule.isContraction ∨ R₁.rule.isExchange) →
      R₂.rule.isWeakening → R₁.immediatelyAbove R₂ → CanPermuteWithLKe R₁ R₂)) 


/-- Lemma 7.3.3 (companion): The four quantifier inference schemas named in the directed permutation remark. -/
@[blueprint "chap7__lemma_7_3_3"]
inductive QuantifierInferenceKind where
  | allRight | exLeft | allLeft | exRight
  deriving DecidableEq

end LCS.Herbrand.SharpenedHauptsatz.Permutability
