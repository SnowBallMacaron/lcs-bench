import LCS.Item
import LCS.Util
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.PrenexForm
import Attach
import LCS.Herbrand.SharpenedHauptsatz.Theorem.SharpenedHauptsatz.ProofsStamp

/-! # Herbrand.SharpenedHauptsatz.Theorem.SharpenedHauptsatz
    Chapter 7, Section 3.3: Theorem 7.3.1 (Gentzen's sharpened Hauptsatz)
    in LK and LKe. The midsequent conditions (1)-(3), and the proof: the
    measures m(T) and n(T) (propositional and weakening inferences below the
    quantifier inferences) and the permutation steps that reduce them in the
    lexicographic order until a midsequent exists.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.PrenexForm

-- ===================================================================
-- Theorem 7.3.1 (companion def): AllRulesPropStructInessentialLK
-- ===================================================================

/-- Theorem 7.3.1 (companion def): Predicate asserting that every rule applied in an indexed `FOLKProofTree` is structural, propositional-logical (logical but not a quantifier rule), or an inessential cut (a cut with an atomic cut formula). Used for the upper part of the midsequent splitting. One-premise rules in the indexed API (`FOLKStep1`) never include cut, so the "inessential cut" disjunct is only active in the two-premise case (via `FOLKStep2.cutFormula`). -/
@[blueprint "chap7__theorem_7_3_1"]
def AllRulesPropStructInessentialLK {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise rule t =>
    (rule.isStructural ∨
     (rule.isLogical ∧ ¬ rule.isQuantifier)) ∧
    AllRulesPropStructInessentialLK t
  | _, .twoPremise rule t1 t2 =>
    (rule.isStructural ∨
     (rule.isLogical ∧ ¬ rule.isQuantifier) ∨
     (match rule.cutFormula with
      | some A => A.isAtomic = true
      | none => False)) ∧
    AllRulesPropStructInessentialLK t1 ∧
    AllRulesPropStructInessentialLK t2

-- ===================================================================
-- Theorem 7.3.1 (companion def): AllRulesQuantContExchToMid
-- ===================================================================

/-- Theorem 7.3.1 (companion def): The rules strictly below the selected
node are quantifier, contraction, or exchange rules. The address uses 0 for
unary/left premises and 1 for right premises. At the selected node itself,
only its conclusion is checked: its concluding inference belongs to the upper
phase. Thus the empty address permits the end sequent, including a propositional
root, as midsequent. Invalid addresses fail. -/
@[blueprint "chap7__theorem_7_3_1"]
def AllRulesQuantContExchToMid {L : Language} (mid : Sequent L) :
    {s : Sequent L} → FOLKProofTree s → List Nat → Prop
  | s, _, [] => s = mid
  | _, .onePremise rule t, 0 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMid mid t p
  | _, .twoPremise rule t _, 0 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMid mid t p
  | _, .twoPremise rule _ t, 1 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMid mid t p
  | _, _, _ => False

-- ===================================================================
-- Theorem 7.3.1 (companion structure): IsMidsequent
-- ===================================================================

/-- Theorem 7.3.1 (companion structure): A quantifier-free midsequent at one
actual node of the fixed proof. A single address selects both the upper subtree
and the end of the lower phase. The inference concluding that node is checked
above it; every inference using it on the path to the root is checked below it.
The upper phase permits structural and propositional rules and atomic cuts;
the lower phase permits quantifier, contraction, and exchange rules. Selecting
the root gives an empty lower phase. -/
@[blueprint "chap7__theorem_7_3_1"]
structure IsMidsequent {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (mid : Sequent L) : Prop where
  /-- Every formula in the midsequent is quantifier-free. -/
  midIsQuantifierFree :
    (∀ A, A ∈ mid.antecedent → FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, A ∈ mid.succedent → FirstOrder.SemanticsN.isQuantifierFree A)
  /-- The upper proof is exactly the subtree at the selected address, and
      the lower phase terminates at that same occurrence. -/
  splitAtNode :
    ∃ (address : List Nat) (tAbove : FOLKProofTree mid),
      lkSubtreeAt T address = some ⟨mid, tAbove⟩ ∧
      AllRulesPropStructInessentialLK tAbove ∧
      AllRulesQuantContExchToMid mid T address

-- ===================================================================
-- Theorem 7.3.1 (companion def): AllRulesPropStructInessentialLKe
-- ===================================================================

/-- Theorem 7.3.1 (companion def): LKe version of `AllRulesPropStructInessentialLK`. Predicate asserting that every rule applied in an `LKeProofTree` is structural, propositional-logical (logical but not a quantifier rule), or an inessential cut (a cut whose cut formula is atomic). Ordinary and equality axioms (including built-in equality congruence) are allowed leaves. One- and two-premise nodes impose the same rule-local side conditions as the LK predicate and recursively check every premise. -/
@[blueprint "chap7__theorem_7_3_1"]
def AllRulesPropStructInessentialLKe {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ _ => True
  | _, .onePremise rule t =>
    (rule.isStructural ∨
     (rule.isLogical ∧ ¬ rule.isQuantifier)) ∧
    AllRulesPropStructInessentialLKe t
  | _, .twoPremise rule t1 t2 =>
    (rule.isStructural ∨
     (rule.isLogical ∧ ¬ rule.isQuantifier) ∨
     (match rule.cutFormula with
      | some A => A.isAtomic = true
      | none => False)) ∧
    AllRulesPropStructInessentialLKe t1 ∧
    AllRulesPropStructInessentialLKe t2

-- ===================================================================
-- Theorem 7.3.1 (companion def): AllRulesQuantContExchToMidLKe
-- ===================================================================

/-- Theorem 7.3.1 (companion def): The rules strictly below the selected
node are quantifier, contraction, or exchange rules. The address uses 0 for
unary/left premises and 1 for right premises. At the selected node itself,
only its conclusion is checked: its concluding inference belongs to the upper
phase. Thus the empty address permits the end sequent, including a propositional
root, as midsequent. Invalid addresses fail. -/
@[blueprint "chap7__theorem_7_3_1"]
def AllRulesQuantContExchToMidLKe {L : Language} (mid : Sequent L) :
    {s : Sequent L} → LKeProofTree s → List Nat → Prop
  | s, _, [] => s = mid
  | _, .onePremise rule t, 0 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMidLKe mid t p
  | _, .twoPremise rule t _, 0 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMidLKe mid t p
  | _, .twoPremise rule _ t, 1 :: p =>
    (rule.isQuantifier ∨ rule.isContraction ∨ rule.isExchange) ∧
    ¬ rule.isWeakening ∧ AllRulesQuantContExchToMidLKe mid t p
  | _, _, _ => False

-- ===================================================================
-- Theorem 7.3.1 (companion structure): IsMidsequentLKe
-- ===================================================================

/-- Theorem 7.3.1 (companion structure): A quantifier-free midsequent at one
actual node of the fixed proof. A single address selects both the upper subtree
and the end of the lower phase. The inference concluding that node is checked
above it; every inference using it on the path to the root is checked below it.
The upper phase permits structural and propositional rules and atomic cuts;
the lower phase permits quantifier, contraction, and exchange rules. Selecting
the root gives an empty lower phase. -/
@[blueprint "chap7__theorem_7_3_1"]
structure IsMidsequentLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (mid : Sequent L) : Prop where
  /-- Every formula in the midsequent is quantifier-free. -/
  midIsQuantifierFree :
    (∀ A, A ∈ mid.antecedent → FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, A ∈ mid.succedent → FirstOrder.SemanticsN.isQuantifierFree A)
  /-- The upper proof is exactly the subtree at the selected address, and
      the lower phase terminates at that same occurrence. -/
  splitAtNode :
    ∃ (address : List Nat) (tAbove : LKeProofTree mid),
      lkeSubtreeAt T address = some ⟨mid, tAbove⟩ ∧
      AllRulesPropStructInessentialLKe tAbove ∧
      AllRulesQuantContExchToMidLKe mid T address

-- ===================================================================
-- Theorem 7.3.1 (companion def): allSequentFormulaeArePrenex
-- ===================================================================

/-- Theorem 7.3.1 (companion def): Predicate asserting that every formula in both the antecedent and succedent of a sequent satisfies `isPrenex`. This is the hypothesis that all formulae in Gamma -> Delta are prenex. -/
@[blueprint "chap7__theorem_7_3_1"]
def allSequentFormulaeArePrenex {L : Language}
    (seq : Sequent L) : Prop :=
  (∀ A, A ∈ seq.antecedent → isPrenex A) ∧
  (∀ A, A ∈ seq.succedent → isPrenex A)

-- ===================================================================
-- Theorem 7.3.1 (companion def): numQuantifierRulesInTree
-- ===================================================================

/-- Theorem 7.3.1 (companion def): Counts the number of quantifier rule applications (`allLeft`, `allRight`, `exLeft`, `exRight`) in the indexed proof tree. Used by `proofMeasureM`. All four quantifier rules live in the one-premise family `FOLKStep1`; two-premise rules in LK (`cut`, `andRight`, `orLeft`, `implLeft`) never introduce quantifiers. -/
@[blueprint "chap7__example_7_3_3"]
def numQuantifierRulesInTree {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .allLeft _ _ _ _ _ _ => 1 + numQuantifierRulesInTree t
    | .allRight _ _ _ _ _ _ _ => 1 + numQuantifierRulesInTree t
    | .exLeft _ _ _ _ _ _ _ => 1 + numQuantifierRulesInTree t
    | .exRight _ _ _ _ _ _ => 1 + numQuantifierRulesInTree t
    | _ => numQuantifierRulesInTree t
  | _, .twoPremise _ t1 t2 =>
    numQuantifierRulesInTree t1 + numQuantifierRulesInTree t2

-- ===================================================================
-- Theorem 7.3.1 (companion def): proofMeasureM
-- ===================================================================

/-- Theorem 7.3.1 (companion def): m(T) is the sum of m(R) over all quantifier inferences R in the proof tree T, where m(R) is the number of propositional-logical inferences on the path from R to the root. Recursive definition from the root outward: if the outermost (closest to root) rule is propositional-logical, every quantifier rule in the subtree t has one more propositional-logical rule on its path to the root, adding (number of quantifier rules in t) to the total. If the outermost rule is a quantifier rule, it contributes m(R) = 0 at this level (no propositional-logical rules above it at this step), so we just recurse. When m(T) = 0, all propositional inferences are above all quantifier inferences. -/
@[blueprint "chap7__example_7_3_3"]
def proofMeasureM {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .andLeftL _ _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .andLeftR _ _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .orRightL _ _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .orRightR _ _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .implRight _ _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .negLeft _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | .negRight _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureM t
    | _ => proofMeasureM t
  | _, .twoPremise rule t1 t2 =>
    match rule with
    | .andRight _ _ _ _ =>
      numQuantifierRulesInTree t1 +
      numQuantifierRulesInTree t2 +
      proofMeasureM t1 + proofMeasureM t2
    | .orLeft _ _ _ _ =>
      numQuantifierRulesInTree t1 +
      numQuantifierRulesInTree t2 +
      proofMeasureM t1 + proofMeasureM t2
    | .implLeft _ _ _ _ _ _ =>
      numQuantifierRulesInTree t1 +
      numQuantifierRulesInTree t2 +
      proofMeasureM t1 + proofMeasureM t2
    | _ =>
      proofMeasureM t1 + proofMeasureM t2

-- ===================================================================
-- Theorem 7.3.1 (companion def): proofMeasureN
-- ===================================================================

/-- Theorem 7.3.1 (companion def): n(T) is the sum of n(R) over all quantifier inferences R in the proof tree T, where n(R) is the number of weakening inferences on the path from R to the root. Recursive definition from the root outward: if the outermost rule is a weakening rule, every quantifier rule in the subtree has one more weakening rule on its path to the root. Otherwise, just recurse. When n(T) = 0, all weakening inferences are above all quantifier inferences. -/
@[blueprint "chap7__example_7_3_3"]
def proofMeasureN {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .weakenLeft _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureN t
    | .weakenRight _ _ _ =>
      numQuantifierRulesInTree t + proofMeasureN t
    | _ => proofMeasureN t
  | _, .twoPremise _ t1 t2 =>
    proofMeasureN t1 + proofMeasureN t2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): Number of quantifier inference occurrences in an LKₑ proof. Ordinary and equality axiom leaves contribute zero; binary premises are counted separately. -/
def numQuantifierRulesInTreeLKe {L : Language} :
    {s : Sequent L} → LKeProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .eqAxiom _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .allLeft _ _ _ _ _ _ => 1 + numQuantifierRulesInTreeLKe t
    | .allRight _ _ _ _ _ _ _ => 1 + numQuantifierRulesInTreeLKe t
    | .exLeft _ _ _ _ _ _ _ => 1 + numQuantifierRulesInTreeLKe t
    | .exRight _ _ _ _ _ _ => 1 + numQuantifierRulesInTreeLKe t
    | _ => numQuantifierRulesInTreeLKe t
  | _, .twoPremise _ t1 t2 =>
    numQuantifierRulesInTreeLKe t1 + numQuantifierRulesInTreeLKe t2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The sum of local m over all quantifier occurrences of an LKₑ proof. Only propositional-logical ancestors contribute; atomic cuts contribute zero, as in the source measure. -/
def proofMeasureMLKe {L : Language} :
    {s : Sequent L} → LKeProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .eqAxiom _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .andLeftL _ _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .andLeftR _ _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .orRightL _ _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .orRightR _ _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .implRight _ _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .negLeft _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | .negRight _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureMLKe t
    | _ => proofMeasureMLKe t
  | _, .twoPremise rule t1 t2 =>
    match rule with
    | .andRight _ _ _ _ =>
      numQuantifierRulesInTreeLKe t1 +
      numQuantifierRulesInTreeLKe t2 +
      proofMeasureMLKe t1 + proofMeasureMLKe t2
    | .orLeft _ _ _ _ =>
      numQuantifierRulesInTreeLKe t1 +
      numQuantifierRulesInTreeLKe t2 +
      proofMeasureMLKe t1 + proofMeasureMLKe t2
    | .implLeft _ _ _ _ _ _ =>
      numQuantifierRulesInTreeLKe t1 +
      numQuantifierRulesInTreeLKe t2 +
      proofMeasureMLKe t1 + proofMeasureMLKe t2
    | _ =>
      proofMeasureMLKe t1 + proofMeasureMLKe t2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The sum of local n over all quantifier occurrences of an LKₑ proof. Only weakening ancestors contribute; ordinary and equality axiom leaves contribute zero. -/
def proofMeasureNLKe {L : Language} :
    {s : Sequent L} → LKeProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .eqAxiom _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .weakenLeft _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureNLKe t
    | .weakenRight _ _ _ =>
      numQuantifierRulesInTreeLKe t + proofMeasureNLKe t
    | _ => proofMeasureNLKe t
  | _, .twoPremise _ t1 t2 =>
    proofMeasureNLKe t1 + proofMeasureNLKe t2

-- ===================================================================
-- Theorem 7.3.1 (companion def): noEssentialCuts
-- ===================================================================

/-- Theorem 7.3.1 (companion def): Predicate asserting that no cut in the canonical LKe proof tree has a non-atomic cut formula (i.e., all cuts are inessential/atomic). Ordinary and equality axioms are vacuous leaves, one-premise nodes recurse into their premise, and two-premise nodes require an atomic cut formula exactly when their rule is cut before recursively checking both premises. -/
@[blueprint "chap7__theorem_7_3_1"]
def noEssentialCuts {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ t => noEssentialCuts t
  | _, .twoPremise rule t1 t2 =>
    (match rule.cutFormula with
     | some A => A.isAtomic = true
     | none => True) ∧
    noEssentialCuts t1 ∧ noEssentialCuts t2

-- ===================================================================
-- Theorem 7.3.1: prescribed permutation phases
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The source-prepared LK proof domain:
prenex end sequent with the end/input free-bound convention, pure-variable
proof, cut-freeness, and atomic axiom leaves. -/
def PhasePreparedLK {L : Language} {s : Sequent L} (T : FOLKProofTree s) : Prop :=
  L.withoutEquality ∧ allSequentFormulaeArePrenex s ∧ Hintikka.crossNoFreeBound s ∧
  IsPureVariableProofLK T ∧ T.isCutFree ∧ hasOnlyAtomicAxioms T

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): An actual selected local replacement and
its output proof, with the original ordered premise proofs and outside
continuation fixed. The m phase permits structural additions. The n phase
permits only contraction/exchange additions besides the two selected rules. -/
def PhaseReplacementLK {L : Language} {s : Sequent L} {T : FOLKProofTree s}
    (upper lower : LKInferenceOccurrence T) (T' : FOLKProofTree s)
    (allowWeakening : Bool) : Prop :=
  ∃ b : LKPermutationBoundary upper lower,
    match b.lowerBoundary with
    | .inl lb => ∃ r : LKOnePremiseLocalReplacement b.upperBoundary lb,
        r.result = T' ∧
        (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
          p ≠ r.firstAddress → p ≠ r.secondAddress →
          rule.isContraction ∨ rule.isExchange)
    | .inr lb => match b.branch with
      | 0 => ∃ r : LKTwoPremiseLocalReplacement b.upperBoundary lb false,
          r.result = T' ∧
          (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
            p ≠ r.firstAddress → p ≠ r.secondAddress →
            rule.isContraction ∨ rule.isExchange)
      | 1 => ∃ r : LKTwoPremiseLocalReplacement b.upperBoundary lb true,
          r.result = T' ∧
          (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
            p ≠ r.firstAddress → p ≠ r.secondAddress →
            rule.isContraction ∨ rule.isExchange)
      | _ => False

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): Positive-m phase: a selected quantifier
inference above a propositional inference with only structural intermediates
is locally permuted. The output is the certified replacement in the same
end sequent. No numerical decrement is assumed in this relation. -/
def MPhaseStepLK {L : Language} {s : Sequent L} (T T' : FOLKProofTree s) : Prop :=
  PhasePreparedLK T ∧ PhasePreparedLK T' ∧ 0 < proofMeasureM T ∧
  ∃ upper lower : LKInferenceOccurrence T,
    upper.rule.isQuantifier ∧ lower.rule.isLogical ∧ ¬ lower.rule.isQuantifier ∧
    principalNotSideOf upper.rule lower.rule ∧ PhaseReplacementLK upper lower T' true

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): With m=0 and n positive, select a quantifier
above a weakening with only contractions/exchanges between them, and move the
weakening above the quantifier through a certified local replacement. -/
def NPhaseStepLK {L : Language} {s : Sequent L} (T T' : FOLKProofTree s) : Prop :=
  PhasePreparedLK T ∧ PhasePreparedLK T' ∧ proofMeasureM T = 0 ∧ 0 < proofMeasureN T ∧
  ∃ upper lower : LKInferenceOccurrence T,
    upper.rule.isQuantifier ∧ lower.rule.isWeakening ∧
    (∀ middle : LKInferenceOccurrence T,
      premiseAddressDescendant middle.address lower.address →
      premiseAddressDescendant upper.address middle.address →
      middle.rule.isContraction ∨ middle.rule.isExchange) ∧
    PhaseReplacementLK upper lower T' false

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The two prescribed phases, with the
positive-m phase preceding the m=0 positive-n phase. -/
def PhaseStepLK {L : Language} {s : Sequent L} (T T' : FOLKProofTree s) : Prop :=
  MPhaseStepLK T T' ∨ NPhaseStepLK T T'

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Theorem 7.3.1 (companion relation): Finite reachability by the prescribed
phase steps. Both endpoints and every intermediate proof have the same indexed
end sequent. This relation specifies finite existence, not a normalizer. -/
inductive PhaseReachableLK {L : Language} {s : Sequent L} :
    FOLKProofTree s → FOLKProofTree s → Prop where
  | refl (T) : PhaseReachableLK T T
  | step {T U V} : PhaseStepLK T U → PhaseReachableLK U V → PhaseReachableLK T V

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The source-prepared LKe proof domain:
prenex end sequent with the end/input free-bound convention, pure-variable
proof, only atomic cuts, and atomic or equality axiom leaves. -/
def PhasePreparedLKe {L : Language} {s : Sequent L} (T : LKeProofTree s) : Prop :=
  L.hasEquality = true ∧ allSequentFormulaeArePrenex s ∧ Hintikka.crossNoFreeBound s ∧
  IsPureVariableProofLKe T ∧ noEssentialCuts T ∧ hasOnlyAtomicOrEqAxioms T

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): An actual selected local replacement and
its output proof, with the original ordered premise proofs and outside
continuation fixed. The m phase permits structural additions. The n phase
permits only contraction/exchange additions besides the two selected rules. -/
def PhaseReplacementLKe {L : Language} {s : Sequent L} {T : LKeProofTree s}
    (upper lower : LKeInferenceOccurrence T) (T' : LKeProofTree s)
    (allowWeakening : Bool) : Prop :=
  ∃ b : LKePermutationBoundary upper lower,
    match b.lowerBoundary with
    | .inl lb => ∃ r : LKeOnePremiseLocalReplacement b.upperBoundary lb,
        r.result = T' ∧
        (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
          p ≠ r.firstAddress → p ≠ r.secondAddress →
          rule.isContraction ∨ rule.isExchange)
    | .inr lb => match b.branch with
      | 0 => ∃ r : LKeTwoPremiseLocalReplacement b.upperBoundary lb false,
          r.result = T' ∧
          (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
            p ≠ r.firstAddress → p ≠ r.secondAddress →
            rule.isContraction ∨ rule.isExchange)
      | 1 => ∃ r : LKeTwoPremiseLocalReplacement b.upperBoundary lb true,
          r.result = T' ∧
          (allowWeakening = true ∨ ∀ p rule, r.replacement.inferenceAt p = some rule →
            p ≠ r.firstAddress → p ≠ r.secondAddress →
            rule.isContraction ∨ rule.isExchange)
      | _ => False

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): Positive-m phase: a selected quantifier
inference above a propositional inference with only structural intermediates
is locally permuted. The output is the certified replacement in the same
end sequent. No numerical decrement is assumed in this relation. -/
def MPhaseStepLKe {L : Language} {s : Sequent L} (T T' : LKeProofTree s) : Prop :=
  PhasePreparedLKe T ∧ PhasePreparedLKe T' ∧ 0 < proofMeasureMLKe T ∧
  ∃ upper lower : LKeInferenceOccurrence T,
    upper.rule.isQuantifier ∧ lower.rule.isLogical ∧ ¬ lower.rule.isQuantifier ∧
    principalNotSideOf upper.rule lower.rule ∧ PhaseReplacementLKe upper lower T' true

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): With m=0 and n positive, select a quantifier
above a weakening with only contractions/exchanges between them, and move the
weakening above the quantifier through a certified local replacement. -/
def NPhaseStepLKe {L : Language} {s : Sequent L} (T T' : LKeProofTree s) : Prop :=
  PhasePreparedLKe T ∧ PhasePreparedLKe T' ∧ proofMeasureMLKe T = 0 ∧ 0 < proofMeasureNLKe T ∧
  ∃ upper lower : LKeInferenceOccurrence T,
    upper.rule.isQuantifier ∧ lower.rule.isWeakening ∧
    (∀ middle : LKeInferenceOccurrence T,
      premiseAddressDescendant middle.address lower.address →
      premiseAddressDescendant upper.address middle.address →
      middle.rule.isContraction ∨ middle.rule.isExchange) ∧
    PhaseReplacementLKe upper lower T' false

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.3.1 (companion def): The two prescribed phases, with the
positive-m phase preceding the m=0 positive-n phase. -/
def PhaseStepLKe {L : Language} {s : Sequent L} (T T' : LKeProofTree s) : Prop :=
  MPhaseStepLKe T T' ∨ NPhaseStepLKe T T'

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Theorem 7.3.1 (companion relation): Finite reachability by the prescribed
phase steps. Both endpoints and every intermediate proof have the same indexed
end sequent. This relation specifies finite existence, not a normalizer. -/
inductive PhaseReachableLKe {L : Language} {s : Sequent L} :
    LKeProofTree s → LKeProofTree s → Prop where
  | refl (T) : PhaseReachableLKe T T
  | step {T U V} : PhaseStepLKe T U → PhaseReachableLKe U V → PhaseReachableLKe T V

end LCS.Herbrand.SharpenedHauptsatz.Theorem

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Theorem 7.3.1: sharpenedHauptsatz_LK
-- ===================================================================

/-- Theorem 7.3.1: Over a language without equality, an LK-provable prenex
sequent satisfying the chapter's sequent-wide free/bound variable convention
has a cut-free pure-variable proof of the same sequent with a midsequent.
The convention is imposed on the end/input sequent. Purity uses actual
node occurrences, and the midsequent selects one node shared by the upper
and lower phases: its formulae are quantifier-free, its upper rules are
structural or propositional (or atomic cuts), and its lower rules are
quantifier, contraction, or exchange rules. The lower phase may be empty. -/
@[attach_debt, blueprint "chap7__theorem_7_3_1" (main := true)]
theorem sharpenedHauptsatz_LK {L : Language}
    (hL : L.withoutEquality) (seq : Sequent L)
    (hCross : Hintikka.crossNoFreeBound seq)
    (hAllPrenex : allSequentFormulaeArePrenex seq)
    (hprov : folkProvable seq) :
    ∃ (t : FOLKProofTree seq) (mid : Sequent L),
      t.isCutFree ∧
      IsPureVariableProofLK t ∧
      IsMidsequent t mid

-- ===================================================================
-- Theorem 7.3.1 (companion theorem): sharpenedHauptsatz_LKe
-- ===================================================================

/-- Theorem 7.3.1 (companion LKₑ variant): An LKₑ-provable prenex sequent
satisfying the chapter's sequent-wide free/bound variable convention has a
pure-variable proof of the same sequent without essential cuts and with a
midsequent. The convention is imposed on the end/input sequent. The genuine
LKₑ proof uses occurrence-based purity and a single selected midsequent node;
atomic cuts are permitted in the upper phase, and the lower phase may be empty. -/
@[attach_debt, blueprint "chap7__theorem_7_3_1" (main := true)]
theorem sharpenedHauptsatz_LKe {L : Language}
    (seq : Sequent L)
    (hCross : Hintikka.crossNoFreeBound seq)
    (hAllPrenex : allSequentFormulaeArePrenex seq)
    (hprov : lkeProvable seq) :
    ∃ (t : LKeProofTree seq) (mid : Sequent L),
      IsPureVariableProofLKe t ∧
      IsMidsequentLKe t mid ∧
      noEssentialCuts t

end LCS.Herbrand.SharpenedHauptsatz.Theorem
