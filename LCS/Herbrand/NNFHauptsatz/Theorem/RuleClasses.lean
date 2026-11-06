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
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleClasses.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.RuleClasses

Section 7.4.3: the classes of G2nnf rules used by Lemma 7.4.2 (quantifier rules,
propositional rules, weakenings, cuts) and the stored side contexts of a rule.
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
namespace LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isQuantifierRule
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for the four quantifier-for-subformulae rules of G2nnf (allSubLeft, allSubRight, exSubLeft, exSubRight). Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isQuantifierRule {L : Language} : G2nnfRuleCore L → Prop
  | .allSubLeft _ _ _ _ _ _ _ _ => True
  | .allSubRight _ _ _ _ _ _ _ _ => True
  | .exSubLeft _ _ _ _ _ _ _ _ => True
  | .exSubRight _ _ _ _ _ _ _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isPropositionalRule
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for the propositional logical rules of G2nnf (conjLeft1, conjLeft2, conjRight, disjLeft, disjRight1, disjRight2). Returns False for all other rules. -/
@[blueprint "chap7__lemma_7_4_2"]
def isPropositionalRule {L : Language} :
    G2nnfRuleCore L → Prop
  | .conjLeft1 _ _ _ _ => True
  | .conjLeft2 _ _ _ _ => True
  | .conjRight _ _ _ _ => True
  | .disjLeft _ _ _ _ => True
  | .disjRight1 _ _ _ _ => True
  | .disjRight2 _ _ _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isWeakening
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for weakLeft and
weakRight. Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isWeakening {L : Language} : G2nnfRuleCore L → Prop
  | .weakLeft _ _ _ => True
  | .weakRight _ _ _ => True
  | _ => False

end LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore
namespace LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Recognize the four quantifier rules of the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isQuantifierRule {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isQuantifierRule

/-- Recognize the six propositional rules of the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isPropositionalRule {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isPropositionalRule

/-- Recognize left or right weakening in the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isWeakening {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isWeakening

end LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Stored antecedent/succedent side contexts. For cut these are the first
premise's frame; the independent second frame remains in the rule itself. -/
def g2nnfRuleSideContexts {L : Language} : G2nnfRuleCore L →
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .axiomPosId _ _ Gamma Delta | .axiomNegId _ _ Gamma Delta
  | .axiomCompRight _ _ Gamma Delta | .axiomCompLeft _ _ Gamma Delta
  | .weakLeft _ Gamma Delta | .weakRight _ Gamma Delta
  | .conjLeft1 _ _ Gamma Delta | .conjLeft2 _ _ Gamma Delta
  | .conjRight _ _ Gamma Delta | .disjLeft _ _ Gamma Delta
  | .disjRight1 _ _ Gamma Delta | .disjRight2 _ _ Gamma Delta
  | .cut _ _ _ Gamma Delta
  | .allSubLeft _ _ _ _ _ _ Gamma Delta
  | .allSubRight _ _ _ _ _ _ Gamma Delta
  | .exSubLeft _ _ _ _ _ _ Gamma Delta
  | .exSubRight _ _ _ _ _ _ Gamma Delta => (Gamma, Delta)
end LCS.Herbrand.NNFHauptsatz.Theorem
end
