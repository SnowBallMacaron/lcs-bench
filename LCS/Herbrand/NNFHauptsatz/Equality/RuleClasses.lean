import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.RuleClasses.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.RuleClasses

Definition 7.4.4 and Theorem 7.4.2: the classes of G2nnf= rules (quantifier and
propositional rules, weakenings, inessential cuts).
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
namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqRule

/-- Definition 7.4.4 (companion def): Returns True for the four quantifier-for-subformulae rules of G2nnf= (allSubLeft, allSubRight, exSubLeft, exSubRight). Returns False for other base G2nnf rules and for equality axioms. -/
@[blueprint "chap7__definition_7_4_4"]
def isQuantifierRule {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.allSubLeft _ _ _ _ _ _ _ _) => True
  | .base (.allSubRight _ _ _ _ _ _ _ _) => True
  | .base (.exSubLeft _ _ _ _ _ _ _ _) => True
  | .base (.exSubRight _ _ _ _ _ _ _ _) => True
  | _ => False

-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.isPropositionalOrInessentialCut
-- ===================================================================

/-- Definition 7.4.4 (companion def): Returns True for base G2nnf rules that are propositional (conjunction, disjunction) or inessential cuts. Inessential cuts are cuts whose cut formula is an equality literal s = t or ¬(s = t) — per textbook Def 6.4.9, atomic predicate cuts P(s₁,...,sₙ) where P ≠ = are ESSENTIAL. Returns False for quantifier rules, weakening rules, axioms, and equality axiom schemas. -/
@[blueprint "chap7__lemma_7_4_3"]
def isPropositionalOrInessentialCut {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.conjLeft1 _ _ _ _) => True
  | .base (.conjLeft2 _ _ _ _) => True
  | .base (.conjRight _ _ _ _) => True
  | .base (.disjLeft _ _ _ _) => True
  | .base (.disjRight1 _ _ _ _) => True
  | .base (.disjRight2 _ _ _ _) => True
  | .base (.cut A _ _ _ _) =>
    -- Textbook Def 6.4.9: inessential cut restricts the cut formula
    -- to a literal s = t or ¬(s = t) over the equality predicate
    -- ONLY. Atomic predicate cuts P(s₁,...,sₙ) with P ≠ = are
    -- ESSENTIAL.
    match A with
    | .eq_ _ _ _ => True
    | .neg (.eq_ _ _ _) => True
    | _ => False
  | _ => False

-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.isWeakening
-- ===================================================================

/-- Definition 7.4.4 (companion def): Returns True for base G2nnf weakening rules (weakLeft, weakRight). Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isWeakening {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.weakLeft _ _ _) => True
  | .base (.weakRight _ _ _) => True
  | _ => False

-- ===================================================================
-- Theorem 7.4.2 (companion def): G2nnfEqRule.isInessentialCut
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Returns True for base G2nnf cut rules whose cut formula is an equality literal s = t or ¬(s = t). Textbook Def 6.4.9 explicitly excludes atomic predicate cuts P(s₁,...,sₙ) where P ≠ = — those are ESSENTIAL cuts. -/
@[blueprint "chap7__theorem_7_4_2"]
def isInessentialCut {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.cut A _ _ _ _) =>
    -- Textbook Def 6.4.9: inessential cut restricts the cut formula
    -- to a literal s = t or ¬(s = t) over the equality predicate
    -- ONLY. Atomic predicate cuts P(s₁,...,sₙ) with P ≠ = are
    -- ESSENTIAL.
    match A with
    | .eq_ _ _ _ => True
    | .neg (.eq_ _ _ _) => True
    | _ => False
  | _ => False

-- ===================================================================
-- Theorem 7.4.2 (companion def): G2nnfEqRule.isPropositionalOnly
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Returns True for base G2nnf rules that are purely propositional (conjunction, disjunction) without counting inessential cuts. Used to distinguish the propositional permutation case from the inessential cut case. -/
@[blueprint "chap7__theorem_7_4_2"]
def isPropositionalOnly {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.conjLeft1 _ _ _ _) => True
  | .base (.conjLeft2 _ _ _ _) => True
  | .base (.conjRight _ _ _ _) => True
  | .base (.disjLeft _ _ _ _) => True
  | .base (.disjRight1 _ _ _ _) => True
  | .base (.disjRight2 _ _ _ _) => True
  | _ => False

end LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
end
