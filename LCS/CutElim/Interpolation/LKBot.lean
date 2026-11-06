import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Interpolants
import Attach
import LCS.CutElim.Interpolation.LKBot.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Lemma 6.5.4 (shared definition): isLKBotAxiom
-- ===================================================================

/-- An LK⊥ axiom over a language with or without equality is either
an ordinary LK axiom or the falsum axiom ⊥ →. -/
@[blueprint "chap6__lemma_6_5_4"]
def isLKBotAxiom {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  isFOLKAxiom s ∨ (s.antecedent = [botFormula botP hBotArity] ∧ s.succedent = [])

-- ===================================================================
-- Lemma 6.5.4 (shared definition): FOLKBotProofTree (indexed)
-- ===================================================================

/-- LK⊥ proof trees over a language with or without equality, indexed
by conclusion sequent. The leaves are ordinary LK axioms or ⊥ →.
These trees also serve the equality interpolation construction. -/
@[blueprint "chap6__lemma_6_5_4"]
inductive FOLKBotProofTree {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type where
  | axiom_ (s : Sequent L) (h : isLKBotAxiom botP hBotArity s) : FOLKBotProofTree botP hBotArity s
  | onePremise {prem conc : Sequent L} (rule : FOLKStep1 prem conc) (t : FOLKBotProofTree botP hBotArity prem) : FOLKBotProofTree botP hBotArity conc
  | twoPremise {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc) (t1 : FOLKBotProofTree botP hBotArity prem1) (t2 : FOLKBotProofTree botP hBotArity prem2) : FOLKBotProofTree botP hBotArity conc

namespace FOLKBotProofTree
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

/-- Lemma 6.5.2 (companion): Returns the sequent labeling the root
of the LK_bot proof tree. -/
def conclusion {s : Sequent L} (_ : FOLKBotProofTree botP hBotArity s) : Sequent L := s

-- ===================================================================
-- Lemma 6.5.4 (shared definition): FOLKBotProofTree.isCutFree
-- ===================================================================

/-- An LK⊥ proof tree is cut-free iff every rule in it is cut-free.
This predicate applies to languages with or without equality. -/
@[blueprint "chap6__lemma_6_5_4"]
def isCutFree : {s : Sequent L} → FOLKBotProofTree botP hBotArity s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => t.isCutFree
  | _, .twoPremise r t1 t2 =>
    (match r with | .cut .. => False | _ => True) ∧ t1.isCutFree ∧ t2.isCutFree

end FOLKBotProofTree

/-- A sequent is LK⊥-provable if it has an LK⊥ proof tree, over a
language with or without equality. -/
@[blueprint "chap6__lemma_6_5_4"]
def lkBotProvable {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  Nonempty (FOLKBotProofTree botP hBotArity s)

-- ===================================================================
-- Lemma 6.5.2: LK⊥ over a language without equality
-- ===================================================================

/-- Indexed LK⊥ proof trees over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev FOLKBotProofTreeNoEq {L : Language} (_hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type :=
  FOLKBotProofTree botP hBotArity

/-- Cut-freeness of an LK⊥ proof tree over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev FOLKBotProofTreeNoEq.isCutFree {L : Language} (hL : L.withoutEquality)
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0} {s : Sequent L}
    (t : FOLKBotProofTreeNoEq hL botP hBotArity s) : Prop :=
  FOLKBotProofTree.isCutFree t

/-- Cut elimination for LK⊥ over a language without equality: under the
§6.1 end-sequent convention that no variable occurs both free and bound
anywhere in the sequent, provability is equivalent to the existence of a
cut-free LK⊥ proof of the same sequent. -/
@[attach_debt, blueprint "chap6__lemma_6_5_2"]
theorem lkBot_cut_elimination {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0) (s : Sequent L)
    (hCross : crossNoFreeBound s) :
    lkBotProvable botP hBotArity s ↔
      ∃ t : FOLKBotProofTree botP hBotArity s, t.isCutFree 

-- ===================================================================
-- Helper: folkToBot — convert FOLK proof tree to FOLKBot proof tree
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- Convert an indexed LK proof tree to an indexed LKbot proof tree. Every LK axiom
(identity: [A] -> [A]) is also an LKbot axiom (via the left disjunct
of isLKBotAxiom). -/
def folkToBot {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L} :
    LCS.CutElim.LK.FOLKProofTree s → FOLKBotProofTree botP hBotArity s
  | .axiom_ s h => .axiom_ s (Or.inl h)
  | .onePremise rule t => .onePremise rule (folkToBot botP hBotArity t)
  | .twoPremise rule t1 t2 => .twoPremise rule (folkToBot botP hBotArity t1) (folkToBot botP hBotArity t2)

-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- LK-provability implies LKbot-provability. -/
theorem folkProvable_to_lkBotProvable {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (h : folkProvable s) : lkBotProvable botP hBotArity s := by
  obtain ⟨t⟩ := h; exact ⟨folkToBot botP hBotArity t⟩

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

theorem lkBot_onePremise {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc)
    (h : lkBotProvable botP hBotArity prem) :
    lkBotProvable botP hBotArity conc := by
  obtain ⟨t⟩ := h; exact ⟨.onePremise rule t⟩

theorem lkBot_twoPremise {p1 p2 conc : Sequent L}
    (rule : FOLKStep2 p1 p2 conc)
    (h1 : lkBotProvable botP hBotArity p1) (h2 : lkBotProvable botP hBotArity p2) :
    lkBotProvable botP hBotArity conc := by
  obtain ⟨t1⟩ := h1; obtain ⟨t2⟩ := h2; exact ⟨.twoPremise rule t1 t2⟩

end LCS.CutElim.Interpolation
end
