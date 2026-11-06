import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import LCS.FirstOrder.ManySorted.Gentzen.SystemG
import Attach
import LCS.FirstOrder.ManySorted.Gentzen.DeductionTrees.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.Gentzen
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

-- ===================================================================
-- Lemma 10.4.1 (companion type): MSGProofTreeCore
-- ===================================================================

/-- Lemma 10.4.1 (companion, §10.4.2): Proof trees for the many-sorted
Gentzen system G, indexed by their conclusion sequent. Structural
validity is built into the type: leaves must be axiom sequents
(`MSSequentCore.isAxiom`), and each rule application constrains its
premise(s) to have the form mandated by the rule (including side
conditions for quantifier rules, carried by `MSGentzenStep1Frame`). Direct
many-sorted analogue of one-sorted `GProofTree` (chap5 Def 5.4.2). -/
@[blueprint "chap10__lemma_10_4_1"]
inductive MSGProofTreeCore {L : MSLanguage} [DecidableEq L.SortType] :
    MSSequentCore L → Type where
  /-- A leaf: an axiom sequent of G. -/
  | axiom_ (s : MSSequentCore L) (hDomain : s.IsSixConnective) (h : MSSequentCore.isAxiom s) : MSGProofTreeCore s
  /-- A one-premise inference: from a proof tree of the premise and a
      one-premise rule, build a proof tree of the conclusion. -/
  | onePremise {prem conc : MSSequentCore L}
      (rule : MSGentzenStep1Core prem conc)
      (t : MSGProofTreeCore prem) : MSGProofTreeCore conc
  /-- A two-premise inference: from proof trees of both premises and a
      two-premise rule, build a proof tree of the conclusion. -/
  | twoPremise {prem1 prem2 conc : MSSequentCore L}
      (rule : MSGentzenStep2Core prem1 prem2 conc)
      (t1 : MSGProofTreeCore prem1) (t2 : MSGProofTreeCore prem2) :
      MSGProofTreeCore conc

/-- Lemma 10.4.1: G proof trees over the equality-free six-connective domain. -/
@[blueprint "chap10__lemma_10_4_1"]
abbrev MSGProofTree {L : MSLanguage} [DecidableEq L.SortType]
    (_hL : L.withoutEquality) (seq : MSSequentCore L) := MSGProofTreeCore seq

/-- Finite ordered deduction trees with arbitrary open leaves. Every node
has a six-connective sequent and every internal node uses a displayed rule. -/
@[blueprint "chap10__lemma_10_4_1"]
inductive MSGDeductionTreeCore {L : MSLanguage} [DecidableEq L.SortType] :
    MSSequentCore L → Type where
  | leaf (seq : MSSequentCore L) (hDomain : seq.IsSixConnective) :
      MSGDeductionTreeCore seq
  | onePremise {prem conc : MSSequentCore L}
      (rule : MSGentzenStep1Core prem conc) (t : MSGDeductionTreeCore prem) :
      MSGDeductionTreeCore conc
  | twoPremise {prem1 prem2 conc : MSSequentCore L}
      (rule : MSGentzenStep2Core prem1 prem2 conc)
      (t1 : MSGDeductionTreeCore prem1) (t2 : MSGDeductionTreeCore prem2) :
      MSGDeductionTreeCore conc

-- ===================================================================
-- Lemma 10.4.1 (companion def): G-provability
-- ===================================================================

/-- Lemma 10.4.1 (companion, §10.4.2): A many-sorted sequent is
G-provable iff there exists an `MSGProofTreeCore` with that sequent as
conclusion. Many-sorted analogue of one-sorted `sequentProvable`
(chap5 Def 5.4.2). -/
@[blueprint "chap10__lemma_10_4_1"]
def msSequentProvable {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (s : MSSequentCore L) : Prop :=
  Nonempty (MSGProofTree hL s)

/-- An arbitrarily indexed ordered family of many-sorted formulae.
The strict total order records positions, including repeated formulae. -/
structure MSFormulaSequence (L : MSLanguage) where
  Index : Type
  before : Index → Index → Prop
  irrefl : ∀ i, ¬ before i i
  trans : ∀ i j k, before i j → before j k → before i k
  total : ∀ i j, i = j ∨ before i j ∨ before j i
  formula : Index → MSFormula L

/-- General carrier of possibly infinite ordered sequents, shared with G=. -/
structure MSInfSequentCore (L : MSLanguage) where
  antecedent : MSFormulaSequence L
  succedent : MSFormulaSequence L

/-- All formulae of an indexed sequent belong to the six-connective domain. -/
def MSInfSequentCore.IsSixConnective {L : MSLanguage} (seq : MSInfSequentCore L) : Prop :=
  (∀ i, msIsSixConnective (seq.antecedent.formula i)) ∧
  (∀ i, msIsSixConnective (seq.succedent.formula i))

/-- Lemma 10.4.1: possibly infinite sequents of equality-free G. -/
@[blueprint "chap10__lemma_10_4_1"]
def MSInfSequent (L : MSLanguage) (_hL : L.withoutEquality) :=
  {seq : MSInfSequentCore L // seq.IsSixConnective}

/-- A finite subsequence selects distinct positions in their original order. -/
def MSFormulaSequence.IsFiniteSubsequence {L : MSLanguage}
    (a : MSFormulaSequence L) (xs : List (MSFormula L)) : Prop :=
  ∃ f : Fin xs.length → a.Index,
    (∀ i j, i < j → a.before (f i) (f j)) ∧
    ∀ i, xs.get i = a.formula (f i)

/-- A finite subsequent selects an ordered subsequence on each side. -/
def MSInfSequentCore.IsFiniteSubsequent {L : MSLanguage}
    (seq : MSInfSequentCore L) (finite : MSSequentCore L) : Prop :=
  seq.antecedent.IsFiniteSubsequence finite.antecedent ∧
  seq.succedent.IsFiniteSubsequence finite.succedent

/-- Lemma 10.4.1: a possibly infinite sequent is G-provable when some
finite subsequent, with the original order retained, has a G-proof. -/
@[blueprint "chap10__lemma_10_4_1"]
def msInfSequentProvable {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL) : Prop :=
  ∃ finite : MSSequentCore L,
    seq.val.IsFiniteSubsequent finite ∧ msSequentProvable hL finite

end LCS.FirstOrder.ManySorted.Gentzen
end
