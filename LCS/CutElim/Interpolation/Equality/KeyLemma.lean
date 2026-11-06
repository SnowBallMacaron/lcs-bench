import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.ClosedAxioms
import Attach
import LCS.CutElim.Interpolation.Equality.KeyLemma.ProofsStamp

section
namespace LCS.CutElim.Interpolation.Equality
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
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Lemma 6.5.4 (required type): LKeBotProofTree
-- ===================================================================

/-- Proof trees for LKₑ,⊥, indexed by their conclusion sequent.
The system has the ordinary LK axioms and rules, equality-axiom leaves,
and the falsum axiom ⊥ →. The designated nullary predicate represents
the genuine logical constant ⊥. -/
@[blueprint "chap6__lemma_6_5_4"]
inductive LKeBotProofTree {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type where
  /-- Ordinary LK axiom leaf. -/
  | axiom_ (s : Sequent L) (h : isFOLKAxiom s) :
      LKeBotProofTree hL botP hBotArity s
  /-- Equality axiom leaf. -/
  | eqAxiom (ax : LKeEqualityAxiom L) :
      LKeBotProofTree hL botP hBotArity (ax.toSequent hL)
  /-- The falsum axiom ⊥ →. -/
  | botAxiom :
      LKeBotProofTree hL botP hBotArity (Sequent.mk [botFormula botP hBotArity] [])
  /-- One-premise LK rule above an LKₑ,⊥ subproof. -/
  | onePremise {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (t : LKeBotProofTree hL botP hBotArity prem) :
      LKeBotProofTree hL botP hBotArity conc
  /-- Two-premise LK rule above LKₑ,⊥ subproofs, including cut. -/
  | twoPremise {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
      (t1 : LKeBotProofTree hL botP hBotArity prem1)
      (t2 : LKeBotProofTree hL botP hBotArity prem2) :
      LKeBotProofTree hL botP hBotArity conc

-- ===================================================================
-- Lemma 6.5.4 (required def): formulaNonEqPredSymbols
-- ===================================================================

/-- Lemma 6.5.4 (required): The set of predicate symbols occurring
in a formula, excluding the equality symbol. For FormulaN, equality
is a built-in constructor (not a predicate symbol), so this is
simply the set of all predicate symbols in the formula. -/
@[blueprint "chap6__lemma_6_5_4"]
def formulaNonEqPredSymbols {L : Language}
    (A : FormulaN L) : Set L.predSymbols :=
  formulaPredSymbolsN A

-- ===================================================================
-- Lemma 6.5.4 (helper def): listFormulaNonEqPredSymbols
-- ===================================================================

/-- Lemma 6.5.4 (helper): The set of non-equality predicate
symbols occurring in a list of formulae. -/
@[blueprint "chap6__lemma_6_5_4"]
def listFormulaNonEqPredSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.predSymbols :=
  fun P => ∃ A ∈ fs, formulaNonEqPredSymbols A P

-- ===================================================================
-- Lemma 6.5.4 (required structure): IsLKeInterpolant
-- ===================================================================

/-- Lemma 6.5.4 (required): A formula C is an interpolant of a
partition <Gamma_1, Delta_1, Gamma_2, Delta_2> of an LKₑ-provable
sequent if: (i) Gamma_1 -> Delta_1, C and C, Gamma_2 -> Delta_2
are LKₑ-provable, and (ii) all predicate symbols (except equality),
constant symbols, and free variables in C occur both in
Gamma_1 union Delta_1 and in Gamma_2 union Delta_2. -/
@[blueprint "chap6__lemma_6_5_4"]
structure IsLKeInterpolant {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (p : SequentPartition s) (C : FormulaN L) : Prop where
  /-- Gamma_1 -> Delta_1, C is LKₑ-provable -/
  left_lke_provable :
    lkeProvable
      { antecedent := p.gamma1
        succedent := p.delta1 ++ [C] }
  /-- C, Gamma_2 -> Delta_2 is LKₑ-provable -/
  right_lke_provable :
    lkeProvable
      { antecedent := [C] ++ p.gamma2
        succedent := p.delta2 }
  /-- All predicate symbols in C other than equality occur in both sides
      of the partition (OD-A20). Equality is a separate constructor;
      the designated nullary predicate botP is included in this condition. -/
  pred_common_except_eq :
    ∀ P, formulaNonEqPredSymbols C P →
      listFormulaNonEqPredSymbols (p.gamma1 ++ p.delta1) P ∧
      listFormulaNonEqPredSymbols (p.gamma2 ++ p.delta2) P
  /-- All constant symbols in C occur in both sides of the
      partition -/
  const_common :
    formulaConstSymbolsN C ⊆
      listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩
      listFormulaConstSymbols (p.gamma2 ++ p.delta2)
  /-- All free variables in C occur in both sides of the
      partition -/
  fv_common :
    formulaFVN C ⊆
      listFormulaFV (p.gamma1 ++ p.delta1) ∩
      listFormulaFV (p.gamma2 ++ p.delta2)

-- ===================================================================
-- Lemma 6.5.4 (companion theorem): bot_equiv_neg_refl_lke
-- ===================================================================

-- ===================================================================
-- Helper: restricted semantic validity of lkBotProvable
-- ===================================================================

-- ===================================================================
-- Helper: closedReflAxiom has empty const/pred symbols
-- ===================================================================

-- ===================================================================
-- Helper: closedEqualityAxioms have empty const symbols
-- ===================================================================



-- ===================================================================
-- Helper: closedEqualityAxiomsForSide have empty const symbols
-- ===================================================================



-- ===================================================================
-- Helper: closedReflAxiom/closedFunCongAxiom have empty pred symbols
-- (closedPredCongAxiom P has pred symbols = {P})
-- ===================================================================







-- ===================================================================
-- Helper: bridge from sequentPredSymbolsList to listFormulaPredSymbols
-- ===================================================================





-- ===================================================================
-- Helper: closedEqualityAxiomsForSide formulas are universally valid
-- ===================================================================



-- ===================================================================
-- Helper: closedEqualityAxiomsForSide formulas are closed
-- ===================================================================

-- ===================================================================
-- Lemma 6.5.4: public textbook statement and witness
-- ===================================================================

/-- Lemma 6.5.4 (interpolation key lemma with equality): every
partition of an LKₑ-provable sequent has an interpolant whose two
sequents are LKₑ-provable (OD-A18, D6-2 A).
The common-predicate condition exempts only equality (OD-A20).
The designated nullary predicate represents ⊥. Partitions are partitions
of formula occurrences. -/
@[attach_debt, blueprint "chap6__lemma_6_5_4" (main := true)]
theorem interpolation_key_lemma_equality {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s) :
    ∃ C : FormulaN L, IsLKeInterpolant hL botP hBotArity p C 

-- ===================================================================
-- Lemma 6.5.4 (companion theorem): se_partition_union
-- ===================================================================

end LCS.CutElim.Interpolation.Equality
end
