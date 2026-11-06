import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.LKBot
import Attach
import LCS.CutElim.Interpolation.Partitions.ProofsStamp

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
namespace List

/-- Lemma 6.5.2 (required type): Two lists l1 and l2 form an
interleaving of a list l if l can be obtained by interleaving the
elements of l1 and l2 while preserving the relative order within
each list. Used in `SequentPartition` to express that the antecedent
(resp. succedent) is the union of two disjoint subsequences. -/
@[blueprint "chap6__lemma_6_5_2"]
inductive Interleaving {α : Type} :
    List α → List α → List α → Prop where
  /-- The empty list is an interleaving of two empty lists -/
  | nil : List.Interleaving [] [] []
  /-- Prepending an element from the first list -/
  | left (a : α) {l1 l2 l : List α} :
    List.Interleaving l1 l2 l →
    List.Interleaving (a :: l1) l2 (a :: l)
  /-- Prepending an element from the second list -/
  | right (a : α) {l1 l2 l : List α} :
    List.Interleaving l1 l2 l →
    List.Interleaving l1 (a :: l2) (a :: l)

end List

-- ===================================================================
-- Lemma 6.5.2 (required structure): SequentPartition
-- ===================================================================

/-- Lemma 6.5.2 (required): A partition of a sequent Gamma -> Delta
is a quadruple <Gamma_1, Delta_1, Gamma_2, Delta_2> where
(Gamma_1, Gamma_2) are disjoint subsequences of Gamma whose
interleaving gives Gamma, and similarly (Delta_1, Delta_2) are
disjoint subsequences of Delta whose interleaving gives Delta. -/
@[blueprint "chap6__lemma_6_5_2"]
structure SequentPartition {L : Language} (s : Sequent L) where
  /-- The first partition of the antecedent -/
  gamma1 : List (FormulaN L)
  /-- The first partition of the succedent -/
  delta1 : List (FormulaN L)
  /-- The second partition of the antecedent -/
  gamma2 : List (FormulaN L)
  /-- The second partition of the succedent -/
  delta2 : List (FormulaN L)
  /-- The antecedent is an interleaving of gamma1 and gamma2 -/
  gamma_partition :
    List.Interleaving gamma1 gamma2 s.antecedent
  /-- The succedent is an interleaving of delta1 and delta2 -/
  delta_partition :
    List.Interleaving delta1 delta2 s.succedent

-- ===================================================================

-- ===================================================================
-- Lemma 6.5.2 (required structure): IsInterpolant
-- ===================================================================

/-- Lemma 6.5.2 (required): A formula C is an interpolant of a
partition <Gamma_1, Delta_1, Gamma_2, Delta_2> of a sequent if:
(i) Gamma_1 -> Delta_1, C and C, Gamma_2 -> Delta_2 are
LK_bot-provable, and (ii) all predicate symbols (except falsum),
constant symbols, and free variables in C occur both in
Gamma_1 union Delta_1 and in Gamma_2 union Delta_2. -/
@[blueprint "chap6__lemma_6_5_2"]
structure IsInterpolant {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (p : SequentPartition s) (C : FormulaN L) : Prop where
  /-- Gamma_1 -> Delta_1, C is LK_bot-provable -/
  left_provable :
    lkBotProvable botP hBotArity
      { antecedent := p.gamma1
        succedent := p.delta1 ++ [C] }
  /-- C, Gamma_2 -> Delta_2 is LK_bot-provable -/
  right_provable :
    lkBotProvable botP hBotArity
      { antecedent := [C] ++ p.gamma2
        succedent := p.delta2 }
  /-- All predicate symbols in C EXCEPT ⊥ occur in both sides of the
      partition. Textbook Lem 6.5.2(ii) explicitly excludes ⊥: "all
      predicate symbols (except for ⊥)". Without this exception the
      axiom case C = ⊥ would fail its own pred_common obligation. -/
  pred_common : ∀ P, P ∈ formulaPredSymbolsN C → P ≠ botP →
    P ∈ listFormulaPredSymbols (p.gamma1 ++ p.delta1) ∧
    P ∈ listFormulaPredSymbols (p.gamma2 ++ p.delta2)
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
  /-- If all partition formulas have no eq_, the interpolant has no eq_ -/
  no_eq : (∀ A ∈ p.gamma1 ++ p.delta1 ++ p.gamma2 ++ p.delta2, formulaNoEq A) →
    formulaNoEq C

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

end LCS.CutElim.Interpolation
end
