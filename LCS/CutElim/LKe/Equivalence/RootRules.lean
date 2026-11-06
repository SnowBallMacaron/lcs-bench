import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.CutElim.LKe.Equivalence.RootRules.ProofsStamp

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge

-- ===================================================================
-- Lemma 6.3.2 (required def): rootIsConjRight
-- ===================================================================
/-- Lemma 6.3.2 (required def): Predicate asserting that the root
rule of the proof tree is conjunction-right applied to the formula
A /\ B in the succedent, with A and B as the given arguments. The
requested contexts are compared with the rule constructor's indexed
prefix and suffix around that principal occurrence. -/
@[blueprint "chap6__lemma_6_3_2"]
def rootIsConjRight {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) (A B : FormulaN L)
    (Γ Δ Λ : List (FormulaN L)) : Prop :=
  match T with
  | .base (.twoPremise (.conjRight Γ' Δ' Λ' A' B') _ _) =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | .twoPremise (.conjRight Γ' Δ' Λ' A' B') _ _ =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | _ => False

-- ===================================================================
-- Lemma 6.3.2 (required def): rootIsImplLeft
-- ===================================================================
/-- Lemma 6.3.2 (required def): Predicate asserting that the root
rule of the proof tree is implication-left applied to the formula
A implies B in the antecedent, with A and B as the given arguments.
The requested contexts are compared with the rule constructor's indexed
prefix and suffix around that principal occurrence. -/
@[blueprint "chap6__lemma_6_3_2"]
def rootIsImplLeft {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) (A B : FormulaN L)
    (Γ Δ Λ : List (FormulaN L)) : Prop :=
  match T with
  | .base (.twoPremise (.implLeft Γ' Δ' Λ' A' B') _ _) =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | .twoPremise (.implLeft Γ' Δ' Λ' A' B') _ _ =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | _ => False

end LCS.CutElim.LKe.Equivalence
end
