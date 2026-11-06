import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables.ProofsStamp

-- END PROOF
-- END PROOF

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

/-- Lemma 6.4.3 (companion): Collect all eigenvariables from a G1nnf proof tree. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def eigenvariables {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → Set Nat
  | _, _, .axiom_ _ _ _ _ _ => fun _ => False
  | _, _, .onePremise rule _ _ _ _ sub => fun v =>
    (match rule with
     | .allRight _ _ y => v = y
     | .exLeft _ _ y => v = y
     | _ => False) ∨ eigenvariables sub v
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 => fun v =>
    (match rule with
     | .allRight _ _ y => v = y
     | .exLeft _ _ y => v = y
     | _ => False) ∨ eigenvariables sub1 v ∨ eigenvariables sub2 v

end G1nnfProofTree

theorem G1nnfProofTree.eigenvariables_onePremise {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (v : Nat) :
    (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub).eigenvariables v =
      ((match rule with
        | .allRight _ _ ev => v = ev
        | .exLeft _ _ ev => v = ev
        | _ => False) ∨ sub.eigenvariables v) := by
  cases rule <;> first | rfl | omega

theorem G1nnfProofTree.eigenvariables_twoPremise {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (v : Nat) :
    (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2).eigenvariables v =
      ((match rule with
        | .allRight _ _ ev => v = ev
        | .exLeft _ _ ev => v = ev
        | _ => False) ∨ sub1.eigenvariables v ∨ sub2.eigenvariables v) := by
  cases rule <;> first | rfl | omega

namespace G1nnfProofTree

theorem ruleEigenvariable_mem_variableSupport {L : Language}
    (rule : G1nnfRule L) (w : Nat)
    (hw :
      match rule with
      | .allRight _ _ ev => w = ev
      | .exLeft _ _ ev => w = ev
      | _ => False) :
    w ∈ rule.variableSupport := by
  cases rule <;>
    simp_all [G1nnfRule.variableSupport, LCS.Finset.mem_insert]

theorem eigenvariables_mem_variableSupport {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (w : Nat) :
    T.eigenvariables w → w ∈ T.variableSupport := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      intro hw
      exact hw.elim
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      intro hw
      rw [G1nnfProofTree.eigenvariables_onePremise] at hw
      rcases hw with hRule | hSub
      · exact
          G1nnfProofTree.variableSupport_onePremise_of_rule
            rule Γ Δ hPrem hAC sub w
              (ruleEigenvariable_mem_variableSupport rule w hRule)
      · exact
          G1nnfProofTree.variableSupport_onePremise_of_subtree
            rule Γ Δ hPrem hAC sub w (ih hSub)
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      intro hw
      rw [G1nnfProofTree.eigenvariables_twoPremise] at hw
      rcases hw with hRule | hSubs
      · exact
          G1nnfProofTree.variableSupport_twoPremise_of_rule
            rule Γ Δ hPrem hAC sub1 sub2 w
              (ruleEigenvariable_mem_variableSupport rule w hRule)
      · rcases hSubs with hSub1 | hSub2
        · exact
            G1nnfProofTree.variableSupport_twoPremise_of_left_subtree
              rule Γ Δ hPrem hAC sub1 sub2 w (ih1 hSub1)
        · exact
            G1nnfProofTree.variableSupport_twoPremise_of_right_subtree
              rule Γ Δ hPrem hAC sub1 sub2 w (ih2 hSub2)

def ruleEigenlabel {L : Language} :
    G1nnfRule L → Option Nat
  | .allRight _ _ ev => some ev
  | .exLeft _ _ ev => some ev
  | _ => none

theorem ruleEigenlabel_eq_some_of_eigenMatch {L : Language}
    (rule : G1nnfRule L) (w : Nat)
    (hw :
      match rule with
      | .allRight _ _ ev => w = ev
      | .exLeft _ _ ev => w = ev
      | _ => False) :
    ruleEigenlabel rule = some w := by
  cases rule <;> simp_all [ruleEigenlabel]

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end
