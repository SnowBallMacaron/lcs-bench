import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz











































helper theorem formulaSubstN_neg {L : Language} (A : FormulaN L)
    (t : Term L) (y : Nat) :
    formulaSubstN (.neg A) t y = .neg (formulaSubstN A t y) := by
-- BEGIN PROOF
  simp [formulaSubstN]

helper theorem formulaSubstN_conj {L : Language} (A B : FormulaN L)
    (t : Term L) (y : Nat) :
    formulaSubstN (.conj A B) t y =
      .conj (formulaSubstN A t y) (formulaSubstN B t y) := by
-- BEGIN PROOF
  simp [formulaSubstN]

helper theorem formulaSubstN_disj {L : Language} (A B : FormulaN L)
    (t : Term L) (y : Nat) :
    formulaSubstN (.disj A B) t y =
      .disj (formulaSubstN A t y) (formulaSubstN B t y) := by
-- BEGIN PROOF
  simp [formulaSubstN]









helper /-- Lemma 6.4.3 (companion): eigenvariable is preserved by substRule
(helper used in `G1nnfProofTree.eigenvariables` computation and in the
substitution lemma 6.4.4). -/
theorem substRule_eigenvariable_eq {L : Language}
    (rule : G1nnfRule L) (t : Term L) (y v : Nat) :
    (match (substRule t y rule) with
     | .allRight _ _ ev => v = ev
     | .exLeft _ _ ev => v = ev
     | _ => False) =
    (match rule with
     | .allRight _ _ ev => v = ev
     | .exLeft _ _ ev => v = ev
     | _ => False) :=
-- BEGIN PROOF
by
  cases rule with
  | allRight x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
  | exLeft x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
  | allLeft x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
  | exRight x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
  | axiomPosAtomic _ _ _ _ => rfl
  | axiomNegAtomic _ _ _ _ => rfl
  | axiomCompLeft _ _ _ _ => rfl
  | axiomCompRight _ _ _ _ => rfl
  | cut _ _ _ => rfl
  | conjLeft1 _ _ => rfl
  | conjLeft2 _ _ => rfl
  | conjRight _ _ => rfl
  | disjLeft _ _ => rfl
  | disjRight1 _ _ => rfl
  | disjRight2 _ _ => rfl















end LCS.CutElim.Hauptsatz

end
