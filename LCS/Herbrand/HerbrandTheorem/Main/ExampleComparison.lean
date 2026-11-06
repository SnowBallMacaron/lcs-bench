import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.HerbrandTheorem.Main.Example
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.ExampleComparison.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Main.ExampleComparison
    Chapter 7, Section 5.4: the end of Example 7.5.3. The reconstructed proof
    agrees with the proof of Example 7.3.4 under the displayed renaming of
    variables (w to x1, v to y, u to z).

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

/-- Example 7.5.3: the displayed comparison renaming w↦x₁, v↦y, u↦z.
Original binder names 0–6 and all other variables are fixed. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExRestoreVariables : Substitution herbrandExLang
  | 9 => .var 4
  | 8 => .var 1
  | 7 => .var 3
  | x => .var x

/-- Example 7.5.3: the complete seven-quantifier suffix, including its twelve
exchanges and every boundary through the midsequent, agrees with Example 7.3.4
under the displayed renaming. Quantifier binders agree exactly; eigenvariables
and instantiating terms agree after renaming. This compares two fixed proofs. -/
@[attach_debt, blueprint "chap7__example_7_5_3"]
theorem herbrandExSuffixRenamed :
    (∀ d ≤ 19,
      ((LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt
        herbrandExPrefix7 (List.replicate d 0)).map (fun node =>
          (Sequent.mk
            (node.1.antecedent.map (Substitution.applyFormula herbrandExRestoreVariables))
            (node.1.succedent.map (Substitution.applyFormula herbrandExRestoreVariables))))) =
      ((LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt
        midsequentExampleTree (List.replicate d 0)).map (fun node =>
          (Sequent.mk
            (node.1.antecedent.map (fun A => herbrandExFromSkolemFormula (skolemExampleLiftFormula A)))
            (node.1.succedent.map (fun A => herbrandExFromSkolemFormula (skolemExampleLiftFormula A))))))) ∧
    (∀ d < 19,
      match LCS.Herbrand.SharpenedHauptsatz.Permutability.lkInferenceAt herbrandExPrefix7 (List.replicate d 0),
        LCS.Herbrand.SharpenedHauptsatz.Permutability.lkInferenceAt midsequentExampleTree (List.replicate d 0) with
      | some (.one r), some (.one q) => r.ctorIdx = q.ctorIdx ∧
        match r, q with
        | .allRight y x _ _ _ _ _, .allRight z w _ _ _ _ _ =>
          herbrandExRestoreVariables y = .var z ∧ x = w
        | .exRight t x _ _ _ _, .exRight u w _ _ _ _ =>
          Substitution.applyTerm herbrandExRestoreVariables t =
            herbrandExFromSkolemTerm (skolemExampleLiftTerm u) ∧ x = w
        | _, _ => True
      | _, _ => False)

end LCS.Herbrand.HerbrandTheorem.Main
