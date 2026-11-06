import LCS.FirstOrder.Semantics.Subformulae.SubstitutionInTautologies

section

namespace LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

helper /-- Example 5.3.4: The displayed proposition B is a tautology. -/
theorem examplePropFormula_5_3_4_tautology {α : Type} (P Q : α) :
    tautology (examplePropFormula_5_3_4 P Q) := by
  intro v
  exact ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

helper /-- Example 5.3.4: The specified substitution sends B to the displayed A. -/
theorem exampleInstance_5_3_4_subst {L : Language} (P Q : PS0 L)
    (C D : Formula L) (x y : Nat) (sigma : PS0 L → Formula L)
    (hP : sigma P = Formula.all x C)
    (hQ : sigma Q = Formula.ex y (Formula.conj C D)) :
    propSubst sigma (examplePropFormula_5_3_4 P Q) = exampleInstance_5_3_4 C D x y := by
  simp [examplePropFormula_5_3_4, propSubst, exampleInstance_5_3_4, hP, hQ]

proof_of exampleInstance_5_3_4_inPROPL := ⟨examplePropFormula_5_3_4 P Q, sigma, examplePropFormula_5_3_4_tautology P Q,
    exampleInstance_5_3_4_subst P Q C D x y sigma hP hQ⟩

helper /-- Proof of Lemma 5.3.5: Evaluating a propositional substitution agrees
with the valuation that evaluates each substituted first-order formula. -/
theorem propSubst_correspondence {L : Language} (M : Structure L)
    (s : Assignment M) (sigma : PS0 L → Formula L)
    (B : PropFormulaOver (PS0 L)) :
    evalProp (fun p => formulaEval M (sigma p) s) B ↔
      formulaEval M (propSubst sigma B) s := by
  induction B with
  | fls => exact Iff.rfl
  | var p => exact Iff.rfl
  | neg B ih => exact not_congr ih
  | conj B C ihB ihC => exact and_congr ihB ihC
  | disj B C ihB ihC => exact or_congr ihB ihC
  | impl B C ihB ihC => exact imp_congr ihB ihC
  | equiv_ B C ihB ihC => exact iff_congr ihB ihC

proof_of propInstanceValid := by
  rintro ⟨B, sigma, hValid, rfl⟩ M s
  exact (propSubst_correspondence M s sigma B).mp
    (hValid (fun p => formulaEval M (sigma p) s))

end LCS.FirstOrder.Semantics.Subformulae

end
