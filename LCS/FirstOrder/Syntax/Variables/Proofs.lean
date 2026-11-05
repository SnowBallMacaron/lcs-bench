import LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Syntax.Variables

proof_of fv_bv_overlap_possible := by
  rcases h with hEq | ⟨P, hP⟩
  · let atom : Formula L := Formula.eq_ hEq (Term.var 0) (Term.var 0)
    exact ⟨Formula.conj atom (Formula.all 0 atom), 0,
      Or.inl (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · let atom : Formula L := Formula.predN P hP (fun _ => Term.var 0)
    exact ⟨Formula.conj atom (Formula.all 0 atom), 0,
      Or.inl ⟨⟨0, hP⟩, rfl⟩, Or.inr (Or.inr rfl)⟩


proof_of exampleFormulaA_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaA_5_2_3, exampleFormulaB_5_2_3, exampleFormulaC_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega


helper /-- Example 5.2.3: BV(A) = {x, y}, with x = 0 and y = 1. -/
theorem exampleFormulaA_5_2_3_bv :
    formulaBV exampleFormulaA_5_2_3 = Set.singleton 0 ∪ Set.singleton 1 := by
  funext n
  apply propext
  simp [exampleFormulaA_5_2_3, exampleFormulaB_5_2_3, exampleFormulaC_5_2_3, formulaBV,
    Set.union, Set.singleton, Set.empty]

proof_of exampleFormulaB_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaB_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega


helper /-- Example 5.2.3: BV(B) = {x}, with x = 0 and y = 1. -/
theorem exampleFormulaB_5_2_3_bv :
    formulaBV exampleFormulaB_5_2_3 = Set.singleton 0 := by
  funext n
  apply propext
  simp [exampleFormulaB_5_2_3, formulaBV,
    Set.union, Set.singleton, Set.empty]

proof_of exampleFormulaC_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaC_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega


helper /-- Example 5.2.3: BV(C) = {x, y}, with x = 0 and y = 1. -/
theorem exampleFormulaC_5_2_3_bv :
    formulaBV exampleFormulaC_5_2_3 = Set.singleton 0 ∪ Set.singleton 1 := by
  funext n
  apply propext
  simp [exampleFormulaC_5_2_3, formulaBV,
    Set.union, Set.singleton, Set.empty]

end LCS.FirstOrder.Syntax.Variables
