import LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Syntax.Variables

proof_of exampleFormulaA_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaA_5_2_3, exampleFormulaB_5_2_3, exampleFormulaC_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega

proof_of exampleFormulaB_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaB_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega

proof_of exampleFormulaC_5_2_3_fv := by
  funext n
  apply propext
  dsimp [exampleFormulaC_5_2_3, formulaFV, termFV, exampleLang_5_2_3,
    Set.iUnion, Set.union, Set.diff, Set.singleton]
  simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
  omega

end LCS.FirstOrder.Syntax.Variables
