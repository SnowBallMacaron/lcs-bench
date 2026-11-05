import LCS.CutElim.Interpolation.ConstantSubstitution

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











helper theorem Interpolation.formulaBV_formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) :
    formulaBVN (formulaSubstConst A z c) = formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => rfl
  | eq_ _ t1 t2 => rfl
  | conj A B ihA ihB => simp only [formulaSubstConst, formulaBVN, ihA, ihB]
  | disj A B ihA ihB => simp only [formulaSubstConst, formulaBVN, ihA, ihB]
  | impl A B ihA ihB => simp only [formulaSubstConst, formulaBVN, ihA, ihB]
  | neg A ih => simp only [formulaSubstConst, formulaBVN, ih]
  | all w A ih => simp only [formulaSubstConst, formulaBVN, ih]
  | ex w A ih => simp only [formulaSubstConst, formulaBVN, ih]



end LCS.CutElim.Interpolation

end
