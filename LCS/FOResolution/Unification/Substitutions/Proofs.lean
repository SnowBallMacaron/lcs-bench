import LCS.FOResolution.Unification.Substitutions

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

proof_of termSubstAll_compose := SubstitutionCore.termSubstAll_compose t sigma.map theta.map

proof_of substCompose_assoc := by
  apply FiniteSubstitution.ext
  · exact List.append_assoc _ _ _
  · intro x
    exact termSubstAll_compose (sigma x) theta rho

end LCS.FOResolution.Unification
end
