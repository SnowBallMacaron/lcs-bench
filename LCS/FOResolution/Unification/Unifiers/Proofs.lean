import LCS.FOResolution.Unification.Unifiers

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

proof_of mostCommonInstance_eq := by
  exact h.1.2 _ _ (List.head_mem h.1.1) ht

end LCS.FOResolution.Unification
end
