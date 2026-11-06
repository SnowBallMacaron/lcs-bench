import LCS.Herbrand.HerbrandTheorem.SigmaMatrix

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

proof_of sigmaMatrixTerm_mem := by
  unfold sigmaMatrixRequiredTerms
  apply List.mem_flatMap.mpr
  refine ⟨p, List.mem_ofFn.mpr ⟨p, rfl⟩, ?_⟩
  split <;> rename_i hp
  · exact List.mem_singleton.mpr rfl
  · cases h.symm.trans hp

end LCS.Herbrand.HerbrandTheorem
