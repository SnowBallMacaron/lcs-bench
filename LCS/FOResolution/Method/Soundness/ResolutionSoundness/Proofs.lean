import LCS.FOResolution.Method.Soundness.ResolutionSoundness

section
namespace LCS.FOResolution.Method.Soundness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method

proof_of resolution_soundness_fo := by
  obtain ⟨T, _hD, hLeaves, hWF, hEmpty⟩ := hRef
  intro ⟨M, hSat⟩
  have hValid := tree_label_valid hNoEq S M hSat T hLeaves hWF
  obtain ⟨lit, hMem, _⟩ := hValid (fun _ => Classical.choice M.carrierNonempty)
  rw [hEmpty] at hMem
  exact List.not_mem_nil hMem

end LCS.FOResolution.Method.Soundness
end
