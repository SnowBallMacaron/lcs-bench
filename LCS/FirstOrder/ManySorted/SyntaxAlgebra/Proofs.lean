import LCS.FirstOrder.ManySorted.SyntaxAlgebra

namespace LCS.FirstOrder.ManySorted.SyntaxAlgebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.Basic (FirstOrderLanguage)

open LCS.FirstOrder.Syntax.Algebra (SyntaxOperation FirstOrderSort)

proof_of msAmbientString_cons := by
  cases s <;> simp [msAmbientStringAt, msStringHeadSort, hrank]

proof_of msAmbientString_nonempty_carrier := by
  cases s with
  | none => exact ⟨msAmbientBottom L⟩
  | some s => exact ⟨msAmbientVariable L s 0⟩

proof_of msGeneratedString_least := by
  induction h with
  | var s i => exact variables s i
  | operation op args _ ih => exact closed op args ih

proof_of msString_free_generation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s w h
    cases s with
    | none => exact False.elim h
    | some s =>
      obtain ⟨i, rfl⟩ := h
      exact .var s i
  · intro op _ args h
    exact .operation op args h
  · intro D hv hc s w h
    exact msGeneratedString_least D (fun s i => hv _ _ ⟨i, rfl⟩)
      (fun op args hg => hc op True.intro args hg) h
  · -- REPAIR(T10-48): proof pending
    sorry

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
