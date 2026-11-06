import LCS.CutElim.Robinson

namespace LCS.CutElim.Robinson

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax (peanoLanguage)

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.FirstOrder.Completeness.MetaTheorems

open LCS.FirstOrder.Equality.MetaTheorems

open LCS.FirstOrder.Equality

open Classical

open LCS.FirstOrder.SemanticsN

helper /-- When the amalgamated language has a formula, inconsistency of
setUnion S1 S2 yields a validity witness. -/
theorem setUnion_inconsistent_valid {L L1 L2 : Language}
    {hI : LanguageIntersection L L1 L2}
    [Nonempty (FormulaN (languageAmalgam hI))]
    {S1 : Set (FormulaN L1)} {S2 : Set (FormulaN L2)}
    (h : ¬isConsistentSetUnified (setUnion hI S1 S2)) :
    ∃ (cs : List (FormulaN (languageAmalgam hI))),
      (∀ c, c ∈ cs → setUnion hI S1 S2 c) ∧
      sequentValid (Sequent.mk cs []) := by
-- BEGIN PROOF
  unfold isConsistentSetUnified at h
  split at h <;> rename_i heq
  · -- hasEquality = true: inconsistency via G_=-provability
    have hEmpty : ¬ isConsistentSetEqEmptySucc heq (setUnion hI S1 S2) :=
      fun hEmpty => h ((isConsistentSetEq_iff_emptySucc heq
        (setUnion hI S1 S2)).mpr hEmpty)
    obtain ⟨cs, hcs⟩ := Classical.not_forall.mp hEmpty
    obtain ⟨hmem, hprov⟩ := Classical.not_imp.mp hcs
    exact ⟨cs, hmem, soundnessGEq heq _
      (Classical.byContradiction fun hc => hprov hc)⟩
  · -- hasEquality = false: inconsistency via G-provability
    have hEmpty : ¬ LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSetEmptySucc
        (setUnion hI S1 S2) := fun hEmpty => h
      ((LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSet_iff_emptySucc
        (setUnion hI S1 S2)).mpr hEmpty)
    obtain ⟨cs, hcs⟩ := Classical.not_forall.mp hEmpty
    obtain ⟨hmem, hprov⟩ := Classical.not_imp.mp hcs
    exact ⟨cs, hmem, soundnessG_Ext _
      (Classical.byContradiction fun hc => hprov hc)⟩

proof_of robinson_joint_consistency := by
  -- BEGIN PROOF
    exact Classical.byContradiction fun hIncons => by
      letI : Nonempty (FormulaN (languageAmalgam hIntersect)) := ⟨Countable.enumerate 0⟩
      obtain ⟨cs, hcs_mem, hcs_valid⟩ := setUnion_inconsistent_valid hIncons
      have hsat : satisfiableSetN (setUnion hIntersect S1 S2) :=
        setUnion_satisfiable hIntersect hCase S1 S2
          hSent1 hSent2 hCons1 hCons2 hComplete
      obtain ⟨M, s, hMs⟩ := hsat
      obtain ⟨B, hB, _⟩ := hcs_valid M s
        (fun A hA => hMs A (hcs_mem A hA))
      simp at hB

end LCS.CutElim.Robinson
