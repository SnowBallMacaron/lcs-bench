import LCS.FOResolution.Method.Completeness.ResolutionCompleteness

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical

proof_of resolution_completeness_fo := by
  classical
  by_cases hEmpty : S []
  · let emptyTree : FOResolutionTree L hNoEq := .axiom_ []
    exact ⟨[emptyTree], emptyTree, rfl, hEmpty, True.intro, rfl⟩
  have hSource : ∃ C, S C := by
    apply Classical.byContradiction
    intro h
    apply hUnsat
    let M : Structure L := {
      carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => False
    }
    exact ⟨M, fun C hC => (h ⟨C, hC⟩).elim⟩
  obtain ⟨C, hC⟩ := hSource
  cases C with
  | nil => exact (hEmpty hC).elim
  | cons lit rest =>
    -- A literal of a source clause supplies the formula needed internally
    -- by the clause-sentence bridge.
    let A : FormulaN L := clauseToFormula.litToFormula hNoEq lit
    rcases (finite_unsatisfiable_empty_or_clauseSentence (hNoEq := by all_goals exact hNoEq))
        A S hFinite hUnsat with hEmpty | hCertificate
    · let emptyTree : FOResolutionTree L hNoEq := .axiom_ []
      exact ⟨[emptyTree], emptyTree, rfl, hEmpty, True.intro, rfl⟩
    · obtain ⟨head, tail, hP⟩ := hCertificate
      have hProv :
          G1nnfProvableSet hNoEq
            (({(clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail} : LCS.Finset (FormulaN L)),
             (∅ : LCS.Finset (FormulaN L))) :=
        LCS.Herbrand.SHGTheorem.Main.g1nnf_provable_of_unsat_closed_nnf_noeq
          hNoEq
          ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
          hP.sentence_nnf
          hP.sentence_closed
          hP.sentence_unsatisfiable
      have hAllNNF :
          allSequentFormulaeAreNNF
            (({(clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail} : LCS.Finset (FormulaN L)),
             (∅ : LCS.Finset (FormulaN L))) := by
        constructor
        · intro F hF
          rw [(LCS.Finset.mem_singleton F
            ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)).mp hF]
          exact hP.sentence_nnf
        · intro F hF
          exact (LCS.Finset.not_mem_empty hF).elim
      have hAllRectified :
          AllRectified
            (({(clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail} : LCS.Finset (FormulaN L)),
             (∅ : LCS.Finset (FormulaN L))) := by
        constructor
        · intro F hF
          rw [(LCS.Finset.mem_singleton F
            ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)).mp hF]
          exact hP.sentence_rectified
        · intro F hF
          exact (LCS.Finset.not_mem_empty hF).elim
      have hCross : LCS.CutElim.Hauptsatz.finsetCrossNoFreeBound
          ({(clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail} : LCS.Finset (FormulaN L)) ∅ := by
        intro x hx
        obtain ⟨F, hF, hxF⟩ := hx
        rcases hF with hF | hF
        · have hEq := (LCS.Finset.mem_singleton F
            ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)).1 hF
          subst F
          rw [hP.sentence_closed] at hxF
          exact hxF.elim
        · exact (LCS.Finset.not_mem_empty hF).elim
      obtain ⟨T, mid, _hCutFree, _hPure, hMid⟩ :=
        sharpenedHauptsatz_G2nnf
          (L := L) hNoEq
          (({(clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L)))
          hAllNNF hAllRectified hCross hProv
      exact (clauseSentence_midsequent_resolution_refutation (hNoEq := by all_goals exact hNoEq))
        A S head tail hP mid hMid

end LCS.FOResolution.Method.Completeness
end
