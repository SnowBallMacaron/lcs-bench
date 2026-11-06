import LCS.Herbrand.SHGTheorem.Main.PrenexCorollary

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

proof_of shgCorollary_prenex := by
  have hSourcePrenex : isPrenex spec.source := by
    rw [← hSource]
    exact _hPrenex
  have hSKUniversal :
      UniversalPrenexFormula (SK spec) :=
    skolemForm_universalPrenex_of_source_prenex
      spec hSourcePrenex
  have hSKNormal := skolemForm_isSkolemNormalForm' spec
  have hSKDistinct : distinctQuantifierBindings (SK spec) :=
    hSKNormal.2.1.2
  have hSKClosed : FormulaN.isClosed (SK spec) :=
    hSKNormal.2.2
  constructor
  · intro hUnsat
    obtain ⟨C, ci, hCiSource, hCiFormula, hCiWF, hCUnsat⟩ :=
      (shgTheorem_unsat spec A hSource hConst).mp hUnsat
    have hCiUniversal : UniversalPrenexFormula ci.source := by
      rw [hCiSource]
      exact hSKUniversal
    have hCiNNF : FormulaN.isNNF ci.source := by
      rw [hCiSource]
      exact skolemForm_isNNF' spec
    have hCiDistinct : distinctQuantifierBindings ci.source := by
      rw [hCiSource]
      exact hSKDistinct
    have hCiClosed : FormulaN.isClosed ci.source := by
      rw [hCiSource]
      exact hSKClosed
    have hConjunction :=
      cInstance_toFormula_isFiniteGroundConjunctionOfMatrix
        ci hCiWF hCiUniversal hCiNNF hCiDistinct hCiClosed
    rw [hCiFormula, hCiSource] at hConjunction
    exact ⟨C, hConjunction, hCUnsat⟩
  · rintro ⟨F, ⟨_, _, _, instances, hFlattening⟩, hFUnsat⟩
    intro hASat
    apply hFUnsat
    have hSKSat : satisfiableN (SK spec) :=
      (skolem_form_sat_iff spec A hSource (SK spec) rfl).mp hASat
    obtain ⟨M, s, hSKEval⟩ := hSKSat
    refine ⟨M, s, (hFlattening.formulaEvalN_iff_all_leaves M s).mpr ?_⟩
    intro f hf
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hf
    exact universalPrenex_eval_groundSubstitution
      (SK spec) hSKUniversal hSKClosed M s hSKEval
      g.substitution g.termsClosed /- ATTACH-BLOCKER: private name in relocated declaration -/

end LCS.Herbrand.SHGTheorem.Main
end
