import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
open LCS.FirstOrder.Equality

-- Helper: equality axiom sequents are valid
-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
theorem equalityAxiomValid {L : Language} (hL : L.hasEquality = true)
    (ax : LKeEqualityAxiom L) :
    sequentValid (ax.toSequent hL) := by
-- BEGIN PROOF
  cases ax with
  | refl t =>
    intro M s _
    exact ⟨FormulaN.eq_ hL t t, List.Mem.head _, eqReflValid hL t M s⟩
  | funcCong f ss ts =>
    intro M s hant
    refine ⟨FormulaN.eq_ hL (Term.func f ss) (Term.func f ts), List.Mem.head _, ?_⟩
    simp only [formulaEvalN, termEval]
    congr 1; funext i
    have := hant (FormulaN.eq_ hL (ss i) (ts i)) (by
      simp only [LKeEqualityAxiom.toSequent, List.mem_map]
      exact ⟨i, List.mem_finRange i, rfl⟩)
    simp only [formulaEvalN] at this; exact this
  | predCong P ss ts =>
    intro M s hant
    refine ⟨FormulaN.predN P ts, List.Mem.head _, ?_⟩
    simp only [formulaEvalN]
    have hPss : formulaEvalN M (FormulaN.predN P ss) s :=
      hant (FormulaN.predN P ss) (by
        simp only [LKeEqualityAxiom.toSequent]
        exact List.mem_append_right _ (List.Mem.head _))
    simp only [formulaEvalN] at hPss
    have heqs : ∀ i, termEval M s (ss i) = termEval M s (ts i) := by
      intro i
      have := hant (FormulaN.eq_ hL (ss i) (ts i)) (by
        simp only [LKeEqualityAxiom.toSequent]
        apply List.mem_append_left
        simp only [List.mem_map]
        exact ⟨i, List.mem_finRange i, rfl⟩)
      simp only [formulaEvalN] at this; exact this
    have : (fun i => termEval M s (ts i)) = (fun i => termEval M s (ss i)) :=
      funext (fun i => (heqs i).symm)
    rw [this]; exact hPss
  | eqCong s1 s2 t1 t2 =>
    intro M s hant
    refine ⟨FormulaN.eq_ hL t1 t2, List.Mem.head _, ?_⟩
    have h1 := hant (FormulaN.eq_ hL s1 t1) (by
      simp [LKeEqualityAxiom.toSequent])
    have h2 := hant (FormulaN.eq_ hL s2 t2) (by
      simp [LKeEqualityAxiom.toSequent])
    have h3 := hant (FormulaN.eq_ hL s1 s2) (by
      simp [LKeEqualityAxiom.toSequent])
    simp only [formulaEvalN] at h1 h2 h3 ⊢
    rw [← h1, h3, h2]

-- Helper: LKe soundness -- every LKe tree's conclusion is valid
-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
theorem lkeProofTree_valid {L : Language} {s : Sequent L}
    (T : LKeProofTree s) :
    sequentValid s := by
-- BEGIN PROOF
  induction T with
  | axiom_ s hAx =>
    exact lemma_6_2_1_axioms_valid s hAx
  | eqAxiom hL ax =>
    exact equalityAxiomValid hL ax
  | onePremise rule _ ih =>
    exact lemma_6_2_1_rules1_preserve_validity rule ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact lemma_6_2_1_rules2_preserve_validity rule ih1 ih2

-- Soundness at the lkeProvable level
-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.LKe.Equivalence.Validity, LCS.Herbrand.HerbrandTheorem.Part2
theorem lkeProvable_valid {L : Language}
    (s : Sequent L) (h : lkeProvable s) :
    sequentValid s := by
-- BEGIN PROOF
  obtain ⟨T⟩ := h
  exact lkeProofTree_valid T

end LCS.CutElim.LKe.Equivalence
end
