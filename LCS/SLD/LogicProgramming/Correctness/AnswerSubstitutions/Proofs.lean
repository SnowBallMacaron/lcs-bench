import LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions

section

namespace LCS.SLD.LogicProgramming.Correctness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.SLD.FirstOrder

open LCS.SLD.LogicProgramming

proof_of exIndefiniteAnswerValidity := by
  classical
  intro M hSat s
  change ¬ M.interpPred .rocksinger (fun _ => s 22) ∨ M.interpPred .rich (fun _ => s 22)
  by_cases hRock : M.interpPred .rocksinger (fun _ => s 22)
  · right
    have hRule := hSat (fun _ => s 22) ex954_C4
      (by
        change ex954_C4 ∈ [ex954_C1, ex954_C2, ex954_C3, ex954_C4, exCorrectnessGoalClause1]
        simp)
    change (∀ a ∈ [mkCorrAtom .rocksinger (.var 0)],
      formulaEvalN M a.toFormula (fun _ => s 22)) →
      M.interpPred .rich (fun _ => s 22) at hRule
    apply hRule
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact hRock
  · exact Or.inl hRock

helper theorem emptyClause_in_set_unsatisfiable {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (S : FOClause L hNoEq → Prop) (hEmpty : S []) :
    (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq)) S := by
-- BEGIN PROOF
  intro ⟨M, hSat⟩
  exact universalClosure_nil_validIn_false hNoEq M A []
    (FOClause.universalClosure_of_validIn hNoEq M [] (hSat [] hEmpty) A [])







helper def collectDerivClauses {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → List (FOHornClause L hNoEq)
  | _, .init _ _ => []
  | _, .step prev clause _ _ _ _ _ _ _ _ _ _ =>
    clause :: (collectDerivClauses (hNoEq := hNoEq)) prev

helper theorem collectDerivClauses_in_D {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    ∀ c ∈ (collectDerivClauses (hNoEq := hNoEq)) d, c ∈ D := by
-- BEGIN PROOF
  induction d with
  | init _ _ => intro c hc; simp [collectDerivClauses] at hc
  | step _ clause hClause _ _ _ _ _ _ _ _ _ ih =>
    intro c hc
    simp [collectDerivClauses] at hc
    rcases hc with rfl | hc
    · exact hClause
    · exact ih c hc









helper theorem substFormula_comp {L : Language} (A : FormulaN L) (sigma theta : Nat → Term L) :
    substLit.substFormula theta (substLit.substFormula sigma A) =
    substLit.substFormula (SubstitutionCore.substCompose theta sigma) A := by
-- BEGIN PROOF
  induction A with
  | predN P args =>
    simp [substLit.substFormula]; funext i
    exact SubstitutionCore.termSubstAll_compose (args i) sigma theta
  | eq_ _ t1 t2 =>
    simp [substLit.substFormula]
    exact ⟨SubstitutionCore.termSubstAll_compose t1 sigma theta,
           SubstitutionCore.termSubstAll_compose t2 sigma theta⟩
  | neg _ ih => simp [substLit.substFormula, ih]
  | conj _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | disj _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | impl _ _ ihA ihB => simp [substLit.substFormula, ihA, ihB]
  | all _ _ ih => simp [substLit.substFormula, ih]
  | ex _ _ ih => simp [substLit.substFormula, ih]

























end LCS.SLD.LogicProgramming.Correctness

end
