import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand

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

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- Skolemization preserves a prenex source's prefix shape while
eliminating every existential prefix entry. -/
theorem skolemForm_universalPrenex_of_source_prenex
    {L : Language} (spec : SkolemSpec L)
    (hPrenex : isPrenex spec.source) :
    UniversalPrenexFormula (SK spec) := by
  have hLiftQF :
      ∀ A : FormulaN L,
        FirstOrder.SemanticsN.isQuantifierFree A →
        FirstOrder.SemanticsN.isQuantifierFree
          (liftFormulaSkolem
            (skolemRank := spec.skolemRank) A) := by
    intro A hQF
    induction A with
    | predN _ _ => trivial
    | eq_ _ _ _ => trivial
    | neg A ih => exact ih hQF
    | conj A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | disj A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | impl A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | all _ _ => exact hQF.elim
    | ex _ _ => exact hQF.elim
  have hLiftPrenex :
      ∀ A : FormulaN L,
        isPrenex A →
        isPrenex
          (liftFormulaSkolem
            (skolemRank := spec.skolemRank) A) := by
    intro A hA
    induction A with
    | predN _ _ => exact hA
    | eq_ _ _ _ => exact hA
    | neg A _ => exact hLiftQF (.neg A) hA
    | conj A B _ _ => exact hLiftQF (.conj A B) hA
    | disj A B _ _ => exact hLiftQF (.disj A B) hA
    | impl A B _ _ => exact hLiftQF (.impl A B) hA
    | all _ A ih => exact ih hA
    | ex _ A ih => exact ih hA
  have hQFDescriptorCount :
      ∀ A : FormulaN spec.language,
        FirstOrder.SemanticsN.isQuantifierFree A →
        skolemDescriptorCount A = 0 := by
    intro A hQF
    induction A with
    | predN _ _ => rfl
    | eq_ _ _ _ => rfl
    | neg _ _ => rfl
    | conj A B ihA ihB =>
      simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
    | disj A B ihA ihB =>
      simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
    | impl _ _ _ _ => rfl
    | all _ _ => exact hQF.elim
    | ex _ _ => exact hQF.elim
  have hTraversalPrenex :
      ∀ (m : Nat) (A : FormulaN spec.language)
        (scope : List Nat) (indices : List (Fin spec.n))
        (B : FormulaN spec.language) (used : Nat),
        formulaQuantCount A = m →
        isPrenex A →
        indices.length = skolemDescriptorCount A →
        skolemFormExactAux spec A scope indices =
          some (B, used) →
        isPrenex B := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro A scope indices B used hCount hAPrenex hLength hRun
      cases A with
      | predN P ts =>
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (by
            simpa [skolemDescriptorCount] using hLength)
        subst indices
        simp only [skolemFormExactAux] at hRun
        cases hRun
        exact trivial
      | eq_ hEq t₁ t₂ =>
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (by
            simpa [skolemDescriptorCount] using hLength)
        subst indices
        simp only [skolemFormExactAux] at hRun
        cases hRun
        exact trivial
      | neg C =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.neg C) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.neg C) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.neg C) scope hZero
        have hEq : B = FormulaN.neg C :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | conj C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.conj C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.conj C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.conj C D) scope hZero
        have hEq : B = FormulaN.conj C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | disj C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.disj C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.disj C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.disj C D) scope hZero
        have hEq : B = FormulaN.disj C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | impl C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.impl C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.impl C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.impl C D) scope hZero
        have hEq : B = FormulaN.impl C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | all x C =>
        have hCountC : formulaQuantCount C < m := by
          simp [formulaQuantCount] at hCount
          omega
        have hLengthC :
            indices.length = skolemDescriptorCount C := by
          simpa [skolemDescriptorCount] using hLength
        have hRunTop := hRun
        simp only [skolemFormExactAux] at hRun
        generalize hRec :
            skolemFormExactAux spec C
              (scope ++ [x]) indices = rec at hRun
        cases rec with
        | none =>
          simp at hRun
        | some result =>
          obtain ⟨C', used'⟩ := result
          have hWrapped :
              skolemFormExactAux spec
                  (FormulaN.all x C) scope indices =
                some (FormulaN.all x C', used') := by
            simp [skolemFormExactAux, hRec]
          have hB : B = FormulaN.all x C' :=
            skolemFormExactAux_formula_unique hRunTop hWrapped
          subst B
          exact
            ih (formulaQuantCount C) hCountC C
              (scope ++ [x]) indices C' used' rfl
              hAPrenex hLengthC hRec
      | ex x C =>
        cases indices with
        | nil =>
          have hImpossible :
              0 = 1 + skolemDescriptorCount C := by
            simpa only [List.length_nil,
              skolemDescriptorCount] using hLength
          omega
        | cons i rest =>
          have hCountSub :
              formulaQuantCount
                  (formulaSubstN C
                    (exactSkolemTerm spec i) x) < m := by
            rw [formulaSubst_quantCount]
            simp [formulaQuantCount] at hCount
            omega
          have hLengthRest :
              rest.length =
                skolemDescriptorCount
                  (formulaSubstN C
                    (exactSkolemTerm spec i) x) := by
            rw [formulaSubstN_descriptorCount]
            simp only [List.length_cons,
              skolemDescriptorCount] at hLength
            omega
          have hPrenexSub :
              isPrenex
                (formulaSubstN C
                  (exactSkolemTerm spec i) x) :=
            isPrenex_formulaSubstN C
              (exactSkolemTerm spec i) x hAPrenex
          have hRunTop := hRun
          simp only [skolemFormExactAux, skolemSubst] at hRun
          generalize hRec :
              skolemFormExactAux spec
                (formulaSubstN C
                  (exactSkolemTerm spec i) x)
                scope rest = rec at hRun
          cases rec with
          | none =>
            simp at hRun
          | some result =>
            obtain ⟨C', used'⟩ := result
            have hWrapped :
                skolemFormExactAux spec
                    (FormulaN.ex x C) scope (i :: rest) =
                  some (C', used' + 1) := by
              simp [skolemFormExactAux, skolemSubst, hRec]
            have hB : B = C' :=
              skolemFormExactAux_formula_unique hRunTop hWrapped
            subst B
            exact
              ih _ hCountSub _ scope rest C' used' rfl
                hPrenexSub hLengthRest hRec
  let lifted :=
    liftFormulaSkolem
      (skolemRank := spec.skolemRank) spec.source
  have hLiftedPrenex : isPrenex lifted :=
    hLiftPrenex spec.source hPrenex
  have hSKPrenex : isPrenex (SK spec) :=
    hTraversalPrenex
      (formulaQuantCount lifted) lifted [] spec.indices
      (SK spec) spec.n rfl hLiftedPrenex
      spec.indices_length_eq_lifted_descriptorCount
      (skolemFormExactAux_top_formula_result spec)
  have hUniversalPrefix :
      ∀ B : FormulaN spec.language,
        isSkolemNormalFormShape B →
        ∀ p, p ∈ prenexPrefix B →
          p.1 = QuantifierKind.universal := by
    intro B
    induction B with
    | predN _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | eq_ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | neg _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | conj _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | disj _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | impl _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | all x C ih =>
      intro hShape p hp
      simp only [prenexPrefix, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih hShape p hp
    | ex _ _ _ =>
      intro hShape
      exact hShape.elim
  exact
    ⟨hSKPrenex,
      hUniversalPrefix (SK spec)
        (skolemForm_isSkolemNormalForm' spec).1⟩

open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem

end LCS.Herbrand.SHGTheorem.Main
end
