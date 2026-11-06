import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Helper: Skolem form is in Skolem normal form
-- ===================================================================

/-- Helper: lifting a formula into the Skolem-extended language preserves
NNF. Term-level rewrapping does not disturb the formula-level shape, so
the clauses defining `isNNF` (atomic, neg-atomic, conj, disj, all, ex)
each match before and after the lift. -/
theorem liftFormulaSkolem_isNNF {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    A.isNNF → (liftFormulaSkolem (skolemRank := skolemRank) A).isNNF := by
-- BEGIN PROOF
  intro h
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg B _ =>
    cases B with
    | predN _ _ => exact trivial
    | eq_ _ _ _ => exact trivial
    | _ => exact h.elim
  | conj _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl _ _ _ _ => exact h.elim
  | all _ _ ih => exact ih h
  | ex _ _ ih => exact ih h

/-- The exact allocation traversal preserves NNF and eliminates every
existential on any successful descriptor-count-sized run. -/
theorem skolemFormExactAux_shape_nnf {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      FormulaN.isNNF B ∧ isSkolemNormalFormShape B := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨trivial, trivial⟩
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨trivial, trivial⟩
    | .neg B, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg B) scope [] =
            some (.neg B, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      cases B with
      | predN _ _ =>
        exact ⟨trivial, by
          simp [isSkolemNormalFormShape, FormulaN.isAtomic]⟩
      | eq_ _ _ _ =>
        exact ⟨trivial, by
          simp [isSkolemNormalFormShape, FormulaN.isAtomic]⟩
      | _ => exact hNNF.elim
    | .conj A B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        skolemFormExactAux_result S _ A scope
          (indices.take (skolemDescriptorCount A)) rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B scope
          (indices.drop (skolemDescriptorCount A)) rfl hRightLength
      have hPropA :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          A' _ rfl hNNF.1 hLeftLength hA'
      have hPropB :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          B' _ rfl hNNF.2 hRightLength hB'
      have hCanonical :
          skolemFormExactAux S (.conj A B) scope indices =
            some (.conj A' B',
              skolemDescriptorCount A + skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hA', hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨⟨hPropA.1, hPropB.1⟩, ⟨hPropA.2, hPropB.2⟩⟩
    | .disj A B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        skolemFormExactAux_result S _ A scope
          (indices.take (skolemDescriptorCount A)) rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B scope
          (indices.drop (skolemDescriptorCount A)) rfl hRightLength
      have hPropA :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          A' _ rfl hNNF.1 hLeftLength hA'
      have hPropB :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          B' _ rfl hNNF.2 hRightLength hB'
      have hCanonical :
          skolemFormExactAux S (.disj A B) scope indices =
            some (.disj A' B',
              skolemDescriptorCount A + skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hA', hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨⟨hPropA.1, hPropB.1⟩, ⟨hPropA.2, hPropB.2⟩⟩
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount B := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B (scope ++ [x])
          indices rfl hBodyLength
      have hPropB :=
        ih _ qB B (scope ++ [x]) indices B' _
          rfl hNNF hBodyLength hB'
      have hCanonical :
          skolemFormExactAux S (.all x B) scope indices =
            some (.all x B', skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hPropB
    | .ex x B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount B := by
          simp [skolemDescriptorCount] at hLength
          omega
        let BSub := formulaSubstN B (exactSkolemTerm S i) x
        have qBSub : formulaQuantCount BSub < m := by
          simp only [BSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF BSub :=
          isNNF_formulaSubstN B _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount BSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨B', hB'⟩ :=
          skolemFormExactAux_result S _ BSub scope rest rfl hSubLength
        have hPropB :=
          ih _ qBSub BSub scope rest B' _
            rfl hNNFSub hSubLength hB'
        have hCanonical :
            skolemFormExactAux S (.ex x B) scope (i :: rest) =
              some (B', skolemDescriptorCount BSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, BSub, hB']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hPropB

end LCS.Herbrand.SHGTheorem.Herbrand
end
