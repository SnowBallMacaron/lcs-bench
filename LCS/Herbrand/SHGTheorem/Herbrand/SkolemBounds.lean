import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
import LCS.Herbrand.SHGTheorem.Herbrand.Provenance
import LCS.Herbrand.SHGTheorem.Herbrand.LowerTrace
import LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
import Attach
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds.ProofsStamp

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

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
/-- Helper: lifting preserves `distinctQuantifierBindings`. Structural
induction: the lift does not change formula-level structure (quantifiers,
connectives), and BV is preserved by `liftFormulaSkolem_formulaBVN`. -/
theorem liftFormulaSkolem_distinctQuantifierBindings {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L)
    (h : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (liftFormulaSkolem (skolemRank := skolemRank) A) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings] at *
    exact ih h
  | conj _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | disj _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | impl _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | all _ _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ih h.1, h.2⟩
  | ex _ _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ih h.1, h.2⟩

-- retained: used by LCS.SLD.FirstOrder.HashLanguage
/-- Helper: lifting preserves `isRectified`. -/
theorem liftFormulaSkolem_isRectified {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L)
    (h : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    LCS.FirstOrder.Semantics.Subformulae.isRectified
      (liftFormulaSkolem (skolemRank := skolemRank) A) :=
  ⟨liftFormulaSkolem_boundVarsFresh A h.1,
   liftFormulaSkolem_distinctQuantifierBindings A h.2⟩

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Conservative invariant for proofs about the legacy numeric-counter
`skolemFormAux`. It rules out that helper's empty-scope placeholder but
is intentionally not used by top-level `skolemForm`: requiring every
future rank to be zero at an empty outer scope is too strong for
existentials nested below later universal quantifiers. Exact descriptor
alignment replaces this invariant in all top-level results. -/
def noFallback {L : Language} (S : SkolemSpec L)
    (scope : List Nat) (i : Nat) (A : FormulaN S.language) : Prop :=
  scope.length = 0 →
    ∀ j : Fin S.n, i ≤ j.val → j.val < i + countExN A →
      S.skolemRank j = 0



-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- FV subset bound for `skolemFormAux`. Starting from an NNF input with
sufficient Skolem-symbol allocation AND the `noFallback` invariant,
every free variable of the output is either a free variable of the
input or a variable in `scope` (introduced by the Skolem substitution
`f(y_1,...,y_m)` whose argument vector indexes `scope`). Strong
induction on `formulaQuantCount A`. -/
theorem skolemFormAux_fv_bound {L : Language} (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat) (i : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      i + countExN A ≤ S.n →
      noFallback S scope i A →
      ∀ y ∈ formulaFVN (skolemFormAux S A scope i).1,
        y ∈ formulaFVN A ∨ y ∈ scope := by
-- BEGIN PROOF
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope i hCount hNNF hAlloc hNF
    unfold skolemFormAux
    match A, hCount, hNNF, hAlloc, hNF with
    | .predN _ _, _, _, _, _ => exact fun _ hy => Or.inl hy
    | .eq_ _ _ _, _, _, _, _ => exact fun _ hy => Or.inl hy
    | .neg _, _, _, _, _ => exact fun _ hy => Or.inl hy
    | .conj B C, hCount, hNNF, hAlloc, hNF =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have hNF_B : noFallback S scope i B := by
        intro hScope j hij hjB
        exact hNF hScope j hij (by simp [countExN]; omega)
      have ihB := ih _ qB B scope i rfl hB hAllocB hNF_B
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have hNF_C : noFallback S scope i' C := by
        intro hScope j hij hjC
        rw [hi'] at hij
        exact hNF hScope j (by omega) (by
          rw [hi'] at hjC; simp [countExN]; omega)
      have ihC := ih _ qC C scope i' rfl hC hAllocC hNF_C
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      intro y hy
      simp only [formulaFVN] at hy
      rcases hy with hy | hy
      · rcases ihB y hy with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihC y hy with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    | .disj B C, hCount, hNNF, hAlloc, hNF =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have hNF_B : noFallback S scope i B := by
        intro hScope j hij hjB
        exact hNF hScope j hij (by simp [countExN]; omega)
      have ihB := ih _ qB B scope i rfl hB hAllocB hNF_B
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have hNF_C : noFallback S scope i' C := by
        intro hScope j hij hjC
        rw [hi'] at hij
        exact hNF hScope j (by omega) (by
          rw [hi'] at hjC; simp [countExN]; omega)
      have ihC := ih _ qC C scope i' rfl hC hAllocC hNF_C
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      intro y hy
      simp only [formulaFVN] at hy
      rcases hy with hy | hy
      · rcases ihB y hy with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases ihC y hy with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hAlloc, _ =>
      have hB : FormulaN.isNNF B := hNNF
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have hNF_B : noFallback S (scope ++ [x]) i B := by
        intro hScope _ _ _
        simp [List.length_append] at hScope
      have ihB := ih _ qB B (scope ++ [x]) i rfl hB hAllocB hNF_B
      simp only
      generalize hBres : skolemFormAux S B (scope ++ [x]) i = Bres at ihB
      obtain ⟨B', i'⟩ := Bres
      intro y hy
      simp only [formulaFVN] at hy
      obtain ⟨hyB', hyNe⟩ := hy
      rcases ihB y hyB' with h | h
      · exact Or.inl (by
          simp only [formulaFVN]
          exact ⟨h, hyNe⟩)
      · rcases List.mem_append.mp h with h1 | h1
        · exact Or.inr h1
        · rcases List.mem_singleton.mp h1 with rfl
          exact absurd rfl hyNe
    | .ex x B, hCount, hNNF, hAlloc, hNF =>
      have hB : FormulaN.isNNF B := hNNF
      have hlt : i < S.n := by
        have := hAlloc
        simp [countExN] at this
        omega
      simp only [hlt, ↓reduceDIte]
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      let skolemTerm : Term S.language :=
        if hRank : S.skolemRank ⟨i, hlt⟩ = 0 then
          Term.const (.inr ⟨⟨i, hlt⟩, hRank⟩)
        else
          Term.func (.inr ⟨⟨i, hlt⟩, Nat.pos_of_ne_zero hRank⟩) fun k =>
            match hLen : scope.length with
            | 0 => Term.var x
            | _ + 1 =>
              Term.var (scope.get ⟨k.val % scope.length, by
                rw [hLen]; exact Nat.mod_lt _ (by omega)⟩)
      have qBsub : formulaQuantCount (formulaSubstN B skolemTerm x) < m := by
        rw [formulaSubst_quantCount]; omega
      have hB_subNNF : FormulaN.isNNF (formulaSubstN B skolemTerm x) :=
        isNNF_formulaSubstN B _ _ hB
      have hAllocB_sub :
          (i + 1) + countExN (formulaSubstN B skolemTerm x) ≤ S.n := by
        rw [formulaSubstN_countExN]
        simp [countExN] at hAlloc; omega
      have hNF_sub : noFallback S scope (i + 1) (formulaSubstN B skolemTerm x) := by
        intro hScope j hij hjB
        rw [formulaSubstN_countExN] at hjB
        exact hNF hScope j (by omega) (by simp [countExN]; omega)
      have ihBsub := ih _ qBsub _ scope (i + 1) rfl hB_subNNF hAllocB_sub hNF_sub
      have hTermFV : ∀ y ∈ termFV skolemTerm, y ∈ scope := by
        intro y hy
        dsimp only [skolemTerm] at hy
        split at hy
        · exact hy.elim
        · rename_i hRank
          change ∃ k, _ at hy
          obtain ⟨k, hk⟩ := hy
          by_cases hEmpty : scope.length = 0
          · exact (hRank (hNF hEmpty ⟨i, hlt⟩
              (by simp) (by simp [countExN]; omega))).elim
          · dsimp only at hk
            split at hk
            · next hLen => exact (hEmpty hLen).elim
            · change y = scope.get _ at hk
              rw [hk]
              exact List.get_mem _ _
      intro y hy
      rcases ihBsub y hy with hy | hy
      · rcases LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
                 B skolemTerm x y hy with ⟨hyB, hyNe⟩ | hyTerm
        · exact Or.inl (by
            simp only [formulaFVN]
            exact ⟨hyB, hyNe⟩)
        · exact Or.inr (hTermFV y hyTerm)
      · exact Or.inr hy

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
/-- Substitution preserves `distinctQuantifierBindings`. Substitution
rewrites terms inside the formula but leaves the quantifier tree
structure (and thus BV) intact. -/
theorem distinctQuantifierBindings_of_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (h : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (formulaSubstN A t x) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
    exact ih h
  | conj B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | disj B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | impl B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | all y B ih =>
    simp only [formulaSubstN]
    split
    · simp only [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
        LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
      exact ⟨ih h.1, h.2⟩
    · exact h
  | ex y B ih =>
    simp only [formulaSubstN]
    split
    · simp only [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
        LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
      exact ⟨ih h.1, h.2⟩
    · exact h

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Exact Skolemization preserves distinct quantifier bindings.
Disjointness at binary nodes follows from the bound-variable subset
theorem, and the eliminated existential case uses substitution's
invariance of the quantifier tree. -/
theorem skolemFormExactAux_distinctQuantifierBindings {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      distinctQuantifierBindings A →
      distinctQuantifierBindings B := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun hDQ
    match A, hCount, hNNF, hLength, hDQ with
    | .predN P ts, _, _, hLength, _ =>
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
      trivial
    | .eq_ h t₁ t₂, _, _, hLength, _ =>
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
      trivial
    | .neg C, _, hNNF, hLength, hDQ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hDQ
    | .conj C D, hCount, hNNF, hLength, hDQ =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hDQC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC' hDQ.1
      have hDQD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD' hDQ.2.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C scope
          (indices.take (skolemDescriptorCount C)) C' _
          rfl hNNF.1 hLeftLength hC'
      have hBVD :=
        skolemFormExactAux_bv_bound S _ D scope
          (indices.drop (skolemDescriptorCount C)) D' _
          rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, hDQD, ?_⟩
      intro y hy
      exact hDQ.2.2 y ⟨hBVC y hy.1, hBVD y hy.2⟩
    | .disj C D, hCount, hNNF, hLength, hDQ =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hDQC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC' hDQ.1
      have hDQD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD' hDQ.2.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C scope
          (indices.take (skolemDescriptorCount C)) C' _
          rfl hNNF.1 hLeftLength hC'
      have hBVD :=
        skolemFormExactAux_bv_bound S _ D scope
          (indices.drop (skolemDescriptorCount C)) D' _
          rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, hDQD, ?_⟩
      intro y hy
      exact hDQ.2.2 y ⟨hBVC y hy.1, hBVD y hy.2⟩
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength, hDQ =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hDQC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hC' hDQ.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C (scope ++ [x])
          indices C' _ rfl hNNF hBodyLength hC'
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, ?_⟩
      intro hx
      exact hDQ.2 (hBVC x hx)
    | .ex x C, hCount, hNNF, hLength, hDQ =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount C := by
          simp [skolemDescriptorCount] at hLength
          omega
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          isNNF_formulaSubstN C _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hDQSub : distinctQuantifierBindings CSub :=
          distinctQuantifierBindings_of_formulaSubstN
            C (exactSkolemTerm S i) x hDQ.1
        have hDQC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hC' hDQSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hDQC



-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Exact descriptor alignment discharges all traversal obligations
internally: the Skolem form of every bundled rectified NNF sentence is
closed, rectified, and contains no existential quantifier. No
allocation or rank-zero side condition is exposed to callers. -/
theorem skolemForm_isSkolemNormalForm' {L : Language}
    (spec : SkolemSpec L) :
    isSkolemNormalForm (skolemForm spec) := by
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNFLift : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (skolemFormTraversal spec) := by
    simp [A, skolemFormTraversal]
  have hShape :=
    skolemFormExactAux_shape_nnf spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount hRun
  have hFVSource : ∀ y ∈ formulaFVN A, y ∈ ([] : List Nat) := by
    intro y hy
    have hFVlift :
        formulaFVN A = formulaFVN spec.source := by
      simpa [A] using liftFormulaSkolem_formulaFVN spec.source
    have hySource : y ∈ formulaFVN spec.source := hFVlift ▸ hy
    rw [spec.hSentence] at hySource
    exact hySource.elim
  have hFV :=
    skolemFormExactAux_fv_bound spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount
      spec.indices_scopes_lifted hRun hFVSource
  have hDQlift : distinctQuantifierBindings A := by
    simpa [A] using
      liftFormulaSkolem_distinctQuantifierBindings
        spec.source spec.hRect.2
  have hDQ :=
    skolemFormExactAux_distinctQuantifierBindings spec _ A []
      spec.indices (skolemFormTraversal spec).1
      (skolemFormTraversal spec).2 rfl hNNFLift
      spec.indices_length_eq_lifted_descriptorCount hRun hDQlift
  change
    isSkolemNormalFormShape (skolemFormTraversal spec).1 ∧
      isRectified (skolemFormTraversal spec).1 ∧
      FormulaN.isClosed (skolemFormTraversal spec).1
  refine ⟨hShape.2, ?_, ?_⟩
  · refine ⟨?_, hDQ⟩
    intro y hy
    exact List.not_mem_nil (hFV y hy.1)
  · unfold FormulaN.isClosed
    funext y
    apply propext
    constructor
    · intro hy
      exact (List.not_mem_nil (hFV y hy)).elim
    · intro hy
      exact hy.elim

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- The exact top-level traversal preserves NNF. -/
theorem skolemForm_isNNF' {L : Language}
    (spec : SkolemSpec L) :
    FormulaN.isNNF (skolemForm spec) := by
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNFLift : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (skolemFormTraversal spec) := by
    simp [A, skolemFormTraversal]
  have hShape :=
    skolemFormExactAux_shape_nnf spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount hRun
  exact hShape.1

end LCS.Herbrand.SHGTheorem.Herbrand
end

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
section
-- ATTACH-BLOCKER: global set_option
set_option autoImplicit false
namespace SkolemAllocationRegression









end SkolemAllocationRegression
end
end LCS.Herbrand.SHGTheorem.Herbrand
end

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

/-- Internal closed-seed core of the G1nnf branch of Lemma 7.6.2.
    The seed is the exact capability needed by the universal
    c-instance case; the public Chapter 7 wrapper obtains it from the
    section's standing constant-symbol assumption. -/
theorem herbrand_half_lemma_G1nnf_seed {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hProv : G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      Nonempty (G2nnfProofTree (show spec.language.withoutEquality from hL)
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language))) := by
  have hClosed : FormulaN.isClosed A := hSource ▸ spec.hSentence
  have hCross : LCS.CutElim.Hauptsatz.finsetCrossNoFreeBound
      ({A} : LCS.Finset (FormulaN L)) ∅ := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := hx
    rcases hF with hF | hF
    · have hFA := (LCS.Finset.mem_singleton F A).1 hF
      subst F
      rw [hClosed] at hxF
      exact hxF.elim
    · exact (LCS.Finset.not_mem_empty hF).elim
  have hNNF : allSequentFormulaeAreNNF
      (({A} : LCS.Finset (FormulaN L)), ∅) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ (hSource ▸ spec.hNNF)
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  have hRect : AllRectified (({A} : LCS.Finset (FormulaN L)), ∅) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ (hSource ▸ spec.hRect)
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  obtain ⟨T, mid, hCutFree, hPure, hMid⟩ :=
    sharpenedHauptsatz_G2nnf hL _ hNNF hRect hCross hProv
  -- REPAIR(T6-21d): proof pending
  sorry

/-- Lemma 7.6.2, equality-free branch: from a G1nnf proof of the
original sequent A ->, obtain a quantifier-free c-instance C of SK spec
with a G1nnf proof of C -> over spec.language. The exact source equality
retains the rectified-NNF sentence domain; no prenex conversion is assumed.
This is the existence specification; effective extraction is deferred. -/
theorem herbrand_half_lemma_G1nnf {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hProv : G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      Nonempty (G1nnfProofTree (show spec.language.withoutEquality from hL)
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language))) := by
  -- REPAIR(T7-80): proof pending (G1 output over the exact Skolem extension).
  sorry

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): herbrand_half_lemma_G1nnfEq
-- ===================================================================

/-- Closed-seed form of the equality branch of Lemma 7.6.2. -/
theorem herbrand_half_lemma_G1nnfEq_seed {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hProv : G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      (haveI hL' : spec.language.hasEquality = true := hL
       Nonempty (G2nnfEqProofTree hL'
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language)))) := by
  -- REPAIR(T6-21d): proof pending
  sorry

/-- Lemma 7.6.2, equality branch: from a G1nnf= proof of the original
sequent A ->, obtain a quantifier-free c-instance C of SK spec with a
G1nnf= proof of C -> over the same Skolem extension. The source is the
specified rectified NNF sentence. Effective extraction remains deferred. -/
theorem herbrand_half_lemma_G1nnfEq {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hProv : G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      (haveI hL' : spec.language.hasEquality = true := hL
       Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hL'
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language)))) := by
  -- REPAIR(T7-80): proof pending (G1 output over the exact Skolem extension).
  sorry

-- ===================================================================
-- Lemma 7.6.2: herbrand_half_lemma
-- ===================================================================

/-- Lemma 7.6.2, existence specification for a rectified NNF sentence A
and its fixed Skolem form SK spec. Each original proof of A -> yields a
quantifier-free c-instance C with a proof of C ->, representing provability
of not C in NNF. Both input and output use G1nnf without equality and
G1nnf= with equality; the output lives in spec.language. The conjunction
keeps the two language branches separate. Effective extraction is deferred. -/
@[blueprint "chap7__lemma_7_6_2" (main := true)]
theorem herbrand_half_lemma {L : Language}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    (∀ hL : L.withoutEquality, G1nnfProvableSet hL
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        Nonempty (G1nnfProofTree (show spec.language.withoutEquality from hL)
          ({C} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language)))) ∧
    (∀ (hL : L.hasEquality = true),
      G1nnfEqProvable_Set hL
          (({A} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        (haveI hL' : spec.language.hasEquality = true := hL
         Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hL'
          ({C} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language))))) 

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Retention-aware antecedent lineage along an exact root-to-node path
consisting of universal-left steps. Unlike strict occurrence lineage, this
relation follows either the transformed principal formula or a retained
`Finset` context cell, including the case where their formulae collide. -/
def g2nnfUniversalAntecedentLineage {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode} :
    (path : G2nnfProofTree.RootToNodePath root node) →
    FormulaN L → FormulaN L → List (Nat × Term L) → Prop
  | .root _, source, target, substitutions =>
      source = target ∧ substitutions = []
  | .onePremise rule _ _ _ _ path,
      source, target, substitutions =>
      match rule with
      | .allSubLeft A occurrence x B t _ Gamma _ =>
          (source ∈ Gamma ∧
            g2nnfUniversalAntecedentLineage path
              source target substitutions) ∨
          ∃ tail,
            source = A ∧
            g2nnfUniversalAntecedentLineage path
              (occurrence.replace (formulaSubstN B t x))
              target tail ∧
            substitutions = (x, t) :: tail
      | _ => False
  | .leftPremise _ _ _ _ _ _ _, _, _, _ => False
  | .rightPremise _ _ _ _ _ _ _, _, _, _ => False

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution commutes with extraction of a prenex matrix when the
substituted variable is not bound in the formula. -/
theorem prenexMatrix_formulaSubstN_of_not_bv {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (h : ¬x ∈ formulaBVN A) :
    prenexMatrix (formulaSubstN A t x) =
      formulaSubstN (prenexMatrix A) t x := by
  induction A with
  | predN P ts => rfl
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih => rfl
  | conj A B ihA ihB => rfl
  | disj A B ihA ihB => rfl
  | impl A B ihA ihB => rfl
  | all y A ih =>
      have hxy : x ≠ y := by
        intro hEq
        apply h
        simp [hEq, formulaBVN]
      have hA : ¬x ∈ formulaBVN A := by
        intro hx
        apply h
        simp [formulaBVN, hx]
      simp [formulaSubstN, hxy, prenexMatrix, ih hA]
  | ex y A ih =>
      have hxy : x ≠ y := by
        intro hEq
        apply h
        simp [hEq, formulaBVN]
      have hA : ¬x ∈ formulaBVN A := by
        intro hx
        apply h
        simp [formulaBVN, hx]
      simp [formulaSubstN, hxy, prenexMatrix, ih hA]

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
theorem isQuantifierFree_prenexPrefix_eq_nil {L : Language}
    (A : FormulaN L) (h : isQuantifierFree A) :
    prenexPrefix A = [] := by
  cases A <;> simp_all [isQuantifierFree, prenexPrefix]

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
theorem isQuantifierFree_prenexMatrix_eq_self {L : Language}
    (A : FormulaN L) (h : isQuantifierFree A) :
    prenexMatrix A = A := by
  cases A <;> simp_all [isQuantifierFree, prenexMatrix]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- A universal-prenex lineage reaching a quantifier-free target consumes
the complete source prefix, in order, and replays to that exact target. -/
theorem g2nnfUniversalAntecedentLineage_fullPrefixReplay
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    {path : G2nnfProofTree.RootToNodePath root node}
    {source target : FormulaN L}
    {substitutions : List (Nat × Term L)}
    (hLineage : g2nnfUniversalAntecedentLineage path
      source target substitutions)
    (hPrenex : isPrenex source)
    (hUniversal : ∀ p ∈ prenexPrefix source,
      p.1 = QuantifierKind.universal)
    (hDistinct : distinctQuantifierBindings source)
    (hTargetQf : isQuantifierFree target) :
    substitutions.map Prod.fst =
        (prenexPrefix source).map Prod.snd ∧
      replayQuantifierSubstitutionsFormula substitutions
        (prenexMatrix source) = target := by
  induction path generalizing source substitutions with
  | root T =>
      simp only [g2nnfUniversalAntecedentLineage] at hLineage
      rcases hLineage with ⟨rfl, rfl⟩
      constructor
      · simpa using isQuantifierFree_prenexPrefix_eq_nil _ hTargetQf
      · change prenexMatrix source = source
        exact isQuantifierFree_prenexMatrix_eq_self _ hTargetQf
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [g2nnfUniversalAntecedentLineage] at hLineage
      next A occurrence x B t hSelected Gamma Delta =>
        rcases hLineage with hContext | hPrincipal
        · exact ih hContext.2 hPrenex hUniversal hDistinct
        · rcases hPrincipal with ⟨tail, rfl, hTail, rfl⟩
          have hShape :
              source = FormulaN.all x B :=
            (eq_of_mem_maxQuantSubformulae_of_isPrenex
              source occurrence.selected hPrenex
              occurrence.selected_mem).symm.trans hSelected
          subst source
          cases occurrence
          simp only [MaxQuantifierOccurrence.replace] at hTail
          have hPrenexB : isPrenex B := hPrenex
          have hUniversalB :
              ∀ p ∈ prenexPrefix B,
                p.1 = QuantifierKind.universal := by
            intro p hp
            apply hUniversal p
            simp [prenexPrefix, hp]
          have hPrenexSub :
              isPrenex (formulaSubstN B t x) :=
            isPrenex_formulaSubstN B t x hPrenexB
          have hUniversalSub :
              ∀ p ∈ prenexPrefix (formulaSubstN B t x),
                p.1 = QuantifierKind.universal := by
            intro p hp
            apply hUniversalB p
            rwa [prenexPrefix_formulaSubstN] at hp
          have hDistinctSub :
              distinctQuantifierBindings
                (formulaSubstN B t x) :=
            distinctQuantifierBindings_of_formulaSubstN
              B t x hDistinct.1
          obtain ⟨hPrefix, hReplay⟩ :=
            ih hTail hPrenexSub hUniversalSub
              hDistinctSub
          constructor
          · simp [prenexPrefix, prenexPrefix_formulaSubstN,
              hPrefix]
          · simp only [replayQuantifierSubstitutionsFormula,
              prenexMatrix]
            rw [← prenexMatrix_formulaSubstN_of_not_bv
              B t x hDistinct.2]
            exact hReplay
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hLineage.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hLineage.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Every formula in the endpoint antecedent of an all-left path has a
retention-aware lineage from some formula in the root antecedent. -/
theorem g2nnfUniversalAntecedentLineage_of_mem
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ source ∈ Γroot, ∃ substitutions,
      g2nnfUniversalAntecedentLineage path
        source target substitutions := by
  induction path with
  | root T =>
      exact ⟨target, hTarget, [], rfl, rfl⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [AllRulesAllSubLeftOnPath] at hAll
      case allSubLeft A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, substitutions, hLineage⟩ :=
          ih hAll hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with hInserted | hContext
        · refine ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl),
            (x, t) :: substitutions, ?_⟩
          right
          exact ⟨substitutions, rfl, hInserted ▸ hLineage, rfl⟩
        · refine ⟨source,
            LCS.Finset.mem_insert.mpr (Or.inr hContext),
            substitutions, ?_⟩
          left
          exact ⟨hContext, hLineage⟩
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Singleton specialization of antecedent-lineage coverage. -/
theorem g2nnfUniversalAntecedentLineage_from_singleton
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {B : FormulaN L} {Δroot Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({B} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ substitutions,
      g2nnfUniversalAntecedentLineage path
        B target substitutions := by
  obtain ⟨source, hSource, substitutions, hLineage⟩ :=
    g2nnfUniversalAntecedentLineage_of_mem
      path hAll hTarget
  have hEq : source = B :=
    (LCS.Finset.mem_singleton source B).mp hSource
  subst source
  exact ⟨substitutions, hLineage⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Full-prefix specialization at the same occurrence supplied by the
midsequent theorem. -/
theorem universalPrenexSingleton_midsequentFullPrefix
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ occurrence : G2nnfProofTree.NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      ∀ target, target ∈ mid.1 →
        ∃ substitutions,
          g2nnfUniversalAntecedentLineage occurrence.path
              source target substitutions ∧
            substitutions.map Prod.fst =
              (prenexPrefix source).map Prod.snd ∧
            replayQuantifierSubstitutionsFormula substitutions
              (prenexMatrix source) = target := by
  rcases universalPrenexSingleton_midsequentSpecialization
      source hSource mid hMid with
    ⟨hSuccedent, occurrence, hAbove, hAllSubLeft,
      hAntecedent⟩
  refine ⟨hSuccedent, occurrence, hAbove, hAllSubLeft, ?_⟩
  intro target hTarget
  obtain ⟨substitutions, hLineage⟩ :=
    g2nnfUniversalAntecedentLineage_from_singleton
      occurrence.path hAllSubLeft hTarget
  obtain ⟨hPrefix, hReplay⟩ :=
    g2nnfUniversalAntecedentLineage_fullPrefixReplay
      hLineage hSource.1 hSource.2 hDistinct
      (hMid.midIsQuantifierFree.1 target hTarget)
  exact ⟨substitutions, hLineage, hPrefix, hReplay⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Universal-left steps preserve nonemptiness of the antecedent. -/
theorem antecedent_ne_empty_of_allSubLeftOnPath
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    (hRoot : Γroot ≠ LCS.Finset.empty) :
    Γnode ≠ LCS.Finset.empty := by
  induction path with
  | root T =>
      exact hRoot
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [AllRulesAllSubLeftOnPath] at hAll
      case allSubLeft A occurrence x B t hSelected Gamma Delta =>
        apply ih hAll
        intro hEmpty
        change LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma = LCS.Finset.empty at hEmpty
        have hInserted :
            occurrence.replace (formulaSubstN B t x) ∈
              LCS.Finset.insert
                (occurrence.replace (formulaSubstN B t x))
                Gamma :=
          LCS.Finset.mem_insert.mpr (Or.inl rfl)
        rw [hEmpty] at hInserted
        exact LCS.Finset.not_mem_empty hInserted
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
theorem finset_ofList_toList {α : Type} [DecidableEq α]
    (S : LCS.Finset α) :
    LCS.Finset.ofList S.toList = S := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_ofList, LCS.Finset.mem_toList]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
theorem finset_toList_ne_nil_of_ne_empty
    {α : Type} [DecidableEq α]
    (S : LCS.Finset α)
    (hS : S ≠ LCS.Finset.empty) :
    S.toList ≠ [] := by
  intro hNil
  apply hS
  apply LCS.Finset.ext
  intro a
  constructor
  · intro ha
    have hList : a ∈ S.toList :=
      (LCS.Finset.mem_toList S a).mpr ha
    rw [hNil] at hList
    simp at hList
  · intro ha
    exact (LCS.Finset.not_mem_empty ha).elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Enumerate the actual midsequent antecedent list, preserving the same
node occurrence and giving full-prefix lineage for every list cell. -/
theorem universalPrenexSingleton_midsequentFullPrefixList
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ (occurrence : G2nnfProofTree.NodeOccurrence
          T mid.1 mid.2)
        (instances : List (FormulaN L)),
      AllRulesPropOrWeakening occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      instances ≠ [] ∧
      LCS.Finset.ofList instances = mid.1 ∧
      ∀ target, target ∈ instances →
        ∃ substitutions,
          g2nnfUniversalAntecedentLineage occurrence.path
              source target substitutions ∧
            substitutions.map Prod.fst =
              (prenexPrefix source).map Prod.snd ∧
            replayQuantifierSubstitutionsFormula substitutions
              (prenexMatrix source) = target := by
  rcases universalPrenexSingleton_midsequentFullPrefix
      source hSource hDistinct mid hMid with
    ⟨hSuccedent, occurrence, hAbove, hAllSubLeft,
      hInstances⟩
  have hRootNonempty :
      LCS.Finset.singleton source ≠ LCS.Finset.empty := by
    intro hEmpty
    have hSourceMem :
        source ∈ LCS.Finset.singleton source :=
      (LCS.Finset.mem_singleton source source).mpr rfl
    rw [hEmpty] at hSourceMem
    exact LCS.Finset.not_mem_empty hSourceMem
  have hMidNonempty : mid.1 ≠ LCS.Finset.empty :=
    antecedent_ne_empty_of_allSubLeftOnPath
      occurrence.path hAllSubLeft hRootNonempty
  refine ⟨hSuccedent, occurrence, mid.1.toList,
    hAbove, hAllSubLeft,
    finset_toList_ne_nil_of_ne_empty mid.1 hMidNonempty,
    finset_ofList_toList mid.1, ?_⟩
  intro target hTarget
  exact hInstances target
    ((LCS.Finset.mem_toList mid.1 target).mp hTarget)

end LCS.Herbrand.SHGTheorem.Herbrand
end

