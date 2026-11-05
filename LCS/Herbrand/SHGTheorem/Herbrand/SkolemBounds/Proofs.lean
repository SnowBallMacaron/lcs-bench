import LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds

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







helper /-- BV subset bound for `skolemFormAux`. Starting from an NNF input
with sufficient Skolem-symbol allocation, every bound variable of the
output is a bound variable of the input: `skolemFormAux` only eliminates
existentials (it never introduces new quantifier bindings) and
`formulaSubstN` preserves BV by `formulaBV_formulaSubst`. Independent of
the `noFallback` hypothesis. -/
theorem skolemFormAux_bv_bound {L : Language} (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat) (i : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      i + countExN A ≤ S.n →
      ∀ y ∈ formulaBVN (skolemFormAux S A scope i).1,
        y ∈ formulaBVN A := by
-- BEGIN PROOF
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope i hCount hNNF hAlloc
    unfold skolemFormAux
    match A, hCount, hNNF, hAlloc with
    | .predN _ _, _, _, _ => exact fun _ hy => hy
    | .eq_ _ _ _, _, _, _ => exact fun _ hy => hy
    | .neg _, _, _, _ => exact fun _ hy => hy
    | .conj B C, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B scope i rfl hB hAllocB
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      intro y hy
      simp only [formulaBVN] at hy
      rcases hy with hy | hy
      · exact Or.inl (ihB y hy)
      · exact Or.inr (ihC y hy)
    | .disj B C, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B scope i rfl hB hAllocB
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      intro y hy
      simp only [formulaBVN] at hy
      rcases hy with hy | hy
      · exact Or.inl (ihB y hy)
      · exact Or.inr (ihC y hy)
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B (scope ++ [x]) i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B (scope ++ [x]) i = Bres at ihB
      obtain ⟨B', i'⟩ := Bres
      intro y hy
      simp only [formulaBVN] at hy
      rcases hy with hy | hy
      · exact Or.inl (ihB y hy)
      · exact Or.inr hy
    | .ex x B, hCount, hNNF, hAlloc =>
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
      have ihBsub := ih _ qBsub _ scope (i + 1) rfl hB_subNNF hAllocB_sub
      intro y hy
      have hyBsub := ihBsub y hy
      rw [LCS.CutElim.Interpolation.formulaBV_formulaSubst B skolemTerm x]
        at hyBsub
      simp only [formulaBVN]
      exact Or.inl hyBsub







helper /-- `distinctQuantifierBindings` preservation for `skolemFormAux`.
Structural induction on the recursion: `.all` case preserves outer
`.all`'s binding structure (and delegates BV-disjointness to the BV
bound); `.ex` case eliminates the existential via `formulaSubstN` on
the body (which preserves BV by `formulaBV_formulaSubst`) then recurses;
connectives distribute, with BV-disjointness on split subtrees derived
from the BV bound. -/
theorem skolemFormAux_distinctQuantifierBindings {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat) (i : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      i + countExN A ≤ S.n →
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A →
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
        (skolemFormAux S A scope i).1 := by
-- BEGIN PROOF
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope i hCount hNNF hAlloc hDQ
    unfold skolemFormAux
    match A, hCount, hNNF, hAlloc, hDQ with
    | .predN _ _, _, _, _, _ => exact trivial
    | .eq_ _ _ _, _, _, _, _ => exact trivial
    | .neg _, _, _, _, hDQ => exact hDQ
    | .conj B C, hCount, hNNF, hAlloc, hDQ =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hDQB := hDQ.1
      have hDQC := hDQ.2.1
      have hBVdisj := hDQ.2.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B scope i rfl hB hAllocB hDQB
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      have hBVb := skolemFormAux_bv_bound S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB hBVb
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC hDQC
      have hBVc := skolemFormAux_bv_bound S _ C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC hBVc
      obtain ⟨C', i''⟩ := Cres
      refine ⟨ihB, ihC, ?_⟩
      intro y ⟨hyB', hyC'⟩
      exact hBVdisj y ⟨hBVb y hyB', hBVc y hyC'⟩
    | .disj B C, hCount, hNNF, hAlloc, hDQ =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hDQB := hDQ.1
      have hDQC := hDQ.2.1
      have hBVdisj := hDQ.2.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B scope i rfl hB hAllocB hDQB
      have hShapeB := skolemFormAux_shape_nnf_counter S _ B scope i rfl hB hAllocB
      have hBVb := skolemFormAux_bv_bound S _ B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB hShapeB hBVb
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := hShapeB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by
        rw [hi']; simp [countExN] at hAlloc; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC hDQC
      have hBVc := skolemFormAux_bv_bound S _ C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC hBVc
      obtain ⟨C', i''⟩ := Cres
      refine ⟨ihB, ihC, ?_⟩
      intro y ⟨hyB', hyC'⟩
      exact hBVdisj y ⟨hBVb y hyB', hBVc y hyC'⟩
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hAlloc, hDQ =>
      have hB : FormulaN.isNNF B := hNNF
      have hDQB := hDQ.1
      have hxNotBV := hDQ.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B (scope ++ [x]) i rfl hB hAllocB hDQB
      have hBVb := skolemFormAux_bv_bound S _ B (scope ++ [x]) i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B (scope ++ [x]) i = Bres at ihB hBVb
      obtain ⟨B', i'⟩ := Bres
      refine ⟨ihB, ?_⟩
      intro hxB'
      exact hxNotBV (hBVb x hxB')
    | .ex x B, hCount, hNNF, hAlloc, hDQ =>
      have hB : FormulaN.isNNF B := hNNF
      have hDQB := hDQ.1
      have hxNotBV := hDQ.2
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
      -- distinctQuantifierBindings preserved by formulaSubstN
      -- (substitution leaves the quantifier tree shape intact).
      have hDQ_sub : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
          (formulaSubstN B skolemTerm x) :=
        distinctQuantifierBindings_of_formulaSubstN B skolemTerm x hDQB
      exact ih _ qBsub _ scope (i + 1) rfl hB_subNNF hAllocB_sub hDQ_sub





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

namespace SkolemAllocationRegression

helper /-- Compiler-backed top-level regressions: zero, one, sibling, and
nested inputs all eliminate every existential rather than exposing an
unchanged-existential fallback. -/
theorem SkolemAllocationRegression.zero_no_surviving_existential :
    isSkolemNormalFormShape (skolemForm
      LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.zeroSpec) :=
  (skolemForm_isSkolemNormalForm'
    LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.zeroSpec).1

helper theorem SkolemAllocationRegression.one_no_surviving_existential :
    isSkolemNormalFormShape (skolemForm
      LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.oneSpec) :=
  (skolemForm_isSkolemNormalForm'
    LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.oneSpec).1

helper theorem SkolemAllocationRegression.sibling_no_surviving_existential :
    isSkolemNormalFormShape (skolemForm
      LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.siblingSpec) :=
  (skolemForm_isSkolemNormalForm'
    LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.siblingSpec).1

helper theorem SkolemAllocationRegression.nested_no_surviving_existential :
    isSkolemNormalFormShape (skolemForm
      LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.nestedSpec) :=
  (skolemForm_isSkolemNormalForm'
    LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.nestedSpec).1

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

proof_of herbrand_half_lemma := ⟨fun hL hProv => herbrand_half_lemma_G1nnf hL spec A hSource hConst hProv,
  -- BEGIN PROOF
     fun hL hProv =>
       herbrand_half_lemma_G1nnfEq hL spec A hSource hConst hProv⟩


























end LCS.Herbrand.SHGTheorem.Herbrand

end
