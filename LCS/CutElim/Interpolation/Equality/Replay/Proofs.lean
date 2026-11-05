import LCS.CutElim.Interpolation.Equality.Replay

section

namespace LCS.CutElim.Interpolation.Equality

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

open LCS.CutElim.Interpolation

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Equality.Completeness

open LCS.FirstOrder.Gentzen.Hintikka



helper /-- Lemma 6.5.3 (companion): Backward direction: if
(closedEqualityAxioms S ++ Gamma) -> Delta is LKe-provable,
then S is LKe-provable. Each formula in S_e is universally valid,
so use lkeProvable_remove_valid_prefix to strip them. -/
theorem lke_with_se_to_lke {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : lkeProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent }) :
    lkeProvable S :=
-- BEGIN PROOF
by
  have hresult := lkeProvable_remove_valid_prefix
    (closedEqualityAxioms hL S) S.antecedent S.succedent
    (closedEqualityAxioms_universally_valid hL S) hProv
  have heq : Sequent.mk S.antecedent S.succedent = S := by cases S; rfl
  rw [heq] at hresult
  exact hresult

helper /-- Lemma 6.5.3 (companion): Backward direction from folkProvable:
if (closedEqualityAxioms S ++ Gamma) -> Delta is LK-provable,
then S is LKe-provable. Wraps the FOLK proof in LKe.lk and
strips the S_e prefix. -/
theorem lk_with_se_to_lke {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent }) :
    lkeProvable S :=
-- BEGIN PROOF
by
  -- folkProvable is now Nonempty (FOLKProofTree s) with indexed proof trees
  obtain ⟨t⟩ := hProv
  have hlke : lkeProvable (Sequent.mk (closedEqualityAxioms hL S ++ S.antecedent) S.succedent) :=
    ⟨LKeProofTree.lk t⟩
  exact lke_with_se_to_lke hL S hlke

proof_of lke_provable_iff_lke_with_se := ⟨lke_to_folk_with_se hL S, lk_with_se_to_lke hL S⟩
  -- BEGIN PROOF






helper /-- Lemma 6.5.4 (companion): closedEqualityAxioms S decomposes
as closedEqualityAxiomsForSide part.gamma1 part.delta1 ++
closedEqualityAxiomsForSide part.gamma2 part.delta2
(up to permutation), i.e., S_e = S_e^1 union S_e^2. -/
theorem se_partition_union {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {s : Sequent L} (p : SequentPartition s) :
    ∀ A, A ∈ closedEqualityAxioms hL s →
      A ∈ closedEqualityAxiomsForSide hL p.gamma1 p.delta1 ∨
      A ∈ closedEqualityAxiomsForSide hL p.gamma2 p.delta2 :=
-- BEGIN PROOF
by
  intro A hA
  simp only [closedEqualityAxioms, closedEqualityAxiomsForSide] at hA ⊢
  rcases List.mem_append.mp hA with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · left
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hRefl)))
    · rw [List.mem_map] at hFun
      obtain ⟨f, hfMem, hfEq⟩ := hFun
      subst hfEq
      simp only [sequentFunSymbolsList] at hfMem
      rw [List.mem_eraseDups, List.mem_flatMap] at hfMem
      obtain ⟨F, hFmem, hFf⟩ := hfMem
      have funSymInSide : ∀ (g1 d1 : List (FormulaN L)),
          F ∈ g1 ++ d1 →
          f ∈ sequentFunSymbolsList { antecedent := g1, succedent := d1 } := by
        intro g1 d1 hF
        simp only [sequentFunSymbolsList]
        rw [List.mem_eraseDups, List.mem_flatMap]
        exact ⟨F, hF, hFf⟩
      have funCongInSide : ∀ (g1 d1 : List (FormulaN L)),
          f ∈ sequentFunSymbolsList { antecedent := g1, succedent := d1 } →
          closedFunCongAxiom hL f ∈ closedEqualityAxiomsForSide hL g1 d1 := by
        intro g1 d1 hf
        simp only [closedEqualityAxiomsForSide]
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨f, hf, rfl⟩
      rcases List.mem_append.mp hFmem with hFante | hFsucc
      · rcases p.gamma_partition.mem_or hFante with hF1 | hF2
        · left; exact funCongInSide _ _ (funSymInSide _ _ (List.mem_append_left _ hF1))
        · right; exact funCongInSide _ _ (funSymInSide _ _ (List.mem_append_left _ hF2))
      · rcases p.delta_partition.mem_or hFsucc with hF1 | hF2
        · left; exact funCongInSide _ _ (funSymInSide _ _ (List.mem_append_right _ hF1))
        · right; exact funCongInSide _ _ (funSymInSide _ _ (List.mem_append_right _ hF2))
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, hPMem, hPEq⟩ := hPred
      subst hPEq
      simp only [sequentPredSymbolsList] at hPMem
      rw [List.mem_eraseDups, List.mem_flatMap] at hPMem
      obtain ⟨F, hFmem, hFP⟩ := hPMem
      have predSymInSide : ∀ (g1 d1 : List (FormulaN L)),
          F ∈ g1 ++ d1 →
          P ∈ sequentPredSymbolsList { antecedent := g1, succedent := d1 } := by
        intro g1 d1 hF
        simp only [sequentPredSymbolsList]
        rw [List.mem_eraseDups, List.mem_flatMap]
        exact ⟨F, hF, hFP⟩
      have predCongInSide : ∀ (g1 d1 : List (FormulaN L)),
          P ∈ sequentPredSymbolsList { antecedent := g1, succedent := d1 } →
          closedPredCongAxiom hL P ∈ closedEqualityAxiomsForSide hL g1 d1 := by
        intro g1 d1 hP
        simp only [closedEqualityAxiomsForSide]
        apply List.mem_append_right
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨P, hP, rfl⟩
      rcases List.mem_append.mp hFmem with hFante | hFsucc
      · rcases p.gamma_partition.mem_or hFante with hF1 | hF2
        · left; exact predCongInSide _ _ (predSymInSide _ _ (List.mem_append_left _ hF1))
        · right; exact predCongInSide _ _ (predSymInSide _ _ (List.mem_append_left _ hF2))
      · rcases p.delta_partition.mem_or hFsucc with hF1 | hF2
        · left; exact predCongInSide _ _ (predSymInSide _ _ (List.mem_append_right _ hF1))
        · right; exact predCongInSide _ _ (predSymInSide _ _ (List.mem_append_right _ hF2))
    · have hHas : sequentHasEq s = true := by
        cases h : sequentHasEq s <;> simp_all
      have hEq := eq_of_mem_optionalSingleton _ hEq
      subst A
      obtain ⟨F, hFmem, hFEq⟩ := List.any_eq_true.mp hHas
      have eqCongInSide : ∀ (g d : List (FormulaN L)), F ∈ g ++ d →
          closedEqCongAxiom hL ∈ closedEqualityAxiomsForSide hL g d := by
        intro g d hF
        have hSide : sequentHasEq (Sequent.mk g d) = true :=
          List.any_eq_true.mpr ⟨F, hF, hFEq⟩
        simp [closedEqualityAxiomsForSide, hSide]
      rcases List.mem_append.mp hFmem with hAnt | hSucc
      · rcases p.gamma_partition.mem_or hAnt with h1 | h2
        · exact Or.inl (eqCongInSide _ _ (List.mem_append_left _ h1))
        · exact Or.inr (eqCongInSide _ _ (List.mem_append_left _ h2))
      · rcases p.delta_partition.mem_or hSucc with h1 | h2
        · exact Or.inl (eqCongInSide _ _ (List.mem_append_right _ h1))
        · exact Or.inr (eqCongInSide _ _ (List.mem_append_right _ h2))

end LCS.CutElim.Interpolation.Equality

end
