import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair

section
namespace LCS.CutElim.Interpolation
open Classical
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
open LCS.FirstOrder.Gentzen.Hintikka
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

theorem allNoEq_cons_replace {L : Language}
    {X Y : FormulaN L} {rest tail : List (FormulaN L)}
    (hXY : formulaNoEq Y → formulaNoEq X) :
    ∀ F, F ∈ (X :: rest) ++ tail →
      ∃ G ∈ (Y :: rest) ++ tail, formulaNoEq G → formulaNoEq F := by
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact ⟨Y, List.mem_append.mpr (Or.inl (List.Mem.head _)), hXY⟩
    · exact ⟨F, List.mem_append.mpr
        (Or.inl (List.Mem.tail _ hF)), id⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr hF), id⟩

theorem allNoEq_snoc_replace {L : Language}
    {X Y : FormulaN L} {head tail : List (FormulaN L)}
    (hXY : formulaNoEq Y → formulaNoEq X) :
    ∀ F, F ∈ head ++ (tail ++ [X]) →
      ∃ G ∈ head ++ (tail ++ [Y]), formulaNoEq G → formulaNoEq F := by
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl hF), id⟩
  · rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hF))), id⟩
    · have hFX : F = X := by simpa using hF
      subst F
      exact ⟨Y, List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr (by simp)))), hXY⟩

theorem lkBot_conjLeft_both {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (A B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨A :: B :: Γ, Δ⟩) :
    lkBotProvable botP hBotArity ⟨.conj A B :: Γ, Δ⟩ := by
  have h₁ := lkBot_exchangeLeft_at [] A B Γ Δ (by simpa using h)
  have h₂ := lkBot_onePremise
    (.andLeftR A B (A :: Γ) Δ) (by simpa using h₁)
  have h₃ := lkBot_exchangeLeft_at [] (.conj A B) A Γ Δ
    (by simpa using h₂)
  have h₄ := lkBot_onePremise
    (.andLeftL A B (.conj A B :: Γ) Δ) (by simpa using h₃)
  exact lkBot_contractLeft_front (.conj A B) Γ Δ
    (by simpa using h₄)

theorem lkBot_disjRight_both {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (A B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ ++ [A, B]⟩) :
    lkBotProvable botP hBotArity ⟨Γ, Δ ++ [.disj A B]⟩ := by
  have h₁ := lkBot_onePremise
    (.orRightR A B Γ (Δ ++ [A])) (by simpa [List.append_assoc] using h)
  have h₂ := lkBot_exchangeRight_at Γ Δ A (.disj A B) []
    (by simpa [List.append_assoc] using h₁)
  have h₃ := lkBot_onePremise
    (.orRightL A B Γ (Δ ++ [.disj A B]))
    (by simpa [List.append_assoc] using h₂)
  exact lkBot_contractRight_end Γ Δ (.disj A B)
    (by simpa [List.append_assoc] using h₃)

theorem lkBot_weaken_to {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ Δ Γ' Δ' : List (FormulaN L))
    (hΓ : ∀ F, F ∈ Γ → F ∈ Γ')
    (hΔ : ∀ F, F ∈ Δ → F ∈ Δ')
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ⟩) :
    lkBotProvable botP hBotArity ⟨Γ', Δ'⟩ := by
  have h₁ := lkBot_weakenLeft_list Γ' Γ Δ h
  have h₂ := lkBot_contract_suffix Γ' Γ Δ hΓ h₁
  have h₃ := lkBot_weakenRight_list Γ' Δ Δ' h₂
  have h₄ := lkBot_swap_succ_blocks_pfx Γ' [] Δ Δ' []
    (by simpa [List.append_assoc] using h₃)
  exact lkBot_contract_suffix_succ Γ' Δ' Δ hΔ
    (by simpa [List.append_assoc] using h₄)

structure FormulaCover {L : Language}
    (F G : FormulaN L) : Prop where
  pred : formulaPredSymbolsN F ⊆ formulaPredSymbolsN G
  const : formulaConstSymbolsN F ⊆ formulaConstSymbolsN G
  fv : formulaFVN F ⊆ formulaFVN G
  noEq : formulaNoEq G → formulaNoEq F

theorem listFormulaCover {L : Language}
    {l l' : List (FormulaN L)}
    (h : ∀ F, F ∈ l → ∃ G ∈ l', FormulaCover F G) :
    listFormulaPredSymbols l ⊆ listFormulaPredSymbols l' ∧
    listFormulaConstSymbols l ⊆ listFormulaConstSymbols l' ∧
    listFormulaFV l ⊆ listFormulaFV l' ∧
    (∀ F, F ∈ l → ∃ G ∈ l', formulaNoEq G → formulaNoEq F) := by
  refine
    ⟨listFormulaPredSymbols_formula_sub (fun F hF => ?_),
      listFormulaConstSymbols_formula_sub (fun F hF => ?_),
      listFormulaFV_formula_sub (fun F hF => ?_),
      fun F hF => ?_⟩
  · obtain ⟨G, hG, hC⟩ := h F hF
    exact ⟨G, hG, hC.pred⟩
  · obtain ⟨G, hG, hC⟩ := h F hF
    exact ⟨G, hG, hC.const⟩
  · obtain ⟨G, hG, hC⟩ := h F hF
    exact ⟨G, hG, hC.fv⟩
  · obtain ⟨G, hG, hC⟩ := h F hF
    exact ⟨G, hG, hC.noEq⟩

theorem FormulaCover.refl {L : Language} (F : FormulaN L) :
    FormulaCover F F :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, id⟩

theorem FormulaCover.impl_left {L : Language}
    (A B : FormulaN L) :
    FormulaCover A (.impl A B) :=
  ⟨formulaPredSymbolsN_impl_left A B,
    formulaConstSymbolsN_impl_left A B,
    formulaFV_impl_left A B,
    fun h => h.1⟩

theorem FormulaCover.impl_right {L : Language}
    (A B : FormulaN L) :
    FormulaCover B (.impl A B) :=
  ⟨formulaPredSymbolsN_impl_right A B,
    formulaConstSymbolsN_impl_right A B,
    formulaFV_impl_right A B,
    fun h => h.2⟩

private theorem interpolation_exists_axiom_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (g₁ d₁ g₂ d₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ s.antecedent)
    (hd : List.Interleaving d₁ d₂ s.succedent)
    (hId : isFOLKAxiom s)
    : ∃ C, IsInterpolant botP hBotArity
          { gamma1 := g₁, delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg, delta_partition := hd } C := by
  classical
  rcases hId with ⟨A, hs₁, hs₂⟩
  rw [hs₁] at hg
  rw [hs₂] at hd
  rcases hg.singleton_iff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hd.singleton_iff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨botFormula botP hBotArity, ?_⟩
    refine
      { left_provable := ?_
        right_provable := ?_
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · exact lkBot_onePremise (.weakenRight (botFormula botP hBotArity) [A] [A]) (lkBot_axiom_id A)
    · exact ⟨.axiom_ ⟨[botFormula botP hBotArity], []⟩ (Or.inr ⟨rfl, rfl⟩)⟩
    · intro P hP hne
      apply (hne hP).elim
    · intro c hc
      rcases hc with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro v hv
      rcases hv with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro _
      trivial
  · refine ⟨A, ?_⟩
    refine
      { left_provable := lkBot_axiom_id A
        right_provable := lkBot_axiom_id A
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · intro P hP _
      exact ⟨⟨A, by simp, hP⟩, ⟨A, by simp, hP⟩⟩
    · intro c hc
      exact ⟨⟨A, by simp, hc⟩, ⟨A, by simp, hc⟩⟩
    · intro v hv
      exact ⟨⟨A, by simp, hv⟩, ⟨A, by simp, hv⟩⟩
    · intro h
      exact h A (by simp)
  · refine ⟨.neg A, ?_⟩
    refine
      { left_provable := ?_
        right_provable := ?_
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · simpa using lkBot_onePremise (.negRight A [] [A]) (lkBot_axiom_id A)
    · simpa using lkBot_onePremise (.negLeft A [A] []) (lkBot_axiom_id A)
    · intro P hP _
      exact ⟨⟨A, by simp, hP⟩, ⟨A, by simp, hP⟩⟩
    · intro c hc
      exact ⟨⟨A, by simp, hc⟩, ⟨A, by simp, hc⟩⟩
    · intro v hv
      exact ⟨⟨A, by simp, hv⟩, ⟨A, by simp, hv⟩⟩
    · intro h
      exact h A (by simp)
  · refine ⟨.neg (botFormula botP hBotArity), ?_⟩
    refine
      { left_provable := ?_
        right_provable := ?_
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · simpa using lkBot_onePremise (.negRight (botFormula botP hBotArity) [] [])
        (show lkBotProvable botP hBotArity ⟨[botFormula botP hBotArity], []⟩ from
          ⟨.axiom_ _ (Or.inr ⟨rfl, rfl⟩)⟩)
    · exact lkBot_onePremise (.weakenLeft (.neg (botFormula botP hBotArity)) [A] [A]) (lkBot_axiom_id A)
    · intro P hP hne
      apply (hne hP).elim
    · intro c hc
      rcases hc with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro v hv
      rcases hv with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro _
      trivial

private theorem interpolation_exists_axiom_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (g₁ d₁ g₂ d₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ s.antecedent)
    (hd : List.Interleaving d₁ d₂ s.succedent)
    (hBot : s.antecedent = [botFormula botP hBotArity] ∧ s.succedent = [])
    : ∃ C, IsInterpolant botP hBotArity
          { gamma1 := g₁, delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg, delta_partition := hd } C := by
  classical
  rcases hBot with ⟨hs₁, hs₂⟩
  rw [hs₁] at hg
  rw [hs₂] at hd
  rcases hd.nil_iff with ⟨rfl, rfl⟩
  rcases hg.singleton_iff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨botFormula botP hBotArity, ?_⟩
    refine
      { left_provable := lkBot_axiom_id _
        right_provable := ?_
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · exact ⟨.axiom_ _ (Or.inr ⟨rfl, rfl⟩)⟩
    · intro P hP hne
      apply (hne hP).elim
    · intro c hc
      rcases hc with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro v hv
      rcases hv with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro _
      trivial
  · refine ⟨.neg (botFormula botP hBotArity), ?_⟩
    refine
      { left_provable := ?_
        right_provable := ?_
        pred_common := ?_
        const_common := ?_
        fv_common := ?_
        no_eq := ?_ }
    · simpa using lkBot_onePremise (.negRight (botFormula botP hBotArity) [] [])
        (show lkBotProvable botP hBotArity ⟨[botFormula botP hBotArity], []⟩ from
          ⟨.axiom_ _ (Or.inr ⟨rfl, rfl⟩)⟩)
    · exact lkBot_onePremise (.weakenLeft (.neg (botFormula botP hBotArity)) [botFormula botP hBotArity] [])
        (show lkBotProvable botP hBotArity ⟨[botFormula botP hBotArity], []⟩ from
          ⟨.axiom_ _ (Or.inr ⟨rfl, rfl⟩)⟩)
    · intro P hP hne
      apply (hne hP).elim
    · intro c hc
      rcases hc with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro v hv
      rcases hv with ⟨i, _⟩
      exact (hBotArity ▸ i).elim0
    · intro _
      trivial

theorem interpolation_exists_axiom (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (hax : isLKBotAxiom botP hBotArity s)
    (p : SequentPartition s)
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hax with hId | hBot
  · exact interpolation_exists_axiom_left L botP hBotArity s g₁ d₁ g₂ d₂ hg hd hId
  · exact interpolation_exists_axiom_right L botP hBotArity s g₁ d₁ g₂ d₂ hg hd hBot

theorem interpolation_exists_weakenLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · let q : SequentPartition (Sequent.mk Γ Δ) := ⟨g₁', d₁, g₂, d₂, hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₁' ++ d₁ → F ∈ (A :: g₁') ++ d₁ := by
      intro F hF
      simp only [List.mem_append, List.mem_cons] at hF ⊢
      exact hF.elim (fun h => Or.inl (Or.inr h)) Or.inr
    refine ⟨C, isInterpolant_transport hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · intro h
      exact lkBot_onePremise (.weakenLeft A g₁' (d₁ ++ [C])) h
    · exact id
    · exact listFormulaPredSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaConstSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaFV_mono hmem
    · exact fun _ h => h
    · intro h F hF
      apply h F
      simp only [List.mem_append] at hF ⊢
      rcases hF with ((hF | hF) | hF) | hF
      · exact Or.inl (Or.inl (Or.inl (List.Mem.tail A hF)))
      · exact Or.inl (Or.inl (Or.inr hF))
      · exact Or.inl (Or.inr hF)
      · exact Or.inr hF
  · let q : SequentPartition (Sequent.mk Γ Δ) := ⟨g₁, d₁, g₂', d₂, hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₂' ++ d₂ → F ∈ (A :: g₂') ++ d₂ := by
      intro F hF
      simp only [List.mem_append, List.mem_cons] at hF ⊢
      exact hF.elim (fun h => Or.inl (Or.inr h)) Or.inr
    refine ⟨C, isInterpolant_transport hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · exact id
    · intro h
      have h' := lkBot_onePremise (.weakenLeft A ([C] ++ g₂') d₂) h
      simpa using (lkBot_exchangeLeft_at [] A C g₂' d₂ (by simpa using h'))
    · exact fun _ h => h
    · exact listFormulaPredSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaConstSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaFV_mono hmem
    · intro h F hF
      apply h F
      simp only [List.mem_append] at hF ⊢
      rcases hF with ((hF | hF) | hF) | hF
      · exact Or.inl (Or.inl (Or.inl hF))
      · exact Or.inl (Or.inl (Or.inr hF))
      · exact Or.inl (Or.inr (List.Mem.tail A hF))
      · exact Or.inr hF

theorem interpolation_exists_weakenRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk Γ Δ) := ⟨g₁, d₁', g₂, d₂, hg, hd'⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₁ ++ d₁' → F ∈ g₁ ++ (d₁' ++ [A]) := by
      intro F hF
      simp only [List.mem_append, List.mem_singleton] at hF ⊢
      exact hF.elim Or.inl (fun h => Or.inr (Or.inl h))
    refine ⟨C, isInterpolant_transport hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · intro h
      have h' := lkBot_onePremise (.weakenRight A g₁ (d₁' ++ [C])) h
      simpa [List.append_assoc] using (lkBot_exchangeRight_at g₁ d₁' C A [] (by simpa using h'))
    · exact id
    · exact listFormulaPredSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaConstSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaFV_mono hmem
    · exact fun _ h => h
    · intro h F hF
      apply h F
      simp only [List.mem_append] at hF ⊢
      rcases hF with ((hF | hF) | hF) | hF
      · exact Or.inl (Or.inl (Or.inl hF))
      · exact Or.inl (Or.inl (Or.inr (Or.inl hF)))
      · exact Or.inl (Or.inr hF)
      · exact Or.inr hF
  · let q : SequentPartition (Sequent.mk Γ Δ) := ⟨g₁, d₁, g₂, d₂', hg, hd'⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₂ ++ d₂' → F ∈ g₂ ++ (d₂' ++ [A]) := by
      intro F hF
      simp only [List.mem_append, List.mem_singleton] at hF ⊢
      exact hF.elim Or.inl (fun h => Or.inr (Or.inl h))
    refine ⟨C, isInterpolant_transport hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · exact id
    · intro h
      exact lkBot_onePremise (.weakenRight A ([C] ++ g₂) d₂') h
    · exact fun _ h => h
    · exact listFormulaPredSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaConstSymbols_mono hmem
    · exact fun _ h => h
    · exact listFormulaFV_mono hmem
    · intro h F hF
      apply h F
      simp only [List.mem_append] at hF ⊢
      rcases hF with ((hF | hF) | hF) | hF
      · exact Or.inl (Or.inl (Or.inl hF))
      · exact Or.inl (Or.inl (Or.inr hF))
      · exact Or.inl (Or.inr hF)
      · exact Or.inr (Or.inl hF)

theorem interpolation_exists_contractLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := A :: A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · let q : SequentPartition (Sequent.mk (A :: A :: Γ) Δ) := ⟨A :: A :: g₁', d₁, g₂, d₂,
        .left A (.left A hg'), hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ (A :: A :: g₁') ++ d₁ → F ∈ (A :: g₁') ++ d₁ := by
      intro F hF
      simp only [List.mem_append, List.mem_cons] at hF ⊢
      rcases hF with (hA | hA | hF) | hF
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr hF)
      · exact Or.inr hF
    refine ⟨C, isInterpolant_transport hI ?_ id (listFormulaPredSymbols_mono hmem) (fun _ h => h)
      (listFormulaConstSymbols_mono hmem) (fun _ h => h)
      (listFormulaFV_mono hmem) (fun _ h => h)
      (allNoEq_mono hmem (fun _ h => h))⟩
    · intro h
      exact lkBot_onePremise (.contractLeft A g₁' (d₁ ++ [C])) h
  · let q : SequentPartition (Sequent.mk (A :: A :: Γ) Δ) := ⟨g₁, d₁, A :: A :: g₂', d₂,
        .right A (.right A hg'), hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ (A :: A :: g₂') ++ d₂ → F ∈ (A :: g₂') ++ d₂ := by
      intro F hF
      simp only [List.mem_append, List.mem_cons] at hF ⊢
      rcases hF with (hA | hA | hF) | hF
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr hF)
      · exact Or.inr hF
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) (listFormulaPredSymbols_mono hmem)
      (fun _ h => h) (listFormulaConstSymbols_mono hmem)
      (fun _ h => h) (listFormulaFV_mono hmem)
      (allNoEq_mono (fun _ h => h) hmem)⟩
    · intro h
      simpa using lkBot_contractLeft_at [C] A g₂' d₂ (by simpa using h)

theorem interpolation_exists_contractRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A, A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A, A])) := ⟨g₁, d₁' ++ [A, A], g₂, d₂, hg,
        hd'.append_left [A, A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₁ ++ (d₁' ++ [A, A]) → F ∈ g₁ ++ (d₁' ++ [A]) := by
      intro F hF
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hF ⊢
      rcases hF with hF | hF | hA | hA
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
      · exact Or.inr (Or.inr hA)
      · exact Or.inr (Or.inr hA)
    refine ⟨C, isInterpolant_transport hI ?_ id (listFormulaPredSymbols_mono hmem) (fun _ h => h)
      (listFormulaConstSymbols_mono hmem) (fun _ h => h)
      (listFormulaFV_mono hmem) (fun _ h => h)
      (allNoEq_mono hmem (fun _ h => h))⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [A, A]) ++ [C]⟩ at h
      simpa [List.append_assoc] using lkBot_contractRight_at g₁ d₁' A [C] (by
          simpa [List.append_assoc] using h)
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A, A])) := ⟨g₁, d₁, g₂, d₂' ++ [A, A], hg,
        hd'.append_right [A, A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hmem : ∀ F, F ∈ g₂ ++ (d₂' ++ [A, A]) → F ∈ g₂ ++ (d₂' ++ [A]) := by
      intro F hF
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hF ⊢
      rcases hF with hF | hF | hA | hA
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
      · exact Or.inr (Or.inr hA)
      · exact Or.inr (Or.inr hA)
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) (listFormulaPredSymbols_mono hmem)
      (fun _ h => h) (listFormulaConstSymbols_mono hmem)
      (fun _ h => h) (listFormulaFV_mono hmem)
      (allNoEq_mono (fun _ h => h) hmem)⟩
    · intro h
      exact lkBot_contractRight_end ([C] ++ g₂) d₂' A (by simpa [List.append_assoc] using h)

theorem interpolation_exists_exchangeLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (Γ : List (FormulaN L))
    (A B : FormulaN L)
    (Δ Λ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ ++ [A, B] ++ Δ, succedent := Λ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ ++ [B, A] ++ Δ, succedent := Λ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  obtain ⟨g₁', g₂', hg', hm₁, hm₂, hm₁', hm₂'⟩ := hg.swap_mid
  let q : SequentPartition (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ) := ⟨g₁', d₁, g₂', d₂, hg', hd⟩
  obtain ⟨C, hI⟩ := ih q
  have lift₁ : ∀ F, F ∈ g₁' ++ d₁ → F ∈ g₁ ++ d₁ := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl (hm₁ F hF))
    · exact List.mem_append.mpr (Or.inr hF)
  have lift₂ : ∀ F, F ∈ g₂' ++ d₂ → F ∈ g₂ ++ d₂ := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl (hm₂ F hF))
    · exact List.mem_append.mpr (Or.inr hF)
  refine ⟨C, isInterpolant_transport hI ?_ ?_ (listFormulaPredSymbols_mono lift₁)
    (listFormulaPredSymbols_mono lift₂)
    (listFormulaConstSymbols_mono lift₁)
    (listFormulaConstSymbols_mono lift₂)
    (listFormulaFV_mono lift₁)
    (listFormulaFV_mono lift₂) ?_⟩
  · intro h
    exact lkBot_mem_equiv_antecedent g₁' g₁ (d₁ ++ [C]) hm₁' hm₁ h
  · intro h
    exact lkBot_mem_equiv_antecedent ([C] ++ g₂') ([C] ++ g₂) d₂
      (by intro F hF; simp only [List.mem_append, List.mem_singleton] at hF ⊢
          exact hF.elim Or.inl (fun h => Or.inr (hm₂' F h)))
      (by intro F hF; simp only [List.mem_append, List.mem_singleton] at hF ⊢
          exact hF.elim Or.inl (fun h => Or.inr (hm₂ F h)))
      h
  · intro h F hF
    apply h F
    simp only [List.mem_append] at hF ⊢
    rcases hF with ((hF | hF) | hF) | hF
    · exact Or.inl (Or.inl (Or.inl (hm₁ F hF)))
    · exact Or.inl (Or.inl (Or.inr hF))
    · exact Or.inl (Or.inr (hm₂ F hF))
    · exact Or.inr hF

theorem interpolation_exists_exchangeRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (Γ Δ : List (FormulaN L))
    (A B : FormulaN L)
    (Λ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A, B] ++ Λ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [B, A] ++ Λ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  obtain ⟨d₁', d₂', hd', hm₁, hm₂, hm₁', hm₂'⟩ := hd.swap_mid
  let q : SequentPartition (Sequent.mk Γ (Δ ++ [A, B] ++ Λ)) := ⟨g₁, d₁', g₂, d₂', hg, hd'⟩
  obtain ⟨C, hI⟩ := ih q
  have lift₁ : ∀ F, F ∈ g₁ ++ d₁' → F ∈ g₁ ++ d₁ := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl hF)
    · exact List.mem_append.mpr (Or.inr (hm₁ F hF))
  have lift₂ : ∀ F, F ∈ g₂ ++ d₂' → F ∈ g₂ ++ d₂ := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl hF)
    · exact List.mem_append.mpr (Or.inr (hm₂ F hF))
  refine ⟨C, isInterpolant_transport hI ?_ ?_ (listFormulaPredSymbols_mono lift₁)
    (listFormulaPredSymbols_mono lift₂)
    (listFormulaConstSymbols_mono lift₁)
    (listFormulaConstSymbols_mono lift₂)
    (listFormulaFV_mono lift₁)
    (listFormulaFV_mono lift₂) ?_⟩
  · intro h
    exact lkBot_mem_equiv_succedent g₁ d₁' d₁ [C] hm₁' hm₁ h
  · intro h
    simpa using lkBot_mem_equiv_succedent ([C] ++ g₂) d₂' d₂ [] hm₂' hm₂ (by simpa using h)
  · intro h F hF
    apply h F
    simp only [List.mem_append] at hF ⊢
    rcases hF with ((hF | hF) | hF) | hF
    · exact Or.inl (Or.inl (Or.inl hF))
    · exact Or.inl (Or.inl (Or.inr (hm₁ F hF)))
    · exact Or.inl (Or.inr hF)
    · exact Or.inr (hm₂ F hF)

theorem interpolation_exists_andLeftL (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A.conj B :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · let q : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨A :: g₁', d₁, g₂, d₂, .left A hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_cons_replace (rest := g₁') (tail := d₁)
      (formulaPredSymbolsN_conj_left A B)
    have hc := listFormulaConstSymbols_cons_replace (rest := g₁') (tail := d₁)
      (formulaConstSymbolsN_conj_left A B)
    have hv := listFormulaFV_cons_replace (rest := g₁') (tail := d₁) (formulaFV_conj_left A B)
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel (allNoEq_cons_replace (fun h => h.1)) (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      exact lkBot_onePremise (.andLeftL A B g₁' (d₁ ++ [C])) h
  · let q : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨g₁, d₁, A :: g₂', d₂, .right A hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_cons_replace (rest := g₂') (tail := d₂)
      (formulaPredSymbolsN_conj_left A B)
    have hc := listFormulaConstSymbols_cons_replace (rest := g₂') (tail := d₂)
      (formulaConstSymbolsN_conj_left A B)
    have hv := listFormulaFV_cons_replace (rest := g₂') (tail := d₂) (formulaFV_conj_left A B)
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) (allNoEq_cons_replace (fun h => h.1)))⟩
    · intro h
      have h₁ := lkBot_exchangeLeft_at [] C A g₂' d₂ (by simpa using h)
      have h₂ := lkBot_onePremise (.andLeftL A B (C :: g₂') d₂) (by simpa using h₁)
      simpa using lkBot_exchangeLeft_at [] (.conj A B) C g₂' d₂ (by simpa using h₂)

theorem interpolation_exists_andLeftR (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := B :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A.conj B :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · let q : SequentPartition (Sequent.mk (B :: Γ) Δ) := ⟨B :: g₁', d₁, g₂, d₂, .left B hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_cons_replace (rest := g₁') (tail := d₁)
      (formulaPredSymbolsN_conj_right A B)
    have hc := listFormulaConstSymbols_cons_replace (rest := g₁') (tail := d₁)
      (formulaConstSymbolsN_conj_right A B)
    have hv := listFormulaFV_cons_replace (rest := g₁') (tail := d₁) (formulaFV_conj_right A B)
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel (allNoEq_cons_replace (fun h => h.2)) (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      exact lkBot_onePremise (.andLeftR A B g₁' (d₁ ++ [C])) h
  · let q : SequentPartition (Sequent.mk (B :: Γ) Δ) := ⟨g₁, d₁, B :: g₂', d₂, .right B hg', hd⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_cons_replace (rest := g₂') (tail := d₂)
      (formulaPredSymbolsN_conj_right A B)
    have hc := listFormulaConstSymbols_cons_replace (rest := g₂') (tail := d₂)
      (formulaConstSymbolsN_conj_right A B)
    have hv := listFormulaFV_cons_replace (rest := g₂') (tail := d₂) (formulaFV_conj_right A B)
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) (allNoEq_cons_replace (fun h => h.2)))⟩
    · intro h
      have h₁ := lkBot_exchangeLeft_at [] C B g₂' d₂ (by simpa using h)
      have h₂ := lkBot_onePremise (.andLeftR A B (C :: g₂') d₂) (by simpa using h₁)
      simpa using lkBot_exchangeLeft_at [] (.conj A B) C g₂' d₂ (by simpa using h₂)

theorem interpolation_exists_orRightL (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A.disj B] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁, d₁' ++ [A], g₂, d₂, hg, hd'.append_left [A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_snoc_replace (head := g₁) (tail := d₁')
      (formulaPredSymbolsN_disj_left A B)
    have hc := listFormulaConstSymbols_snoc_replace (head := g₁) (tail := d₁')
      (formulaConstSymbolsN_disj_left A B)
    have hv := listFormulaFV_snoc_replace (head := g₁) (tail := d₁') (formulaFV_disj_left A B)
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel (allNoEq_snoc_replace (fun h => h.1)) (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [A]) ++ [C]⟩ at h
      have h₁ := lkBot_exchangeRight_at g₁ d₁' A C [] (by simpa [List.append_assoc] using h)
      have h₂ := lkBot_onePremise (.orRightL A B g₁ (d₁' ++ [C])) (by simpa [List.append_assoc] using h₁)
      simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.disj A B) []
          (by simpa [List.append_assoc] using h₂)
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁, d₁, g₂, d₂' ++ [A], hg, hd'.append_right [A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_snoc_replace (head := g₂) (tail := d₂')
      (formulaPredSymbolsN_disj_left A B)
    have hc := listFormulaConstSymbols_snoc_replace (head := g₂) (tail := d₂')
      (formulaConstSymbolsN_disj_left A B)
    have hv := listFormulaFV_snoc_replace (head := g₂) (tail := d₂') (formulaFV_disj_left A B)
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) (allNoEq_snoc_replace (fun h => h.1)))⟩
    · intro h
      exact lkBot_onePremise (.orRightL A B ([C] ++ g₂) d₂') (by simpa [List.append_assoc] using h)

theorem interpolation_exists_orRightR (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [B] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A.disj B] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [B])) := ⟨g₁, d₁' ++ [B], g₂, d₂, hg, hd'.append_left [B]⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_snoc_replace (head := g₁) (tail := d₁')
      (formulaPredSymbolsN_disj_right A B)
    have hc := listFormulaConstSymbols_snoc_replace (head := g₁) (tail := d₁')
      (formulaConstSymbolsN_disj_right A B)
    have hv := listFormulaFV_snoc_replace (head := g₁) (tail := d₁') (formulaFV_disj_right A B)
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel (allNoEq_snoc_replace (fun h => h.2)) (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [B]) ++ [C]⟩ at h
      have h₁ := lkBot_exchangeRight_at g₁ d₁' B C [] (by simpa [List.append_assoc] using h)
      have h₂ := lkBot_onePremise (.orRightR A B g₁ (d₁' ++ [C])) (by simpa [List.append_assoc] using h₁)
      simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.disj A B) []
          (by simpa [List.append_assoc] using h₂)
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [B])) := ⟨g₁, d₁, g₂, d₂' ++ [B], hg, hd'.append_right [B]⟩
    obtain ⟨C, hI⟩ := ih q
    have hp := listFormulaPredSymbols_snoc_replace (head := g₂) (tail := d₂')
      (formulaPredSymbolsN_disj_right A B)
    have hc := listFormulaConstSymbols_snoc_replace (head := g₂) (tail := d₂')
      (formulaConstSymbolsN_disj_right A B)
    have hv := listFormulaFV_snoc_replace (head := g₂) (tail := d₂') (formulaFV_disj_right A B)
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) (allNoEq_snoc_replace (fun h => h.2)))⟩
    · intro h
      exact lkBot_onePremise (.orRightR A B ([C] ++ g₂) d₂') (by simpa [List.append_assoc] using h)

theorem interpolation_exists_implRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ ++ [B] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A.impl B] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk (A :: Γ) (Δ ++ [B])) := ⟨A :: g₁, d₁' ++ [B], g₂, d₂,
        .left A hg, hd'.append_left [B]⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ (A :: g₁) ++ (d₁' ++ [B]) → ∃ G ∈ g₁ ++ (d₁' ++ [.impl A B]),
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hFA | hF
        · subst F
          refine ⟨.impl A B, ?_, formulaPredSymbolsN_impl_left A B, formulaConstSymbolsN_impl_left A B,
            formulaFV_impl_left A B, fun h => h.1⟩
          exact List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp)))
        · exact ⟨F, List.mem_append.mpr (Or.inl hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · rcases List.mem_append.mp hF with hF | hF
        · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · have hFB : F = B := by simpa using hF
          subst F
          refine ⟨.impl A B, ?_, formulaPredSymbolsN_impl_right A B, formulaConstSymbolsN_impl_right A B,
            formulaFV_impl_right A B, fun h => h.2⟩
          exact List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp)))
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF
      obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF
      obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF
      obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ (A :: g₁) ++ (d₁' ++ [B]) → ∃ G ∈ g₁ ++ (d₁' ++ [.impl A B]),
          formulaNoEq G → formulaNoEq F := by
      intro F hF
      obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel hn (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨A :: g₁, (d₁' ++ [B]) ++ [C]⟩ at h
      have h₁ := lkBot_exchangeRight_at (A :: g₁) d₁' B C [] (by simpa [List.append_assoc] using h)
      have h₂ := lkBot_onePremise (.implRight A B g₁ (d₁' ++ [C])) (by simpa [List.append_assoc] using h₁)
      simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.impl A B) []
          (by simpa [List.append_assoc] using h₂)
  · let q : SequentPartition (Sequent.mk (A :: Γ) (Δ ++ [B])) := ⟨g₁, d₁, A :: g₂, d₂' ++ [B],
        .right A hg, hd'.append_right [B]⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ (A :: g₂) ++ (d₂' ++ [B]) → ∃ G ∈ g₂ ++ (d₂' ++ [.impl A B]),
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hFA | hF
        · subst F
          refine ⟨.impl A B, ?_, formulaPredSymbolsN_impl_left A B, formulaConstSymbolsN_impl_left A B,
            formulaFV_impl_left A B, fun h => h.1⟩
          exact List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp)))
        · exact ⟨F, List.mem_append.mpr (Or.inl hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · rcases List.mem_append.mp hF with hF | hF
        · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · have hFB : F = B := by simpa using hF
          subst F
          refine ⟨.impl A B, ?_, formulaPredSymbolsN_impl_right A B, formulaConstSymbolsN_impl_right A B,
            formulaFV_impl_right A B, fun h => h.2⟩
          exact List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp)))
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF
      obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF
      obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF
      obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ (A :: g₂) ++ (d₂' ++ [B]) → ∃ G ∈ g₂ ++ (d₂' ++ [.impl A B]),
          formulaNoEq G → formulaNoEq F := by
      intro F hF
      obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) hn)⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨[C] ++ (A :: g₂), d₂' ++ [B]⟩ at h
      have h₁ := lkBot_exchangeLeft_at [] C A g₂ (d₂' ++ [B]) (by simpa using h)
      simpa using lkBot_onePremise (.implRight A B (C :: g₂) d₂') (by simpa using h₁)

theorem interpolation_exists_negLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A.neg :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁', d₁ ++ [A], g₂, d₂, hg', hd.append_left [A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ g₁' ++ (d₁ ++ [A]) → ∃ G ∈ (.neg A :: g₁') ++ d₁,
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)),
          fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · rcases List.mem_append.mp hF with hF | hF
        · exact ⟨F, List.mem_append.mpr (Or.inr hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · have hFA : F = A := by simpa using hF
          subst F
          exact ⟨.neg A, List.mem_append.mpr (Or.inl (List.Mem.head _)),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ g₁' ++ (d₁ ++ [A]) → ∃ G ∈ (.neg A :: g₁') ++ d₁, formulaNoEq G → formulaNoEq F := by
      intro F hF; obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel hn (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      change lkBotProvable botP hBotArity ⟨g₁', (d₁ ++ [A]) ++ [C]⟩ at h
      have h₁ := lkBot_exchangeRight_at g₁' d₁ A C [] (by simpa [List.append_assoc] using h)
      simpa [List.append_assoc] using lkBot_onePremise (.negLeft A g₁' (d₁ ++ [C]))
        (by simpa [List.append_assoc] using h₁)
  · let q : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁, d₁, g₂', d₂ ++ [A], hg', hd.append_right [A]⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ g₂' ++ (d₂ ++ [A]) → ∃ G ∈ (.neg A :: g₂') ++ d₂,
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)),
          fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · rcases List.mem_append.mp hF with hF | hF
        · exact ⟨F, List.mem_append.mpr (Or.inr hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · have hFA : F = A := by simpa using hF
          subst F
          exact ⟨.neg A, List.mem_append.mpr (Or.inl (List.Mem.head _)),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ g₂' ++ (d₂ ++ [A]) → ∃ G ∈ (.neg A :: g₂') ++ d₂, formulaNoEq G → formulaNoEq F := by
      intro F hF; obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) hn)⟩
    · intro h
      have h₁ := lkBot_onePremise (.negLeft A (C :: g₂') d₂) (by simpa [List.append_assoc] using h)
      simpa using lkBot_exchangeLeft_at [] (.neg A) C g₂' d₂ (by simpa using h₁)

theorem interpolation_exists_negRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A.neg] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · let q : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨A :: g₁, d₁', g₂, d₂, .left A hg, hd'⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ (A :: g₁) ++ d₁' → ∃ G ∈ g₁ ++ (d₁' ++ [.neg A]),
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hFA | hF
        · subst F
          exact ⟨.neg A, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp))),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · exact ⟨F, List.mem_append.mpr (Or.inl hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)),
          fun _ h => h, fun _ h => h, fun _ h => h, id⟩
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ (A :: g₁) ++ d₁' → ∃ G ∈ g₁ ++ (d₁' ++ [.neg A]), formulaNoEq G → formulaNoEq F := by
      intro F hF; obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI ?_ id hp (fun _ h => h) hc (fun _ h => h) hv (fun _ h => h)
      (allNoEq_rel hn (fun F hF => ⟨F, hF, id⟩))⟩
    · intro h
      have h₁ := lkBot_onePremise (.negRight A g₁ (d₁' ++ [C])) h
      simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.neg A) []
          (by simpa [List.append_assoc] using h₁)
  · let q : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨g₁, d₁, A :: g₂, d₂', .right A hg, hd'⟩
    obtain ⟨C, hI⟩ := ih q
    have hRel : ∀ F, F ∈ (A :: g₂) ++ d₂' → ∃ G ∈ g₂ ++ (d₂' ++ [.neg A]),
          (formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) ∧
          (formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) ∧
          (formulaFVN F ⊆ formulaFVN G) ∧
          (formulaNoEq G → formulaNoEq F) := by
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hFA | hF
        · subst F
          exact ⟨.neg A, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr (by simp))),
            fun _ h => h, fun _ h => h, fun _ h => h, id⟩
        · exact ⟨F, List.mem_append.mpr (Or.inl hF), fun _ h => h, fun _ h => h, fun _ h => h, id⟩
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)),
          fun _ h => h, fun _ h => h, fun _ h => h, id⟩
    have hp := listFormulaPredSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, hP, _, _, _⟩ := hRel F hF
      exact ⟨G, hG, hP⟩)
    have hc := listFormulaConstSymbols_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, hC, _, _⟩ := hRel F hF
      exact ⟨G, hG, hC⟩)
    have hv := listFormulaFV_formula_sub (by
      intro F hF; obtain ⟨G, hG, _, _, hV, _⟩ := hRel F hF
      exact ⟨G, hG, hV⟩)
    have hn : ∀ F, F ∈ (A :: g₂) ++ d₂' → ∃ G ∈ g₂ ++ (d₂' ++ [.neg A]), formulaNoEq G → formulaNoEq F := by
      intro F hF; obtain ⟨G, hG, _, _, _, hN⟩ := hRel F hF
      exact ⟨G, hG, hN⟩
    refine ⟨C, isInterpolant_transport hI id ?_ (fun _ h => h) hp (fun _ h => h) hc (fun _ h => h) hv
      (allNoEq_rel (fun F hF => ⟨F, hF, id⟩) hn)⟩
    · intro h
      have h₁ := lkBot_exchangeLeft_at [] C A g₂ d₂' (by simpa using h)
      simpa using lkBot_onePremise (.negRight A (C :: g₂) d₂') (by simpa using h₁)

private theorem interpolation_exists_allLeft_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A t₀ x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (d₁ g₂ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₁' : List (FormulaN L))
    (hg' : List.Interleaving g₁' g₂ Γ)
    (hg : List.Interleaving (FormulaN.all x A :: g₁') g₂ (FormulaN.all x A :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (FormulaN.all x A :: Γ) (Δ))
          { gamma1 := FormulaN.all x A :: g₁', delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A t₀ x
  let q : SequentPartition (Sequent.mk (X :: Γ) Δ) := ⟨X :: g₁', d₁, g₂, d₂, .left X hg', hd⟩
  obtain ⟨C, hI⟩ := ih q
  have hLeft : lkBotProvable botP hBotArity ⟨.all x A :: g₁', d₁ ++ [C]⟩ :=
    lkBot_onePremise (.allLeft t₀ x A g₁' (d₁ ++ [C]) hfree) (by simpa [q, X] using hI.left_provable)
  have hRight : lkBotProvable botP hBotArity ⟨[C] ++ g₂, d₂⟩ := hI.right_provable
  let side₁ := (.all x A :: g₁') ++ d₁
  let cs := (termConstList t₀).filter (fun c => ¬ listFormulaConstSymbols side₁ c)
  obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ := interpolant_fix_consts
      (.all x A :: g₁') d₁ g₂ d₂ C cs hLeft hRight (by
        intro c hc F hF hFc
        have hnot := of_decide_eq_true (List.mem_filter.mp hc).2
        exact hnot ⟨F, by simpa [side₁] using hF, hFc⟩)
  let vs := (termFVList t₀).filter (fun v => ¬ listFormulaFV side₁ v)
  obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ := interpolant_fix_fvs
      (.all x A :: g₁') d₁ g₂ d₂ C₁ vs hLeft₁ hRight₁ (by
        intro v hv F hF hFv
        have hnot := of_decide_eq_true (List.mem_filter.mp hv).2
        exact hnot ⟨F, by simpa [side₁] using hF, hFv⟩)
  have hp := listFormulaPredSymbols_cons_replace (rest := g₁') (tail := d₁)
    (formulaPredSymbolsN_subst_le_all A t₀ x)
  have liftConst : ∀ c, c ∉ cs → listFormulaConstSymbols ((X :: g₁') ++ d₁) c →
      listFormulaConstSymbols side₁ c := by
    intro c hcs hc
    rcases hc with ⟨F, hF, hFc⟩
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with hFX | hF
      · subst F
        rcases formulaConstSymbolsN_formulaSubst A t₀ x c hFc with hA | ht
        · exact ⟨.all x A, by simp [side₁], hA⟩
        · exact Classical.byContradiction (fun hnot =>
            hcs (List.mem_filter.mpr ⟨(termConstList_mem t₀ c).mpr ht, decide_eq_true hnot⟩))
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)), hFc⟩
    · exact ⟨F, List.mem_append.mpr (Or.inr hF), hFc⟩
  have liftFV : ∀ v, v ∉ vs → listFormulaFV ((X :: g₁') ++ d₁) v → listFormulaFV side₁ v := by
    intro v hvs hv
    rcases hv with ⟨F, hF, hFv⟩
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with hFX | hF
      · subst F
        rcases formulaFV_formulaSubst A t₀ x v hFv with
          ⟨hA, hvx⟩ | ht
        · exact ⟨.all x A, by simp [side₁], ⟨hA, hvx⟩⟩
        · exact Classical.byContradiction (fun hnot =>
            hvs (List.mem_filter.mpr ⟨(termFVList_mem t₀ v).mpr ht, decide_eq_true hnot⟩))
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)), hFv⟩
    · exact ⟨F, List.mem_append.mpr (Or.inr hF), hFv⟩
  have hn := allNoEq_cons_replace (X := X) (Y := .all x A) (rest := g₁') (tail := d₁)
    (fun h => formulaSubstN_noEq A t₀ x h)
  refine ⟨C₂, ?_⟩
  refine
    { left_provable := hLeft₂
      right_provable := hRight₂
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rw [hPred₂, hPred₁] at hP
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hp P hi.1, hi.2⟩
  · intro c hc
    rw [hConst₂] at hc
    obtain ⟨hcC, hcs⟩ := hConst₁ c hc
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨liftConst c hcs hi.1, hi.2⟩
  · intro v hv
    obtain ⟨hvC₁, hvs⟩ := hFV₂ v hv
    have hvC := hFV₁ v hvC₁
    have hi := hI.fv_common v hvC
    dsimp [q] at hi
    exact ⟨liftFV v hvs hi.1, hi.2⟩
  · intro h
    apply hNoEq₂
    apply hNoEq₁
    apply hI.no_eq
    exact allNoEq_rel
      (p := { gamma1 := .all x A :: g₁'
              delta1 := d₁
              gamma2 := g₂
              delta2 := d₂
              gamma_partition := hg
              delta_partition := hd })
      (q := q) hn (fun F hF => ⟨F, hF, id⟩) h

private theorem interpolation_exists_allLeft_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A t₀ x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₂' : List (FormulaN L))
    (hg' : List.Interleaving g₁ g₂' Γ)
    (hg : List.Interleaving g₁ (FormulaN.all x A :: g₂') (FormulaN.all x A :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (FormulaN.all x A :: Γ) (Δ))
          { gamma1 := g₁, delta1 := d₁, gamma2 := FormulaN.all x A :: g₂', delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A t₀ x
  let q : SequentPartition (Sequent.mk (X :: Γ) Δ) := ⟨g₁, d₁, X :: g₂', d₂, .right X hg', hd⟩
  obtain ⟨C, hI⟩ := ih q
  have hLeft : lkBotProvable botP hBotArity ⟨g₁, d₁ ++ [C]⟩ := hI.left_provable
  have hRight : lkBotProvable botP hBotArity ⟨[C] ++ (.all x A :: g₂'), d₂⟩ := by
    have h := hI.right_provable
    change lkBotProvable botP hBotArity ⟨[C] ++ (X :: g₂'), d₂⟩ at h
    have h₁ := lkBot_exchangeLeft_at [] C X g₂' d₂ (by simpa using h)
    have h₂ := lkBot_onePremise (.allLeft t₀ x A (C :: g₂') d₂ hfree) (by simpa [X] using h₁)
    simpa using lkBot_exchangeLeft_at [] (.all x A) C g₂' d₂ (by simpa using h₂)
  let side₂ := (.all x A :: g₂') ++ d₂
  let cs := (termConstList t₀).filter (fun c => ¬ listFormulaConstSymbols side₂ c)
  obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ := interpolant_fix_consts_right
      g₁ d₁ (.all x A :: g₂') d₂ C cs hLeft hRight (by
        intro c hc F hF hFc
        have hnot := of_decide_eq_true (List.mem_filter.mp hc).2
        exact hnot ⟨F, by simpa [side₂] using hF, hFc⟩)
  let vs := (termFVList t₀).filter (fun v => ¬ listFormulaFV side₂ v)
  obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ := interpolant_fix_fvs_right
      g₁ d₁ (.all x A :: g₂') d₂ C₁ vs hLeft₁ hRight₁ (by
        intro v hv F hF hFv
        have hnot := of_decide_eq_true (List.mem_filter.mp hv).2
        exact hnot ⟨F, by simpa [side₂] using hF, hFv⟩)
  have hp := listFormulaPredSymbols_cons_replace (rest := g₂') (tail := d₂)
    (formulaPredSymbolsN_subst_le_all A t₀ x)
  have liftConst : ∀ c, c ∉ cs → listFormulaConstSymbols ((X :: g₂') ++ d₂) c →
      listFormulaConstSymbols side₂ c := by
    intro c hcs hc
    rcases hc with ⟨F, hF, hFc⟩
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with hFX | hF
      · subst F
        rcases formulaConstSymbolsN_formulaSubst A t₀ x c hFc with hA | ht
        · exact ⟨.all x A, by simp [side₂], hA⟩
        · exact Classical.byContradiction (fun hnot =>
            hcs (List.mem_filter.mpr ⟨(termConstList_mem t₀ c).mpr ht, decide_eq_true hnot⟩))
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)), hFc⟩
    · exact ⟨F, List.mem_append.mpr (Or.inr hF), hFc⟩
  have liftFV : ∀ v, v ∉ vs → listFormulaFV ((X :: g₂') ++ d₂) v → listFormulaFV side₂ v := by
    intro v hvs hv
    rcases hv with ⟨F, hF, hFv⟩
    rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with hFX | hF
      · subst F
        rcases formulaFV_formulaSubst A t₀ x v hFv with
          ⟨hA, hvx⟩ | ht
        · exact ⟨.all x A, by simp [side₂], ⟨hA, hvx⟩⟩
        · exact Classical.byContradiction (fun hnot =>
            hvs (List.mem_filter.mpr ⟨(termFVList_mem t₀ v).mpr ht, decide_eq_true hnot⟩))
      · exact ⟨F, List.mem_append.mpr (Or.inl (List.Mem.tail _ hF)), hFv⟩
    · exact ⟨F, List.mem_append.mpr (Or.inr hF), hFv⟩
  have hn := allNoEq_cons_replace (X := X) (Y := .all x A) (rest := g₂') (tail := d₂)
    (fun h => formulaSubstN_noEq A t₀ x h)
  refine ⟨C₂, ?_⟩
  refine
    { left_provable := hLeft₂
      right_provable := hRight₂
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rw [hPred₂, hPred₁] at hP
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hi.1, hp P hi.2⟩
  · intro c hc
    rw [hConst₂] at hc
    obtain ⟨hcC, hcs⟩ := hConst₁ c hc
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hi.1, liftConst c hcs hi.2⟩
  · intro v hv
    obtain ⟨hvC₁, hvs⟩ := hFV₂ v hv
    have hvC := hFV₁ v hvC₁
    have hi := hI.fv_common v hvC
    dsimp [q] at hi
    exact ⟨hi.1, liftFV v hvs hi.2⟩
  · intro h
    apply hNoEq₂
    apply hNoEq₁
    apply hI.no_eq
    exact allNoEq_rel
      (p := { gamma1 := g₁
              delta1 := d₁
              gamma2 := .all x A :: g₂'
              delta2 := d₂
              gamma_partition := hg
              delta_partition := hd })
      (q := q) (fun F hF => ⟨F, hF, id⟩) hn h

theorem interpolation_exists_allLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A t₀ x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := FormulaN.all x A :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · exact interpolation_exists_allLeft_left L botP hBotArity t₀ x A Γ Δ hfree (ih) d₁ g₂ d₂ hd g₁' hg' hg
  · exact interpolation_exists_allLeft_right L botP hBotArity t₀ x A Γ Δ hfree (ih) g₁ d₁ d₂ hd g₂' hg' hg

private theorem interpolation_exists_allRight_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A (Term.var y) x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ g₂ d₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₁' : List (FormulaN L))
    (hd' : List.Interleaving d₁' d₂ Δ)
    (hd : List.Interleaving (d₁' ++ [FormulaN.all x A]) d₂ (Δ ++ [FormulaN.all x A]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))
          { gamma1 := g₁, delta1 := d₁' ++ [FormulaN.all x A], gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A (.var y) x
  let q : SequentPartition (Sequent.mk Γ (Δ ++ [X])) := ⟨g₁, d₁' ++ [X], g₂, d₂, hg, hd'.append_left [X]⟩
  obtain ⟨C, hI⟩ := ih q
  have hFreshOther : ∀ F ∈ g₂ ++ d₂, y ∉ formulaFVN F := by
    intro F hF hy
    apply hfresh F ?_ hy
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl (hg.mem_right hF))
    · exact List.mem_append.mpr (Or.inr (hd.mem_right hF))
  have hyC : y ∉ formulaFVN C := by
    intro hy
    have hi := (hI.fv_common y hy).2
    dsimp [q] at hi
    exact let ⟨F, hF, hyF⟩ := hi
      hFreshOther F hF hyF
  have hp := listFormulaPredSymbols_snoc_replace (head := g₁) (tail := d₁')
    (formulaPredSymbolsN_subst_le_all A (.var y) x)
  have hc := listFormulaConstSymbols_snoc_replace (head := g₁) (tail := d₁')
    (formulaConstSymbolsN_subst_var_le_all A y x)
  have hfv : formulaFVN C ⊆ listFormulaFV (g₁ ++ (d₁' ++ [.all x A])) ∩ listFormulaFV (g₂ ++ d₂) := by
    intro v hv
    have hi := hI.fv_common v hv
    dsimp [q] at hi
    exact listFormulaFV_snoc_replace_fresh (formulaFV_subst_var_le_all_union A y x) hFreshOther v hi
  have hn := allNoEq_snoc_replace (X := X) (Y := .all x A) (head := g₁) (tail := d₁')
    (fun h => formulaSubstN_noEq A (.var y) x h)
  refine ⟨C, ?_⟩
  refine
    { left_provable := ?_
      right_provable := hI.right_provable
      pred_common := ?_
      const_common := ?_
      fv_common := hfv
      no_eq := ?_ }
  · have h := hI.left_provable
    change lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [X]) ++ [C]⟩ at h
    have h₁ := lkBot_exchangeRight_at g₁ d₁' X C [] (by simpa [List.append_assoc] using h)
    have hfresh' : ∀ F ∈ (Sequent.mk g₁ ((d₁' ++ [C]) ++ [.all x A])).antecedent ++ (Sequent.mk g₁
            ((d₁' ++ [C]) ++ [.all x A])).succedent,
          y ∉ formulaFVN F := by
      intro F hF
      change F ∈ g₁ ++ ((d₁' ++ [C]) ++ [.all x A]) at hF
      rcases List.mem_append.mp hF with hF | hF
      · exact hfresh F (List.mem_append.mpr (Or.inl (hg.mem_left hF)))
      · rcases List.mem_append.mp hF with hF | hF
        · rcases List.mem_append.mp hF with hF | hF
          · exact hfresh F (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl (hd'.mem_left hF)))))
          · have hFC : F = C := by simpa using hF
            subst F
            exact hyC
        · have hFall : F = .all x A := by simpa using hF
          subst F
          exact hfresh _ (by simp)
    have h₂ := lkBot_onePremise (.allRight y x A g₁ (d₁' ++ [C]) hfresh' hfree)
      (by simpa [X, List.append_assoc] using h₁)
    simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.all x A) []
        (by simpa [List.append_assoc] using h₂)
  · intro P hP hne
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hp P hi.1, hi.2⟩
  · intro c hcC
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hc c hi.1, hi.2⟩
  · exact hI.no_eq ∘ allNoEq_rel hn (fun F hF => ⟨F, hF, id⟩)

private theorem interpolation_exists_allRight_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A (Term.var y) x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ g₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₂' : List (FormulaN L))
    (hd' : List.Interleaving d₁ d₂' Δ)
    (hd : List.Interleaving d₁ (d₂' ++ [FormulaN.all x A]) (Δ ++ [FormulaN.all x A]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))
          { gamma1 := g₁, delta1 := d₁, gamma2 := g₂, delta2 := d₂' ++ [FormulaN.all x A], gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A (.var y) x
  let q : SequentPartition (Sequent.mk Γ (Δ ++ [X])) := ⟨g₁, d₁, g₂, d₂' ++ [X], hg, hd'.append_right [X]⟩
  obtain ⟨C, hI⟩ := ih q
  have hFreshOther : ∀ F ∈ g₁ ++ d₁, y ∉ formulaFVN F := by
    intro F hF hy
    apply hfresh F ?_ hy
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl (hg.mem_left hF))
    · exact List.mem_append.mpr (Or.inr (hd.mem_left hF))
  have hyC : y ∉ formulaFVN C := by
    intro hy
    have hi := (hI.fv_common y hy).1
    dsimp [q] at hi
    exact let ⟨F, hF, hyF⟩ := hi
      hFreshOther F hF hyF
  have hp := listFormulaPredSymbols_snoc_replace (head := g₂) (tail := d₂')
    (formulaPredSymbolsN_subst_le_all A (.var y) x)
  have hc := listFormulaConstSymbols_snoc_replace (head := g₂) (tail := d₂')
    (formulaConstSymbolsN_subst_var_le_all A y x)
  have hfv : formulaFVN C ⊆ listFormulaFV (g₁ ++ d₁) ∩ listFormulaFV (g₂ ++ (d₂' ++ [.all x A])) := by
    intro v hv
    have hi := hI.fv_common v hv
    dsimp [q] at hi
    have mapped := listFormulaFV_snoc_replace_fresh (head := g₂) (tail := d₂') (other := g₁ ++ d₁)
      (formulaFV_subst_var_le_all_union A y x)
      hFreshOther v ⟨hi.2, hi.1⟩
    exact ⟨mapped.2, mapped.1⟩
  have hn := allNoEq_snoc_replace (X := X) (Y := .all x A) (head := g₂) (tail := d₂')
    (fun h => formulaSubstN_noEq A (.var y) x h)
  refine ⟨C, ?_⟩
  refine
    { left_provable := hI.left_provable
      right_provable := ?_
      pred_common := ?_
      const_common := ?_
      fv_common := hfv
      no_eq := ?_ }
  · have h := hI.right_provable
    have hfresh' : ∀ F ∈ (Sequent.mk ([C] ++ g₂) (d₂' ++ [.all x A])).antecedent ++ (Sequent.mk ([C] ++ g₂)
            (d₂' ++ [.all x A])).succedent,
          y ∉ formulaFVN F := by
      intro F hF
      change F ∈ ([C] ++ g₂) ++ (d₂' ++ [.all x A]) at hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_append.mp hF with hF | hF
        · have hFC : F = C := by simpa using hF
          subst F
          exact hyC
        · exact hfresh F (List.mem_append.mpr (Or.inl (hg.mem_right hF)))
      · rcases List.mem_append.mp hF with hF | hF
        · exact hfresh F (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl (hd'.mem_right hF)))))
        · have hFall : F = .all x A := by simpa using hF
          subst F
          exact hfresh _ (by simp)
    exact lkBot_onePremise (.allRight y x A ([C] ++ g₂) d₂' hfresh' hfree)
      (by simpa [q, X, List.append_assoc] using h)
  · intro P hP hne
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hi.1, hp P hi.2⟩
  · intro c hcC
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hi.1, hc c hi.2⟩
  · exact hI.no_eq ∘ allNoEq_rel (fun F hF => ⟨F, hF, id⟩) hn

theorem interpolation_exists_allRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A (Term.var y) x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [FormulaN.all x A] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · exact interpolation_exists_allRight_left L botP hBotArity y x A Γ Δ hfresh hfree (ih) g₁ g₂ d₂ hg d₁' hd' hd
  · exact interpolation_exists_allRight_right L botP hBotArity y x A Γ Δ hfresh hfree (ih) g₁ d₁ g₂ hg d₂' hd' hd

end LCS.CutElim.Interpolation
end

