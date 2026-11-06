import LCS.Propositional.LK

namespace LCS.Propositional.LK

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Systems.G.Search

proof_of lkAxiom_valid := by
  -- BEGIN PROOF
    intro v hAnt
    exact ⟨A, List.Mem.head _, hAnt A (List.Mem.head _)⟩


proof_of lkStep1_sound := by
  -- BEGIN PROOF
    cases rule with
    | weakenLeft Γ Δ A =>
      intro hAnt
      exact hprem (fun X hX => hAnt X (List.Mem.tail _ hX))
    | weakenRight Γ Δ A =>
      intro hAnt
      obtain ⟨B, hBm, hBt⟩ := hprem hAnt
      exact ⟨B, List.Mem.tail _ hBm, hBt⟩
    | contractLeft Γ₁ Γ₂ Δ A =>
      -- Premise ant: Γ₁ ++ A :: A :: Γ₂, Conclusion ant: Γ₁ ++ A :: Γ₂
      intro hAnt
      apply hprem; intro X hX
      have : X ∈ Γ₁ ++ A :: Γ₂ := by
        simp only [List.mem_append, List.mem_cons] at hX ⊢
        rcases hX with h | h | h | h <;> simp_all
      exact hAnt X this
    | contractRight Γ Δ₁ Δ₂ A =>
      -- Premise succ: Δ₁ ++ A :: A :: Δ₂, Conclusion succ: Δ₁ ++ A :: Δ₂
      intro hAnt
      obtain ⟨C, hCm, hCt⟩ := hprem hAnt
      refine ⟨C, ?_, hCt⟩
      simp only [List.mem_append, List.mem_cons] at hCm ⊢
      rcases hCm with h | h | h | h <;> simp_all
    | exchangeLeft Γ₁ Γ₂ Δ A B =>
      -- Premise ant: Γ₁ ++ A :: B :: Γ₂, Conclusion ant: Γ₁ ++ B :: A :: Γ₂
      intro hAnt
      apply hprem; intro X hX
      -- hX : X ∈ Γ₁ ++ A :: B :: Γ₂, need X ∈ Γ₁ ++ B :: A :: Γ₂
      have : X ∈ Γ₁ ++ B :: A :: Γ₂ := by
        simp only [List.mem_append, List.mem_cons] at hX ⊢
        rcases hX with h | h | h | h <;> simp_all
      exact hAnt X this
    | exchangeRight Γ Δ₁ Δ₂ A B =>
      -- Premise succ: Δ₁ ++ A :: B :: Δ₂, Conclusion succ: Δ₁ ++ B :: A :: Δ₂
      intro hAnt
      obtain ⟨C, hCm, hCt⟩ := hprem hAnt
      -- hCm : C ∈ Δ₁ ++ A :: B :: Δ₂, need C ∈ Δ₁ ++ B :: A :: Δ₂
      refine ⟨C, ?_, hCt⟩
      simp only [List.mem_append, List.mem_cons] at hCm ⊢
      rcases hCm with h | h | h | h <;> simp_all
    | andLeft1 Γ Δ A B =>
      intro hAnt
      have hConj := hAnt _ (List.Mem.head _)
      simp only [evalExtN, hAnd] at hConj
      have hA : evalExtN v A = BoolVal.T := by
        cases ha : evalExtN v A <;> simp_all
      apply hprem; intro X hX
      match List.mem_cons.mp hX with
      | Or.inl h => exact h ▸ hA
      | Or.inr hX' => exact hAnt X (List.Mem.tail _ hX')
    | andLeft2 Γ Δ A B =>
      intro hAnt
      have hConj := hAnt _ (List.Mem.head _)
      simp only [evalExtN, hAnd] at hConj
      have hB : evalExtN v B = BoolVal.T := by
        cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all
      apply hprem; intro X hX
      match List.mem_cons.mp hX with
      | Or.inl h => exact h ▸ hB
      | Or.inr hX' => exact hAnt X (List.Mem.tail _ hX')
    | orRight1 Γ Δ A B =>
      intro hAnt
      obtain ⟨C, hCm, hCt⟩ := hprem hAnt
      match List.mem_cons.mp hCm with
      | Or.inl h =>
        exact ⟨PropFormulaNormalized.disj A B, List.Mem.head _, by
          simp only [evalExtN, hOr]; rw [h] at hCt; rw [hCt]⟩
      | Or.inr hCm' => exact ⟨C, List.Mem.tail _ hCm', hCt⟩
    | orRight2 Γ Δ A B =>
      intro hAnt
      obtain ⟨C, hCm, hCt⟩ := hprem hAnt
      match List.mem_cons.mp hCm with
      | Or.inl h =>
        exact ⟨PropFormulaNormalized.disj A B, List.Mem.head _, by
          simp only [evalExtN, hOr]; rw [h] at hCt; rw [hCt]
          cases evalExtN v A <;> rfl⟩
      | Or.inr hCm' => exact ⟨C, List.Mem.tail _ hCm', hCt⟩
    | implRight Γ Δ A B =>
      intro hAnt
      cases ha : evalExtN v A with
      | T =>
        obtain ⟨C, hCm, hCt⟩ := hprem (fun X hX =>
          match List.mem_cons.mp hX with
          | Or.inl h => h ▸ ha
          | Or.inr h => hAnt X h)
        match List.mem_cons.mp hCm with
        | Or.inl h =>
          exact ⟨PropFormulaNormalized.impl A B, List.Mem.head _, by
            simp only [evalExtN, hImplies, ha]; rw [h] at hCt; rw [hCt]⟩
        | Or.inr hCm' => exact ⟨C, List.Mem.tail _ hCm', hCt⟩
      | F =>
        exact ⟨PropFormulaNormalized.impl A B, List.Mem.head _, by
          simp only [evalExtN, hImplies, ha]⟩
    | negLeft Γ Δ A =>
      intro hAnt
      have hNegA := hAnt _ (List.Mem.head _)
      simp only [evalExtN] at hNegA
      have hAF : evalExtN v A = BoolVal.F := by
        cases ha : evalExtN v A <;> simp_all [hNeg]
      obtain ⟨C, hCm, hCt⟩ := hprem (fun X hX =>
        hAnt X (List.Mem.tail _ hX))
      match List.mem_cons.mp hCm with
      | Or.inl h => exact absurd (h ▸ hCt) (by simp [hAF])
      | Or.inr hCm' => exact ⟨C, hCm', hCt⟩
    | negRight Γ Δ A =>
      intro hAnt
      cases ha : evalExtN v A with
      | T =>
        obtain ⟨C, hCm, hCt⟩ := hprem (fun X hX =>
          match List.mem_cons.mp hX with
          | Or.inl h => h ▸ ha
          | Or.inr h => hAnt X h)
        exact ⟨C, List.Mem.tail _ hCm, hCt⟩
      | F =>
        exact ⟨PropFormulaNormalized.neg A, List.Mem.head _, by
          simp only [evalExtN, hNeg, ha]⟩


proof_of lkStep2_sound := by
  -- BEGIN PROOF
    cases rule with
    | andRight Γ Δ A B =>
      intro hAnt
      obtain ⟨C1, hC1m, hC1t⟩ := hp1 hAnt
      obtain ⟨C2, hC2m, hC2t⟩ := hp2 hAnt
      match List.mem_cons.mp hC1m with
      | Or.inl h1 =>
        match List.mem_cons.mp hC2m with
        | Or.inl h2 =>
          exact ⟨PropFormulaNormalized.conj A B, List.Mem.head _, by
            simp only [evalExtN, hAnd]
            rw [h1] at hC1t; rw [h2] at hC2t; rw [hC1t, hC2t]⟩
        | Or.inr h2 => exact ⟨C2, List.Mem.tail _ h2, hC2t⟩
      | Or.inr h1 => exact ⟨C1, List.Mem.tail _ h1, hC1t⟩
    | orLeft Γ Δ A B =>
      intro hAnt
      have hDisj := hAnt _ (List.Mem.head _)
      simp only [evalExtN, hOr] at hDisj
      cases ha : evalExtN v A with
      | T =>
        exact hp1 (fun X hX =>
          match List.mem_cons.mp hX with
          | Or.inl h => h ▸ ha
          | Or.inr h => hAnt X (List.Mem.tail _ h))
      | F =>
        cases hb : evalExtN v B with
        | T =>
          exact hp2 (fun X hX =>
            match List.mem_cons.mp hX with
            | Or.inl h => h ▸ hb
            | Or.inr h => hAnt X (List.Mem.tail _ h))
        | F => simp [ha, hb] at hDisj
    | implLeft Γ Δ Λ Θ A B =>
      intro hAnt
      have hImpl := hAnt _ (List.Mem.head _)
      simp only [evalExtN, hImplies] at hImpl
      -- Split antecedent context: (A→B) :: (Γ ++ Λ)
      have hΓ : ∀ X ∈ Γ, evalExtN v X = BoolVal.T := fun X hX =>
        hAnt X (List.Mem.tail _ (List.mem_append.mpr (Or.inl hX)))
      have hΛ : ∀ X ∈ Λ, evalExtN v X = BoolVal.T := fun X hX =>
        hAnt X (List.Mem.tail _ (List.mem_append.mpr (Or.inr hX)))
      cases ha : evalExtN v A with
      | F =>
        -- A is false, so from hp1: Γ → A :: Δ, either A or something in Δ is true
        obtain ⟨C, hCm, hCt⟩ := hp1 hΓ
        match List.mem_cons.mp hCm with
        | Or.inl h => exact absurd (h ▸ hCt) (by simp [ha])
        | Or.inr h => exact ⟨C, List.mem_append.mpr (Or.inl h), hCt⟩
      | T =>
        have hBT : evalExtN v B = BoolVal.T := by
          cases hb : evalExtN v B <;> simp_all
        -- B is true, use hp2: B :: Λ → Θ
        obtain ⟨C, hCm, hCt⟩ := hp2 (fun X hX =>
          match List.mem_cons.mp hX with
          | Or.inl h => h ▸ hBT
          | Or.inr h => hΛ X h)
        exact ⟨C, List.mem_append.mpr (Or.inr hCm), hCt⟩
    | cut Γ Δ Λ Θ A =>
      intro hAnt
      -- Split antecedent: Γ ++ Λ
      have hΓ : ∀ X ∈ Γ, evalExtN v X = BoolVal.T := fun X hX =>
        hAnt X (List.mem_append.mpr (Or.inl hX))
      have hΛ : ∀ X ∈ Λ, evalExtN v X = BoolVal.T := fun X hX =>
        hAnt X (List.mem_append.mpr (Or.inr hX))
      cases ha : evalExtN v A with
      | T =>
        -- A is true, use hp2: A :: Λ → Θ
        obtain ⟨C, hCm, hCt⟩ := hp2 (fun X hX =>
          match List.mem_cons.mp hX with
          | Or.inl h => h ▸ ha
          | Or.inr h => hΛ X h)
        exact ⟨C, List.mem_append.mpr (Or.inr hCm), hCt⟩
      | F =>
        -- A is false, use hp1: Γ → A :: Δ
        obtain ⟨C, hCm, hCt⟩ := hp1 hΓ
        match List.mem_cons.mp hCm with
        | Or.inl h => exact absurd (h ▸ hCt) (by simp [ha])
        | Or.inr h => exact ⟨C, List.mem_append.mpr (Or.inl h), hCt⟩


proof_of lkProofTree_valid := @fun
  | _, .axiom_ A => lkAxiom_valid A
  | _, .onePremise rule t => fun v => lkStep1_sound rule v (lkProofTree_valid t v)
  | _, .twoPremise rule t1 t2 =>
    fun v => lkStep2_sound rule v (lkProofTree_valid t1 v) (lkProofTree_valid t2 v)


proof_of soundness_LK := by
  -- BEGIN PROOF
    obtain ⟨t⟩ := h
    exact lkProofTree_valid t


proof_of lemma_3_6_1 := ⟨fun s hs => by
  -- BEGIN PROOF
       obtain ⟨A, hant, hsucc⟩ := hs
       cases s; simp at hant hsucc; subst hant; subst hsucc
       exact lkAxiom_valid A,
     fun rule v hp => lkStep1_sound rule v hp,
     fun rule v hp1 hp2 => lkStep2_sound rule v hp1 hp2,
     soundness_LK⟩


proof_of deductionTree_isProof_of_leaves := @fun
  | _, .leaf s, h => h s (by simp [DeductionTree.leaves])
  | _, .onePremise _ t, h => deductionTree_isProof_of_leaves t h
  | _, .twoPremise _ t₁ t₂, h =>
    ⟨deductionTree_isProof_of_leaves t₁ (fun s hs =>
      h s (List.mem_append.mpr (Or.inl hs))),
     deductionTree_isProof_of_leaves t₂ (fun s hs =>
      h s (List.mem_append.mpr (Or.inr hs)))⟩


proof_of isCutFree_of_eq := by subst h; exact hcf
  -- BEGIN PROOF


proof_of gprimeProof_to_cutFreeLKProof_isCutFree := (gProofToLKCutFree t).property
  -- BEGIN PROOF


proof_of lk_gprime_equivalence := by
  -- BEGIN PROOF
    constructor
    · intro ⟨t⟩
      exact ⟨lkProof_to_gprimeProof t⟩
    · intro ⟨t⟩
      exact ⟨gprimeProof_to_cutFreeLKProof t,
             gprimeProof_to_cutFreeLKProof_isCutFree t⟩

proof_of valid_to_lkProvable := ⟨(validSequent_to_cutFreeLKProof s hv).val⟩


proof_of lkSetProvable_contradiction := by
  obtain ⟨L₁, hL₁, ⟨t₁⟩⟩ := hA
  obtain ⟨L₂, hL₂, ⟨t₂⟩⟩ := hnA
  intro B
  refine ⟨L₂ ++ L₁, ?_, ?_⟩
  · intro C hc
    exact (List.mem_append.mp hc).elim (hL₂ C) (hL₁ C)
  · let neg := LKProofTree.onePremise (LKStep1.negLeft L₁ [] A) t₁
    let contradiction := LKProofTree.twoPremise (LKStep2.cut L₂ [] L₁ [] (.neg A)) t₂ neg
    exact ⟨LKProofTree.onePremise (LKStep1.weakenRight (L₂ ++ L₁) [] B) contradiction⟩


proof_of lkSetProvable_mono := by
  rintro ⟨L, hL, hp⟩
  exact ⟨L, fun B hb => hsub B (hL B hb), hp⟩


proof_of lkSetProvable_remove_neg := by
  obtain ⟨L, hL, hp⟩ := h
  let L' := L.filter (fun B => B != .neg A)
  refine ⟨L', ?_, valid_to_lkProvable _ ?_⟩
  · intro B hb
    have hm := List.mem_filter.mp hb
    rcases hL B hm.1 with hΓ | heq
    · exact hΓ
    · have hne : B ≠ .neg A := by simpa using hm.2
      exact False.elim (hne heq)
  · intro v hv
    refine ⟨A, List.Mem.head _, ?_⟩
    cases ha : evalExtN v A with
    | T => rfl
    | F =>
      have hn : evalExtN v (.neg A) = BoolVal.T := by simp [evalExtN, hNeg, ha]
      have hAll : ∀ B ∈ L, evalExtN v B = BoolVal.T := by
        intro B hb
        by_cases heq : B = .neg A
        · exact heq ▸ hn
        · exact hv B (List.mem_filter.mpr ⟨hb, by simpa using heq⟩)
      obtain ⟨B, hb, ht⟩ := soundness_LK _ hp v hAll
      have : evalExtN v A = BoolVal.T := List.mem_singleton.mp hb ▸ ht
      simp [ha] at this


proof_of consistency_characterization_LK := by
  constructor
  · exact ⟨fun h => ⟨.var 0, h _, h _⟩,
      fun ⟨_, hA, hnA⟩ => lkSetProvable_contradiction hA hnA⟩
  · intro A
    constructor
    · intro hnp hi
      exact hnp (lkSetProvable_remove_neg (hi A))
    · intro hc hp
      apply hc
      have hA : lkSetProvable (Γ ∪ Set.singleton (.neg A)) A :=
        lkSetProvable_mono (fun _ h => Or.inl h) hp
      have hnA : lkSetProvable (Γ ∪ Set.singleton (.neg A)) (.neg A) :=
        ⟨[.neg A], fun B hb => Or.inr (List.mem_singleton.mp hb),
          ⟨LKProofTree.axiom_ (.neg A)⟩⟩
      exact lkSetProvable_contradiction hA hnA


end LCS.Propositional.LK
