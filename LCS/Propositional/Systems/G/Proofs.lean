import LCS.Propositional.Systems.G

namespace LCS.Propositional.Systems.G

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

proof_of exFalsificationSearchLeavesClosed := by
  intro s hs
  simp [exFalsificationSearchTree, InformalImplicationTree.leaves] at hs
  rcases hs with rfl | rfl
  · rintro ⟨v, _, hf⟩
    have hp := hf (.var 0) (by simp)
    have hnp := hf (.neg (.var 0)) (by simp)
    simp [evalExtN] at hp
    simp [evalExtN, hp, hNeg] at hnp
  · rintro ⟨v, ht, _⟩
    have hq := ht (.var 1) (by simp)
    have hnq := ht (.neg (.var 1)) (by simp)
    simp [evalExtN] at hq
    simp [evalExtN, hq, hNeg] at hnq


proof_of exImplLeftPrincipal := List.Mem.tail _ (List.Mem.head _)


proof_of exImplLeftSideFormulae := ⟨List.Mem.head _, List.Mem.head _⟩


proof_of exImplLeftExtraFormulae := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨List.Mem.head _,
           List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           List.Mem.head _⟩
  · exact ⟨List.Mem.head _,
           List.Mem.tail _ (List.Mem.head _),
           List.Mem.tail _ (List.Mem.head _)⟩
  · exact ⟨List.Mem.tail _ (List.Mem.head _),
           List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
           List.Mem.head _⟩

helper theorem mem_mid {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    x ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

helper theorem mem_mid_cases {x y : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    (h : y ∈ Γ ++ [x] ++ Δ) : y ∈ Γ ∨ y = x ∨ y ∈ Δ := by
-- BEGIN PROOF
  rcases List.mem_append.mp h with h1 | h2
  · rcases List.mem_append.mp h1 with hΓ | hx
    · exact Or.inl hΓ
    · simp at hx; exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr h2)

helper theorem mem_mid_of_left {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Γ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

helper theorem mem_mid_of_right {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Δ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

helper theorem mem_two_cases {A B y : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    (h : y ∈ Γ ++ [A, B] ++ Δ) : y ∈ Γ ∨ y = A ∨ y = B ∨ y ∈ Δ := by
-- BEGIN PROOF
  rcases List.mem_append.mp h with h1 | h2
  · rcases List.mem_append.mp h1 with hΓ | hAB
    · exact Or.inl hΓ
    · rcases List.mem_cons.mp hAB with rfl | hB
      · exact Or.inr (Or.inl rfl)
      · simp at hB; exact Or.inr (Or.inr (Or.inl hB))
  · exact Or.inr (Or.inr (Or.inr h2))

proof_of axiom_valid := by
  -- BEGIN PROOF
    intro v hAnt
    obtain ⟨A, hAntA, hSuccA⟩ := h
    exact ⟨A, hSuccA, hAnt A hAntA⟩


helper theorem step1_valid {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (hprem : sequentValid prem) :
    sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | andLeft Γ Δ Λ A B =>
    intro v hAnt
    have hConj := hAnt _ (mem_mid (Γ := Γ) (Δ := Δ))
    simp only [evalExtN, hAnd] at hConj
    have hA : evalExtN v A = BoolVal.T := by
      cases ha : evalExtN v A <;> simp_all
    have hB : evalExtN v B = BoolVal.T := by
      cases hb : evalExtN v B <;> simp_all
    apply hprem v; intro X hX
    rcases mem_two_cases hX with hΓ | hXA | hXB | hΔ
    · exact hAnt X (mem_mid_of_left hΓ)
    · rw [hXA]; exact hA
    · rw [hXB]; exact hB
    · exact hAnt X (mem_mid_of_right hΔ)
  | orRight Γ Δ Λ A B =>
    intro v hAnt
    obtain ⟨X, hXmem, hXtrue⟩ := hprem v hAnt
    rcases mem_two_cases hXmem with hΔ | hXA | hXB | hΛ
    · exact ⟨X, mem_mid_of_left hΔ, hXtrue⟩
    · exact ⟨.disj A B, mem_mid (Γ := Δ) (Δ := Λ), by
        simp only [evalExtN, hOr]; rw [hXA] at hXtrue; rw [hXtrue]⟩
    · exact ⟨.disj A B, mem_mid (Γ := Δ) (Δ := Λ), by
        simp only [evalExtN, hOr]; rw [hXB] at hXtrue; rw [hXtrue]
        cases evalExtN v A <;> rfl⟩
    · exact ⟨X, mem_mid_of_right hΛ, hXtrue⟩
  | implRight Γ Δ Λ A B =>
    intro v hAnt
    cases ha : evalExtN v A with
    | T =>
      obtain ⟨X, hXmem, hXtrue⟩ := hprem v (fun X hX =>
        match List.mem_cons.mp hX with
        | Or.inl h => h ▸ ha
        | Or.inr h => hAnt X h)
      rcases List.mem_cons.mp hXmem with hXB | hCtx
      · exact ⟨.impl A B, mem_mid (Γ := Δ) (Δ := Λ), by
          simp only [evalExtN, hImplies, ha]; rw [hXB] at hXtrue; rw [hXtrue]⟩
      · rcases List.mem_append.mp hCtx with hΔ | hΛ
        · exact ⟨X, mem_mid_of_left hΔ, hXtrue⟩
        · exact ⟨X, mem_mid_of_right hΛ, hXtrue⟩
    | F =>
      exact ⟨.impl A B, mem_mid (Γ := Δ) (Δ := Λ), by
        simp only [evalExtN, hImplies, ha]⟩
  | negLeft Γ Δ Λ A =>
    intro v hAnt
    have hNegA := hAnt _ (mem_mid (Γ := Γ) (Δ := Δ))
    simp only [evalExtN, hNeg] at hNegA
    have hAF : evalExtN v A = BoolVal.F := by
      cases ha : evalExtN v A <;> simp_all
    have hCtx : ∀ X ∈ Γ ++ Δ, evalExtN v X = BoolVal.T := fun X hX =>
      match List.mem_append.mp hX with
      | Or.inl hΓ => hAnt X (mem_mid_of_left hΓ)
      | Or.inr hΔ => hAnt X (mem_mid_of_right hΔ)
    obtain ⟨X, hXmem, hXtrue⟩ := hprem v hCtx
    match List.mem_cons.mp hXmem with
    | Or.inl h => exact absurd (h ▸ hXtrue) (by simp [hAF])
    | Or.inr h => exact ⟨X, h, hXtrue⟩
  | negRight Γ Δ Λ A =>
    intro v hAnt
    cases ha : evalExtN v A with
    | T =>
      obtain ⟨X, hXmem, hXtrue⟩ := hprem v (fun X hX =>
        match List.mem_cons.mp hX with
        | Or.inl h => h ▸ ha
        | Or.inr h => hAnt X h)
      rcases List.mem_append.mp hXmem with hΔ | hΛ
      · exact ⟨X, mem_mid_of_left hΔ, hXtrue⟩
      · exact ⟨X, mem_mid_of_right hΛ, hXtrue⟩
    | F =>
      exact ⟨.neg A, mem_mid (Γ := Δ) (Δ := Λ), by
        simp only [evalExtN, hNeg, ha]⟩

helper theorem step2_valid {prem1 prem2 conc : Sequent}
    (rule : GentzenStep2 prem1 prem2 conc)
    (hp1 : sequentValid prem1) (hp2 : sequentValid prem2) :
    sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | andRight Γ Δ Λ A B =>
    intro v hAnt
    obtain ⟨X1, hX1mem, hX1true⟩ := hp1 v hAnt
    obtain ⟨X2, hX2mem, hX2true⟩ := hp2 v hAnt
    rcases mem_mid_cases hX1mem with hX1Δ | hX1eq | hX1Λ
    · exact ⟨X1, mem_mid_of_left hX1Δ, hX1true⟩
    · -- X1 = A
      rcases mem_mid_cases hX2mem with hX2Δ | hX2eq | hX2Λ
      · exact ⟨X2, mem_mid_of_left hX2Δ, hX2true⟩
      · -- X2 = B, both true
        exact ⟨.conj A B, mem_mid (Γ := Δ) (Δ := Λ), by
          simp only [evalExtN, hAnd]
          rw [hX1eq] at hX1true; rw [hX2eq] at hX2true
          rw [hX1true, hX2true]⟩
      · exact ⟨X2, mem_mid_of_right hX2Λ, hX2true⟩
    · exact ⟨X1, mem_mid_of_right hX1Λ, hX1true⟩
  | orLeft Γ Δ Λ A B =>
    intro v hAnt
    have hDisj := hAnt _ (mem_mid (Γ := Γ) (Δ := Δ))
    simp only [evalExtN, hOr] at hDisj
    have hCtx : ∀ (F : PropFormulaNormalized), evalExtN v F = BoolVal.T →
        ∀ X ∈ Γ ++ [F] ++ Δ, evalExtN v X = BoolVal.T := fun F hF X hX =>
      match mem_mid_cases hX with
      | Or.inl hΓ => hAnt X (mem_mid_of_left hΓ)
      | Or.inr (Or.inl h) => h ▸ hF
      | Or.inr (Or.inr hΔ) => hAnt X (mem_mid_of_right hΔ)
    cases ha : evalExtN v A with
    | T => exact hp1 v (hCtx A ha)
    | F =>
      cases hb : evalExtN v B with
      | T => exact hp2 v (hCtx B hb)
      | F => simp [ha, hb] at hDisj
  | implLeft Γ Δ Λ A B =>
    intro v hAnt
    have hImpl := hAnt _ (mem_mid (Γ := Γ) (Δ := Δ))
    simp only [evalExtN, hImplies] at hImpl
    have hCtx : ∀ X ∈ Γ ++ Δ, evalExtN v X = BoolVal.T := fun X hX =>
      match List.mem_append.mp hX with
      | Or.inl hΓ => hAnt X (mem_mid_of_left hΓ)
      | Or.inr hΔ => hAnt X (mem_mid_of_right hΔ)
    cases ha : evalExtN v A with
    | T =>
      have hBT : evalExtN v B = BoolVal.T := by
        cases hb : evalExtN v B <;> simp_all
      exact hp2 v (fun X hX =>
        match List.mem_cons.mp hX with
        | Or.inl h => h ▸ hBT
        | Or.inr h => hCtx X h)
    | F =>
      obtain ⟨X, hXmem, hXtrue⟩ := hp1 v hCtx
      match List.mem_cons.mp hXmem with
      | Or.inl h => exact absurd (h ▸ hXtrue) (by simp [ha])
      | Or.inr h => exact ⟨X, h, hXtrue⟩

helper theorem proofTree_valid : {s : Sequent} → ProofTree s → sequentValid s
  | _, .axiom_ s h => axiom_valid s h
  | _, .onePremise rule t => step1_valid rule (proofTree_valid t)
  | _, .twoPremise rule t1 t2 =>
    step2_valid rule (proofTree_valid t1) (proofTree_valid t2)

proof_of soundness_G := by
  -- BEGIN PROOF
    obtain ⟨t⟩ := h
    exact proofTree_valid t


end LCS.Propositional.Systems.G
