import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation

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

-- ===================================================================
-- Lemma 6.3.2 (helper): direct G= implLeft permutation
-- ===================================================================
theorem geqImplLeft_markedSplit
    (L : Language)
    : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y → (∃ (K : List
      (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++ [Y] ++ K ∧ S
      = K ++ [X] ++ Q := by
  intro P Q R S X Y heq hne
  have h' : P ++ (X :: Q) = R ++ (Y :: S) := by
    simpa [List.append_assoc] using heq
  rcases List.append_eq_append_iff.mp h' with
    ⟨K, hR, htail⟩ | ⟨K, hP, htail⟩
  · cases K with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at htail
      exact (hne htail.1).elim
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hXZ, hQ⟩
      subst Z
      exact Or.inl ⟨K, by simpa [List.append_assoc] using hR, by simpa [List.append_assoc] using hQ⟩
  · cases K with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at htail
      exact (hne htail.1.symm).elim
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hYZ, hS⟩
      subst Z
      exact Or.inr ⟨K, by simpa [List.append_assoc] using hP, by simpa [List.append_assoc] using hS⟩

theorem geqImplLeft_markedSplit3
    (L : Language)
    : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → (∃ (K : List
      (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧ X = Y ∧ Q = S ∨ ∃ (K : List (FormulaN
      L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q := by
  intro P Q R S X Y heq
  have h' : P ++ (X :: Q) = R ++ (Y :: S) := by
    simpa [List.append_assoc] using heq
  rcases List.append_eq_append_iff.mp h' with
    ⟨K, hR, htail⟩ | ⟨K, hP, htail⟩
  · cases K with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hR htail
      exact Or.inr (Or.inl ⟨hR.symm, htail.1, htail.2⟩)
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hXZ, hQ⟩
      subst Z
      exact Or.inl ⟨K, by simpa [List.append_assoc] using hR, by simpa [List.append_assoc] using hQ⟩
  · cases K with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hP htail
      exact Or.inr (Or.inl ⟨hP, htail.1.symm, htail.2.symm⟩)
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hYZ, hS⟩
      subst Z
      exact Or.inr (Or.inr ⟨K, by simpa [List.append_assoc] using hP, by simpa [List.append_assoc] using hS⟩)

theorem geqImplLeft_geqDepth_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

theorem geqImplLeft_geqLeaf_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) =
      geqLeafSequents p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

theorem geqImplLeft_implFresh1
    (L : Language)
    : ∀ (y : Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++
      Δ ++ Λ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ ++ Δ ++ (Λ ++ [A]) → ¬y ∈ formulaFVN F := by
  intro y A B Γ Δ Λ hfresh F hF
  have hcases : (F ∈ Γ ∨ F ∈ Δ) ∨ F ∈ Λ ∨ F = A := by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hF
  rcases hcases with (hF | hF) | hF | hFA
  · exact hfresh F (by simp [hF])
  · exact hfresh F (by simp [hF])
  · exact hfresh F (by simp [hF])
  · subst F
    have htarget := hfresh (FormulaN.impl A B) (by simp)
    intro hy
    exact htarget (Or.inl hy)

theorem geqImplLeft_implFresh2
    (L : Language)
    : ∀ (y : Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++
      Δ ++ Λ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ [B] ++ Γ ++ Δ ++ Λ → ¬y ∈ formulaFVN F := by
  intro y A B Γ Δ Λ hfresh F hF
  have hcases : ((F = B ∨ F ∈ Γ) ∨ F ∈ Δ) ∨ F ∈ Λ := by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hF
  rcases hcases with ((hFB | hF) | hF) | hF
  · subst F
    have htarget := hfresh (FormulaN.impl A B) (by simp)
    intro hy
    exact htarget (Or.inr hy)
  · exact hfresh F (by simp [hF])
  · exact hfresh F (by simp [hF])
  · exact hfresh F (by simp [hF])

theorem geqImplLeft_base
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk
      ([B] ++ Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s'
      ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (permTwo : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1
      prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth
      sub2 < n → conc = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 :
      GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max
      (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (g : GProofTreeExt s) (hdepth : geqDepth (GEqProofTree.base (hL := hL) g) = n) (hleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents (GEqProofTree.base (hL := hL) g) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.base (hL := hL) g) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  cases g with
  | axiom_ s hAx =>
    have hall := hleaf s (by
      simp [geqLeafSequents, gProofTreeLeafSequents])
    have hbad : isAtomicOrQuantified (FormulaN.impl A B) := by
      exact hall.1 (FormulaN.impl A B) (by
        rw [hseq]
        simp)
    simpa [isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] using hbad
  | onePremise rule sub =>
    exact permOne rule (.base sub) (by
      simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
      omega) hseq (by
        intro s' hs'
        exact hleaf s' (by
          simpa [geqLeafSequents, gProofTreeLeafSequents] using hs'))
  | twoPremise rule sub1 sub2 =>
    exact permTwo rule (.base sub1) (.base sub2) (by
      simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
      omega) (by
      simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
      omega) hseq (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
          exact Or.inl hs')) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
          exact Or.inr hs'))

theorem geqImplLeft_axiom_
    (L : Language) (hL : L.hasEquality = true) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
      (hseq : s = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (hAx : isAxiom s) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.axiom_ (hL := hL) s hAx) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.axiom_ (hL := hL) s hAx) ∧ (∀
      (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  have hall := hleaf s (by simp [geqLeafSequents])
  have hbad : isAtomicOrQuantified (FormulaN.impl A B) := by
    exact hall.1 (FormulaN.impl A B) (by
      rw [hseq]
      simp)
  simpa [isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] using hbad

theorem geqImplLeft_onePremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk
      ([B] ++ Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s'
      ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (prem : Sequent L) (sub : GEqProofTree hL prem) (rule : GentzenStep1Ext
      prem s) (hdepth : geqDepth (GEqProofTree.onePremise rule sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.onePremise rule sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.onePremise rule sub) ∧ (∀ (s'
      : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  exact permOne rule sub (by
    simp only [geqDepth] at hdepth
    omega) hseq (by
      simpa [geqLeafSequents] using hleaf)

theorem geqImplLeft_twoPremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (permTwo : ∀ {prem1 prem2 conc :
      Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree
      hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++
      [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) =
      1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (prem1 prem2 : Sequent L) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2) (rule :
      GentzenStep2Ext prem1 prem2 s) (hdepth : geqDepth (GEqProofTree.twoPremise rule sub1 sub2) = n) (hleaf :
      ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.twoPremise rule sub1 sub2) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.twoPremise rule sub1 sub2) ∧
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  exact permTwo rule sub1 sub2 (by
    simp only [geqDepth] at hdepth
    omega) (by
    simp only [geqDepth] at hdepth
    omega) hseq (by
      intro s' hs'
      exact hleaf s' (by
        simp only [geqLeafSequents, List.mem_append]
        exact Or.inl hs')) (by
      intro s' hs'
      exact hleaf s' (by
        simp only [geqLeafSequents, List.mem_append]
        exact Or.inr hs'))

section
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++
      Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')
include ih

theorem geqImplLeft_conjLeft
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ
      Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [X, Y] ++
      Δr) (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.conj Y] ++ Δr) (Λr)) = (Sequent.mk (Γ ++
      [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Λ
  rcases markedSplit hant (by simp) with
    ⟨K, hΓ, hΔr⟩ | ⟨K, hΓr, hΔ⟩
  · subst Γ
    subst Δr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++ [X, Y] ++ K) Δ Λr
        (by simp [List.append_assoc]) hsubleaf
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 (Γr ++ [X, Y] ++ (K ++ Δ)) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γr) ++ [X, Y] ++ (K ++ Δ)) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.conjLeft Γr (K ++ Δ) (Λr ++ [A]) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.conjLeft ([B] ++ Γr) (K ++ Δ) Λr X Y) q2'
    have hout1 : Sequent.mk (Γr ++ [FormulaN.conj X Y] ++ (K ++ Δ)) (Λr ++ [A]) = Sequent.mk
            ((Γr ++ [FormulaN.conj X Y] ++ K) ++ Δ)
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γr) ++ [FormulaN.conj X Y] ++ (K ++ Δ)) Λr = Sequent.mk
            ([B] ++ (Γr ++ [FormulaN.conj X Y] ++ K) ++ Δ)
            Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      exact hq1'leaf s' (by
        simpa [r1, geqLeafSequents] using hs')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      exact hq2'leaf s' (by
        simpa [r2, geqLeafSequents] using hs')
  · subst Γr
    subst Δ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γ (K ++ [X, Y] ++ Δr) Λr
        (by simp [List.append_assoc]) hsubleaf
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ((Γ ++ K) ++ [X, Y] ++ Δr) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γ ++ K) ++ [X, Y] ++ Δr) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.conjLeft (Γ ++ K) Δr (Λr ++ [A]) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.conjLeft ([B] ++ Γ ++ K) Δr Λr X Y) q2'
    have hout1 : Sequent.mk ((Γ ++ K) ++ [FormulaN.conj X Y] ++ Δr) (Λr ++ [A]) = Sequent.mk
            (Γ ++ (K ++ [FormulaN.conj X Y] ++ Δr))
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.conj X Y] ++ Δr) Λr = Sequent.mk ([B] ++ Γ ++
              (K ++ [FormulaN.conj X Y] ++ Δr)) Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      exact hq1'leaf s' (by
        simpa [r1, geqLeafSequents] using hs')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      exact hq2'leaf s' (by
        simpa [r2, geqLeafSequents] using hs')

theorem geqImplLeft_disjRight
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L))
      (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X, Y] ++ Λr))) (hsubdepth : geqDepth
      sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc
      : (Sequent.mk (Γr) (Δr ++ [X.disj Y] ++ Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γr
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γ Δ
      (Δr ++ [X, Y] ++ Λr) rfl hsubleaf
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 (Γ ++ Δ) (Δr ++ [X, Y] ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) hq1leaf
  let r1 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight (Γ ++ Δ) Δr (Λr ++ [A]) X Y) q1'
  have hout1 : Sequent.mk (Γ ++ Δ) (Δr ++ [FormulaN.disj X Y] ++ (Λr ++ [A])) = Sequent.mk (Γ ++ Δ)
          ((Δr ++ [FormulaN.disj X Y] ++ Λr) ++ [A]) := by
    simp [List.append_assoc]
  let p1 := hout1 ▸ r1
  let p2 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight ([B] ++ Γ ++ Δ) Δr Λr X Y) q2
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    rw [geqDepth_transport hout1 r1]
    simp only [r1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := rfl
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    rw [geqLeaf_transport hout1 r1] at hs'
    exact hq1'leaf s' (by
      simpa [r1, geqLeafSequents] using hs')
  · simpa [p2, geqLeafSequents] using hq2leaf

theorem geqImplLeft_implRight
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L))
      (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) ([Y] ++ Δr ++ Λr))) (hsubdepth :
      geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr) (Δr ++ [X.impl Y] ++ Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γr
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      ([X] ++ Γ) Δ ([Y] ++ Δr ++ Λr)
      (by simp [List.append_assoc]) hsubleaf
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ([X] ++ (Γ ++ Δ)) ([Y] ++ Δr ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) hq1leaf
  have hswapBX : ([B] ++ ([X] ++ Γ) ++ Δ).Perm ([X] ++ ([B] ++ Γ ++ Δ)) := by
    simpa [List.append_assoc] using (List.Perm.append_right (Γ ++ Δ) (List.Perm.swap X B []))
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 ([X] ++ ([B] ++ Γ ++ Δ)) ([Y] ++ Δr ++ Λr) hswapBX
      (List.Perm.refl _) hq2leaf
  let r1 := GEqProofTree.onePremise (GentzenStep1Ext.implRight (Γ ++ Δ) Δr (Λr ++ [A]) X Y) q1'
  let r2 := GEqProofTree.onePremise (GentzenStep1Ext.implRight ([B] ++ Γ ++ Δ) Δr Λr X Y) q2'
  have hout1 : Sequent.mk (Γ ++ Δ) (Δr ++ [FormulaN.impl X Y] ++ (Λr ++ [A])) = Sequent.mk (Γ ++ Δ)
          ((Δr ++ [FormulaN.impl X Y] ++ Λr) ++ [A]) := by
    simp [List.append_assoc]
  let p1 := hout1 ▸ r1
  let p2 := r2
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    rw [geqDepth_transport hout1 r1]
    simp only [r1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, r2, geqDepth]
    omega
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    rw [geqLeaf_transport hout1 r1] at hs'
    exact hq1'leaf s' (by
      simpa [r1, geqLeafSequents] using hs')
  · simpa [p2, r2, geqLeafSequents] using hq2'leaf

theorem geqImplLeft_negLeft
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ
      Δ Λ Γr Δr Λr : List (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X] ++
      Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.neg] ++ Δr) (Λr)) = (Sequent.mk (Γ ++
      [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Λ
  rcases markedSplit hant (by simp) with
    ⟨K, hΓ, hΔr⟩ | ⟨K, hΓr, hΔ⟩
  · subst Γ
    subst Δr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++ K) Δ ([X] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hswapXA : (([X] ++ Λr) ++ [A]).Perm ([X] ++ (Λr ++ [A])) := by
      simp [List.append_assoc]
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 (Γr ++ (K ++ Δ)) ([X] ++ (Λr ++ [A]))
        (by simp [List.append_assoc]) hswapXA hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γr) ++ (K ++ Δ)) ([X] ++ Λr)
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negLeft Γr (K ++ Δ) (Λr ++ [A]) X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negLeft ([B] ++ Γr) (K ++ Δ) Λr X) q2'
    have hout1 : Sequent.mk (Γr ++ [FormulaN.neg X] ++ (K ++ Δ)) (Λr ++ [A]) = Sequent.mk
            ((Γr ++ [FormulaN.neg X] ++ K) ++ Δ)
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γr) ++ [FormulaN.neg X] ++ (K ++ Δ)) Λr = Sequent.mk
            ([B] ++ (Γr ++ [FormulaN.neg X] ++ K) ++ Δ)
            Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      exact hq1'leaf s' (by
        simpa [r1, geqLeafSequents] using hs')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      exact hq2'leaf s' (by
        simpa [r2, geqLeafSequents] using hs')
  · subst Γr
    subst Δ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γ (K ++ Δr) ([X] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hswapXA : (([X] ++ Λr) ++ [A]).Perm ([X] ++ (Λr ++ [A])) := by
      simp [List.append_assoc]
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ((Γ ++ K) ++ Δr) ([X] ++ (Λr ++ [A]))
        (by simp [List.append_assoc]) hswapXA hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γ ++ K) ++ Δr) ([X] ++ Λr)
        (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negLeft (Γ ++ K) Δr (Λr ++ [A]) X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negLeft ([B] ++ Γ ++ K) Δr Λr X) q2'
    have hout1 : Sequent.mk ((Γ ++ K) ++ [FormulaN.neg X] ++ Δr) (Λr ++ [A]) = Sequent.mk
            (Γ ++ (K ++ [FormulaN.neg X] ++ Δr))
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.neg X] ++ Δr) Λr = Sequent.mk ([B] ++ Γ ++
              (K ++ [FormulaN.neg X] ++ Δr)) Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      exact hq1'leaf s' (by
        simpa [r1, geqLeafSequents] using hs')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      exact hq2'leaf s' (by
        simpa [r2, geqLeafSequents] using hs')

theorem geqImplLeft_negRight
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L))
      (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) (Δr ++ Λr))) (hsubdepth : geqDepth sub <
      n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc :
      (Sequent.mk (Γr) (Δr ++ [X.neg] ++ Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γr
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B ([X] ++ Γ) Δ (Δr ++ Λr)
      (by simp [List.append_assoc]) hsubleaf
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ([X] ++ (Γ ++ Δ)) (Δr ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) hq1leaf
  have hswapBX : ([B] ++ ([X] ++ Γ) ++ Δ).Perm ([X] ++ ([B] ++ Γ ++ Δ)) := by
    simpa [List.append_assoc] using (List.Perm.append_right (Γ ++ Δ) (List.Perm.swap X B []))
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 ([X] ++ ([B] ++ Γ ++ Δ)) (Δr ++ Λr) hswapBX
      (List.Perm.refl _) hq2leaf
  let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negRight (Γ ++ Δ) Δr (Λr ++ [A]) X) q1'
  let p2 := GEqProofTree.onePremise (GentzenStep1Ext.negRight ([B] ++ Γ ++ Δ) Δr Λr X) q2'
  have hout1 : Sequent.mk (Γ ++ Δ) (Δr ++ [FormulaN.neg X] ++ (Λr ++ [A])) = Sequent.mk (Γ ++ Δ)
          ((Δr ++ [FormulaN.neg X] ++ Λr) ++ [A]) := by
    simp [List.append_assoc]
  let p1 := hout1 ▸ r1
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    rw [geqDepth_transport hout1 r1]
    simp only [r1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, geqDepth]
    omega
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    rw [geqLeaf_transport hout1 r1] at hs'
    exact hq1'leaf s' (by
      simpa [r1, geqLeafSequents] using hs')
  · simpa [p2, geqLeafSequents] using hq2'leaf

end
end LCS.CutElim.LKe.Equivalence
end
