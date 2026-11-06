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
-- Lemma 6.3.2 (helper): direct G= conjRight permutation
-- ===================================================================
-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_markedSplit
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

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_markedSplit3
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

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_replaceConjFresh
    (L : Language)
    : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X : FormulaN L), formulaFVN X ⊆ formulaFVN C → (∀ (F :
      FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ ant ++ (D ++ [X]
      ++ S) → ¬y ∈ formulaFVN F := by
  intro y ant D S C X hsubset hfresh F hmem
  have hmem' : F ∈ ant ∨ (F ∈ D ∨ F = X) ∨ F ∈ S := by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hmem
  rcases hmem' with hF | (hF | hF) | hF
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl hF)
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl (Or.inl hF)))
  · subst F
    intro hy
    exact hfresh C (by simp) (hsubset y hy)
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr hF))

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqDepth_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqLeaf_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) =
      geqLeafSequents p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqLeafProperty_transport
    (L : Language) (hL : L.hasEquality = true) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s' := by
  intro s₁ s₂ heq p hp
  rw [geqLeaf_transport heq p]
  exact hp

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_base
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ)
      (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (permTwo : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1
      prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth
      sub2 < n → conc = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 :
      GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max
      (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (g : GProofTreeExt s) (hdepth : geqDepth (GEqProofTree.base (hL := hL) g) = n) (hleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents (GEqProofTree.base (hL := hL) g) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.base (hL := hL) g) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  cases g with
  | axiom_ s hAx =>
    have hall := hleaf s (by
      simp [geqLeafSequents, gProofTreeLeafSequents])
    have hbad : isAtomicOrQuantified (FormulaN.conj A B) := by
      exact hall.2 (FormulaN.conj A B) (by
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

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_axiom_
    (L : Language) (hL : L.hasEquality = true) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
      (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (hAx : isAxiom s) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.axiom_ (hL := hL) s hAx) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.axiom_ (hL := hL) s hAx) ∧ (∀
      (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  have hall := hleaf s (by simp [geqLeafSequents])
  have hbad : isAtomicOrQuantified (FormulaN.conj A B) := by
    exact hall.2 (FormulaN.conj A B) (by
      rw [hseq]
      simp)
  simpa [isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] using hbad

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_onePremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ)
      (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (prem : Sequent L) (sub : GEqProofTree hL prem) (rule : GentzenStep1Ext
      prem s) (hdepth : geqDepth (GEqProofTree.onePremise rule sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.onePremise rule sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.onePremise rule sub) ∧ (∀ (s'
      : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  exact permOne rule sub (by
    simp only [geqDepth] at hdepth
    omega) hseq (by
      simpa [geqLeafSequents] using hleaf)

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_twoPremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permTwo : ∀ {prem1 prem2 conc :
      Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree
      hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A]
      ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2)
      = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (prem1 prem2 : Sequent L) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2) (rule :
      GentzenStep2Ext prem1 prem2 s) (hdepth : geqDepth (GEqProofTree.twoPremise rule sub1 sub2) = n) (hleaf :
      ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.twoPremise rule sub1 sub2) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.twoPremise rule sub1 sub2) ∧
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
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ
      ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_conjLeft
    (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL
      (Sequent.mk (Γr ++ [X, Y] ++ Δr) (succ))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.conj Y] ++ Δr)
      (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γr ++ [X, Y] ++ Δr) Δ Λ rfl hsubleaf
  refine ⟨.onePremise (.conjLeft Γr Δr (Δ ++ [A] ++ Λ) X Y) q1, .onePremise
      (.conjLeft Γr Δr (Δ ++ [B] ++ Λ) X Y) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_disjRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X, Y] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf
      : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr)
      (Δr ++ [X.disj Y] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++ [X, Y] ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ [X, Y] ++ K) ++ [A] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X, Y] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ [X, Y] ++ K) ++ [B] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X, Y] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr Δr (K ++ [A] ++ Λ) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr Δr (K ++ [B] ++ Λ) X Y) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.disj X Y] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.disj X Y] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.disj X Y] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.disj X Y] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++ [X, Y] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [X, Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [A] ++ K) ++ [X, Y] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [X, Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [B] ++ K) ++ [X, Y] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr (Δ ++ [A] ++ K) Λr X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr (Δ ++ [B] ++ K) Λr X Y) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.disj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.disj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.disj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.disj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_implRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) ([Y] ++ Δr ++ Λr))) (hsubdepth : geqDepth sub < n)
      (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc :
      (Sequent.mk (Γr) (Δr ++ [X.impl Y] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
        ([X] ++ Γr) ([Y] ++ Δr ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δr ++ K) ++ [A] ++ Λ) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ Δr ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δr ++ K) ++ [B] ++ Λ) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ Δr ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr Δr (K ++ [A] ++ Λ) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr Δr (K ++ [B] ++ Λ) X Y) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.impl X Y] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.impl X Y] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.impl X Y] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.impl X Y] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
        ([X] ++ Γr) ([Y] ++ Δ) (K ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δ) ++ [A] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ (Δ ++ [A] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δ) ++ [B] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ (Δ ++ [B] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr (Δ ++ [A] ++ K) Λr X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr (Δ ++ [B] ++ K) Λr X Y) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.impl X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.impl X Y] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.impl X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.impl X Y] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_negLeft
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List
      (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X] ++ succ))) (hsubdepth
      : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr ++ [X.neg] ++ Δr) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++ Δr) ([X] ++ Δ) Λ
      (by simp [List.append_assoc]) hsubleaf
  have heq1 : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [A] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [A] ++ Λ)) := by
    simp [List.append_assoc]
  have heq2 : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [B] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [B] ++ Λ)) := by
    simp [List.append_assoc]
  let q1' := heq1 ▸ q1
  let q2' := heq2 ▸ q2
  have hdq1 : geqDepth q1' = geqDepth q1 := by
    exact geqDepth_transport heq1 q1
  have hdq2 : geqDepth q2' = geqDepth q2 := by
    exact geqDepth_transport heq2 q2
  refine ⟨.onePremise (.negLeft Γr Δr (Δ ++ [A] ++ Λ) X) q1', .onePremise
      (.negLeft Γr Δr (Δ ++ [B] ++ Λ) X) q2', by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using (geqLeafProperty_transport heq1 q1 hq1leaf)
  · simpa [geqLeafSequents] using (geqLeafProperty_transport heq2 q2 hq2leaf)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_negRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) (Δr ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr
      ++ [X.neg] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B ([X] ++ Γr) (Δr ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) ((Δr ++ K) ++ [A] ++ Λ) = Sequent.mk ([X] ++ Γr)
            (Δr ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) ((Δr ++ K) ++ [B] ++ Λ) = Sequent.mk ([X] ++ Γr)
            (Δr ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr Δr (K ++ [A] ++ Λ) X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr Δr (K ++ [B] ++ Λ) X) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.neg X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.neg X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.neg X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.neg X] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B ([X] ++ Γr) Δ (K ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (Δ ++ [A] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ((Δ ++ [A] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (Δ ++ [B] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ((Δ ++ [B] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr (Δ ++ [A] ++ K) Λr X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr (Δ ++ [B] ++ K) Λr X) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.neg X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [A] ++ (K ++ [FormulaN.neg X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.neg X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [B] ++ (K ++ [FormulaN.neg X] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

end
end LCS.CutElim.LKe.Equivalence
end
