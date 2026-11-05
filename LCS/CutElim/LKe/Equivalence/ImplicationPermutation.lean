import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
import Attach
import LCS.CutElim.LKe.Equivalence.ImplicationPermutation.ProofsStamp

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
section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++
      Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_exLeft
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (implFresh1 : ∀ (y :
      Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++ Δ ++ Λ
      → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ ++ Δ ++ (Λ ++ [A]) → ¬y ∈ formulaFVN F) (implFresh2 : ∀
      (y : Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++ Δ
      ++ Λ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ [B] ++ Γ ++ Δ ++ Λ → ¬y ∈ formulaFVN F) (A B :
      FormulaN L) (Γ Δ Λ : List (FormulaN L)) (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN
      L) (hfresh : ∀ (F : FormulaN L), F ∈ (Γr ++ [FormulaN.ex x X] ++ Δr) ++ (Λr) → ¬y ∈ formulaFVN F) (hfree
      : isFreeForN (Term.var y) x X) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [formulaSubstN X (Term.var y)
      x] ++ Δr) (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub
      → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (Λr)) = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)))
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
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ K)
        Δ Λr (by simp [List.append_assoc]) hsubleaf
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 (Γr ++
          [Substitution.formulaSubstN X (Term.var y) x] ++
          (K ++ Δ))
        (Λr ++ [A]) (by simp [List.append_assoc])
        (List.Perm.refl _) hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γr) ++
          [Substitution.formulaSubstN X (Term.var y) x] ++
          (K ++ Δ))
        Λr (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    have hfresh1 : ∀ F ∈ (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ (K ++ Δ)) (Λr ++ [A])).antecedent ++
            (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ (K ++ Δ)) (Λr ++ [A])).succedent,
          y ∉ Variables.formulaFVN F := by
      have hfresh' : ∀ F ∈ ((Γr ++ [FormulaN.ex x X] ++ K) ++ [FormulaN.impl A B] ++ Δ) ++ Λr,
            y ∉ Variables.formulaFVN F := by
        simpa [List.append_assoc] using hfresh
      simpa [List.append_assoc] using implFresh1 y A B (Γr ++ [FormulaN.ex x X] ++ K) Δ Λr hfresh'
    have hfresh2 : ∀ F ∈ (Sequent.mk (([B] ++ Γr) ++ [FormulaN.ex x X] ++ (K ++ Δ)) Λr).antecedent ++
            (Sequent.mk (([B] ++ Γr) ++ [FormulaN.ex x X] ++ (K ++ Δ)) Λr).succedent,
          y ∉ Variables.formulaFVN F := by
      have hfresh' : ∀ F ∈ ((Γr ++ [FormulaN.ex x X] ++ K) ++ [FormulaN.impl A B] ++ Δ) ++ Λr,
            y ∉ Variables.formulaFVN F := by
        simpa [List.append_assoc] using hfresh
      simpa [List.append_assoc] using implFresh2 y A B (Γr ++ [FormulaN.ex x X] ++ K) Δ Λr hfresh'
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exLeft y Γr (K ++ Δ) (Λr ++ [A]) x X hfresh1 hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exLeft y ([B] ++ Γr) (K ++ Δ) Λr x X hfresh2 hfree) q2'
    have hout1 : Sequent.mk (Γr ++ [FormulaN.ex x X] ++ (K ++ Δ)) (Λr ++ [A]) = Sequent.mk
            ((Γr ++ [FormulaN.ex x X] ++ K) ++ Δ)
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γr) ++ [FormulaN.ex x X] ++ (K ++ Δ)) Λr = Sequent.mk
            ([B] ++ (Γr ++ [FormulaN.ex x X] ++ K) ++ Δ)
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
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γ (K ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ Δr)
        Λr (by simp [List.append_assoc]) hsubleaf
    obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ((Γ ++ K) ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ Δr)
        (Λr ++ [A]) (by simp [List.append_assoc])
        (List.Perm.refl _) hq1leaf
    obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γ ++ K) ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ Δr)
        Λr (by simp [List.append_assoc])
        (List.Perm.refl _) hq2leaf
    have hfresh1 : ∀ F ∈ (Sequent.mk ((Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) (Λr ++ [A])).antecedent ++
            (Sequent.mk ((Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) (Λr ++ [A])).succedent,
          y ∉ Variables.formulaFVN F := by
      have hfresh' : ∀ F ∈ (Γ ++ [FormulaN.impl A B] ++ (K ++ [FormulaN.ex x X] ++ Δr)) ++ Λr,
            y ∉ Variables.formulaFVN F := by
        simpa [List.append_assoc] using hfresh
      simpa [List.append_assoc] using implFresh1 y A B Γ (K ++ [FormulaN.ex x X] ++ Δr) Λr hfresh'
    have hfresh2 : ∀ F ∈ (Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) Λr).antecedent ++
            (Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) Λr).succedent,
          y ∉ Variables.formulaFVN F := by
      have hfresh' : ∀ F ∈ (Γ ++ [FormulaN.impl A B] ++ (K ++ [FormulaN.ex x X] ++ Δr)) ++ Λr,
            y ∉ Variables.formulaFVN F := by
        simpa [List.append_assoc] using hfresh
      simpa [List.append_assoc] using implFresh2 y A B Γ (K ++ [FormulaN.ex x X] ++ Δr) Λr hfresh'
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exLeft y (Γ ++ K) Δr (Λr ++ [A]) x X hfresh1 hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exLeft y ([B] ++ Γ ++ K) Δr Λr x X hfresh2 hfree) q2'
    have hout1 : Sequent.mk ((Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) (Λr ++ [A]) = Sequent.mk
            (Γ ++ (K ++ [FormulaN.ex x X] ++ Δr))
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.ex x X] ++ Δr) Λr = Sequent.mk ([B] ++ Γ ++
              (K ++ [FormulaN.ex x X] ++ Δr)) Λr := by
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

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_exRight
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (ts : List
      (Term L)) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hne : ts ≠ []) (hfree : ∀ (t : Term
      L), t ∈ ts → isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ List.map (fun (t : Term L)
      => formulaSubstN X t x) ts ++ [FormulaN.ex x X] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr
      ++ [FormulaN.ex x X] ++ Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γr
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γ Δ (Δr ++
        ts.map (fun t => Substitution.formulaSubstN X t x) ++
        [FormulaN.ex x X] ++ Λr)
      rfl hsubleaf
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 (Γ ++ Δ) (Δr ++
        ts.map (fun t => Substitution.formulaSubstN X t x) ++
        [FormulaN.ex x X] ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) hq1leaf
  let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts (Γ ++ Δ) Δr (Λr ++ [A]) x X hne hfree) q1'
  let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts ([B] ++ Γ ++ Δ) Δr Λr x X hne hfree) q2
  have hout1 : Sequent.mk (Γ ++ Δ) (Δr ++ [FormulaN.ex x X] ++ (Λr ++ [A])) = Sequent.mk (Γ ++ Δ)
          ((Δr ++ [FormulaN.ex x X] ++ Λr) ++ [A]) := by
    simp [List.append_assoc]
  let p1 := hout1 ▸ r1
  let p2 := r2
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
  · simpa [p2, r2, geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_permOne
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (implFresh1 : ∀ (y :
      Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++ Δ ++ Λ
      → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ ++ Δ ++ (Λ ++ [A]) → ¬y ∈ formulaFVN F) (implFresh2 : ∀
      (y : Nat) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), (∀ (F : FormulaN L), F ∈ Γ ++ [A.impl B] ++ Δ
      ++ Λ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ [B] ++ Γ ++ Δ ++ Λ → ¬y ∈ formulaFVN F) (A B :
      FormulaN L) (Γ Δ Λ : List (FormulaN L))
    : ∀ {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub
      < n → conc = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 :
      GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth
      sub ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  intro prem conc rule sub hsubdepth hconc hsubleaf
  cases rule with
  | conjLeft Γr Δr Λr X Y =>
    exact geqImplLeft_conjLeft L hL n ih markedSplit geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub hsubdepth hsubleaf hconc
  | disjRight Γr Δr Λr X Y =>
    exact geqImplLeft_disjRight L hL n ih geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub hsubdepth hsubleaf hconc
  | implRight Γr Δr Λr X Y =>
    exact geqImplLeft_implRight L hL n ih geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub hsubdepth hsubleaf hconc
  | negLeft Γr Δr Λr X =>
    exact geqImplLeft_negLeft L hL n ih markedSplit geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X sub hsubdepth hsubleaf hconc
  | negRight Γr Δr Λr X =>
    exact geqImplLeft_negRight L hL n ih geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X sub hsubdepth hsubleaf hconc
  | allLeft ts Γr Δr Λr x X hne hfree =>
    exact geqImplLeft_allLeft L hL n ih markedSplit geqDepth_transport geqLeaf_transport A B Γ Δ Λ ts Γr Δr Λr x X hne hfree sub hsubdepth hsubleaf hconc
  | allRight y Γr Δr Λr x X hfresh hfree =>
    exact geqImplLeft_allRight L hL n ih geqDepth_transport geqLeaf_transport implFresh1 implFresh2 A B Γ Δ Λ y Γr Δr Λr x X hfresh hfree sub hsubdepth hsubleaf hconc
  | exLeft y Γr Δr Λr x X hfresh hfree =>
    exact geqImplLeft_exLeft L hL n ih markedSplit geqDepth_transport geqLeaf_transport implFresh1 implFresh2 A B Γ Δ Λ y Γr Δr Λr x X hfresh hfree sub hsubdepth hsubleaf hconc
  | exRight ts Γr Δr Λr x X hne hfree =>
    exact geqImplLeft_exRight L hL n ih geqDepth_transport geqLeaf_transport A B Γ Δ Λ ts Γr Δr Λr x X hne hfree sub hsubdepth hsubleaf hconc

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_conjRight
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L))
      (X Y : FormulaN L) (sub1 : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X] ++ Λr))) (hsub1depth : geqDepth
      sub1 < n) (hsub1leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s')
      (sub2 : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [Y] ++ Λr))) (hsub2depth : geqDepth sub2 < n) (hsub2leaf
      : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr)
      (Δr ++ [X.conj Y] ++ Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γr
  subst Λ
  obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B Γ Δ
      (Δr ++ [X] ++ Λr) rfl hsub1leaf
  obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B Γ Δ
      (Δr ++ [Y] ++ Λr) rfl hsub2leaf
  obtain ⟨a1', ha1'd, ha1'leaf⟩ := geqPermuteContexts a1 (Γ ++ Δ) (Δr ++ [X] ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) ha1leaf
  obtain ⟨a2', ha2'd, ha2'leaf⟩ := geqPermuteContexts a2 (Γ ++ Δ) (Δr ++ [Y] ++ (Λr ++ [A]))
      (by simp [List.append_assoc])
      (by simp [List.append_assoc]) ha2leaf
  let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight (Γ ++ Δ) Δr (Λr ++ [A]) X Y) a1' a2'
  let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight ([B] ++ Γ ++ Δ) Δr Λr X Y) b1 b2
  have hout1 : Sequent.mk (Γ ++ Δ) (Δr ++ [FormulaN.conj X Y] ++ (Λr ++ [A])) = Sequent.mk (Γ ++ Δ)
          ((Δr ++ [FormulaN.conj X Y] ++ Λr) ++ [A]) := by
    simp [List.append_assoc]
  let p1 := hout1 ▸ r1
  let p2 := r2
  have hp1d : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
    rw [geqDepth_transport hout1 r1]
    simp only [r1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := rfl
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    rw [geqLeaf_transport hout1 r1] at hs'
    simp only [r1, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (ha1'leaf s') (ha2'leaf s')
  · intro s' hs'
    simp only [p2, r2, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (hb1leaf s') (hb2leaf s')

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_disjLeft
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ
      Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub1 : GEqProofTree hL (Sequent.mk (Γr ++ [X] ++
      Δr) (Λr))) (hsub1depth : geqDepth sub1 < n) (hsub1leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 →
      seqAllAtomicOrQuantified s') (sub2 : GEqProofTree hL (Sequent.mk (Γr ++ [Y] ++ Δr) (Λr))) (hsub2depth :
      geqDepth sub2 < n) (hsub2leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr ++ [X.disj Y] ++ Δr) (Λr)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Λ
  rcases markedSplit hant (by simp) with
    ⟨K, hΓ, hΔr⟩ | ⟨K, hΓr, hΔ⟩
  · subst Γ
    subst Δr
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B (Γr ++ [X] ++ K) Δ Λr
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B (Γr ++ [Y] ++ K) Δ Λr
        (by simp [List.append_assoc]) hsub2leaf
    obtain ⟨a1', ha1'd, ha1'leaf⟩ := geqPermuteContexts a1 (Γr ++ [X] ++ (K ++ Δ)) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha1leaf
    obtain ⟨a2', ha2'd, ha2'leaf⟩ := geqPermuteContexts a2 (Γr ++ [Y] ++ (K ++ Δ)) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha2leaf
    obtain ⟨b1', hb1'd, hb1'leaf⟩ := geqPermuteContexts b1 (([B] ++ Γr) ++ [X] ++ (K ++ Δ)) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb1leaf
    obtain ⟨b2', hb2'd, hb2'leaf⟩ := geqPermuteContexts b2 (([B] ++ Γr) ++ [Y] ++ (K ++ Δ)) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb2leaf
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft Γr (K ++ Δ) (Λr ++ [A]) X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft ([B] ++ Γr) (K ++ Δ) Λr X Y) b1' b2'
    have hout1 : Sequent.mk (Γr ++ [FormulaN.disj X Y] ++ (K ++ Δ)) (Λr ++ [A]) = Sequent.mk
            ((Γr ++ [FormulaN.disj X Y] ++ K) ++ Δ)
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γr) ++ [FormulaN.disj X Y] ++ (K ++ Δ)) Λr = Sequent.mk
            ([B] ++ (Γr ++ [FormulaN.disj X Y] ++ K) ++ Δ)
            Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (ha1'leaf s') (ha2'leaf s')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hb1'leaf s') (hb2'leaf s')
  · subst Γr
    subst Δ
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B Γ (K ++ [X] ++ Δr) Λr
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B Γ (K ++ [Y] ++ Δr) Λr
        (by simp [List.append_assoc]) hsub2leaf
    obtain ⟨a1', ha1'd, ha1'leaf⟩ := geqPermuteContexts a1 ((Γ ++ K) ++ [X] ++ Δr) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha1leaf
    obtain ⟨a2', ha2'd, ha2'leaf⟩ := geqPermuteContexts a2 ((Γ ++ K) ++ [Y] ++ Δr) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha2leaf
    obtain ⟨b1', hb1'd, hb1'leaf⟩ := geqPermuteContexts b1 (([B] ++ Γ ++ K) ++ [X] ++ Δr) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb1leaf
    obtain ⟨b2', hb2'd, hb2'leaf⟩ := geqPermuteContexts b2 (([B] ++ Γ ++ K) ++ [Y] ++ Δr) Λr
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb2leaf
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft (Γ ++ K) Δr (Λr ++ [A]) X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft ([B] ++ Γ ++ K) Δr Λr X Y) b1' b2'
    have hout1 : Sequent.mk ((Γ ++ K) ++ [FormulaN.disj X Y] ++ Δr) (Λr ++ [A]) = Sequent.mk
            (Γ ++ (K ++ [FormulaN.disj X Y] ++ Δr))
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.disj X Y] ++ Δr) Λr = Sequent.mk ([B] ++ Γ ++
              (K ++ [FormulaN.disj X Y] ++ Δr)) Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (ha1'leaf s') (ha2'leaf s')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hb1'leaf s') (hb2'leaf s')

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_implLeft
    (markedSplit3 : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → (∃ (K
      : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧ X = Y ∧ Q = S ∨ ∃ (K : List
      (FormulaN L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeaf_transport : ∀ {s₁ s₂ :
      Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p) (A B
      : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub1 : GEqProofTree hL
      (Sequent.mk (Γr ++ Δr) ([X] ++ Λr))) (hsub1depth : geqDepth sub1 < n) (hsub1leaf : ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') (sub2 : GEqProofTree hL (Sequent.mk ([Y] ++ Γr
      ++ Δr) (Λr))) (hsub2depth : geqDepth sub2 < n) (hsub2leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub2 → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.impl Y] ++ Δr) (Λr)) = (Sequent.mk (Γ
      ++ [A.impl B] ++ Δ) (Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Λ
  rcases markedSplit3 hant with
    ⟨K, hΓ, hΔr⟩ |
    ⟨hΓr, hXY, hΔr⟩ |
    ⟨K, hΓr, hΔ⟩
  · subst Γ
    subst Δr
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B
        (Γr ++ K) Δ ([X] ++ Λr)
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B ([Y] ++ Γr ++ K) Δ Λr
        (by simp [List.append_assoc]) hsub2leaf
    have hswapXA : (([X] ++ Λr) ++ [A]).Perm ([X] ++ (Λr ++ [A])) := by
      simp [List.append_assoc]
    obtain ⟨a1', ha1'd, ha1'leaf⟩ := geqPermuteContexts a1 (Γr ++ (K ++ Δ)) ([X] ++ (Λr ++ [A]))
        (by simp [List.append_assoc]) hswapXA ha1leaf
    obtain ⟨a2', ha2'd, ha2'leaf⟩ := geqPermuteContexts a2 ([Y] ++ Γr ++ (K ++ Δ)) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha2leaf
    obtain ⟨b1', hb1'd, hb1'leaf⟩ := geqPermuteContexts b1 (([B] ++ Γr) ++ (K ++ Δ)) ([X] ++ Λr)
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb1leaf
    have hswapBY : ([B] ++ ([Y] ++ Γr ++ K) ++ Δ).Perm ([Y] ++ ([B] ++ Γr) ++ (K ++ Δ)) := by
      simpa [List.append_assoc] using (List.Perm.append_right (Γr ++ K ++ Δ) (List.Perm.swap Y B []))
    obtain ⟨b2', hb2'd, hb2'leaf⟩ := geqPermuteContexts b2 ([Y] ++ ([B] ++ Γr) ++ (K ++ Δ)) Λr
        hswapBY (List.Perm.refl _) hb2leaf
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft Γr (K ++ Δ) (Λr ++ [A]) X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft ([B] ++ Γr) (K ++ Δ) Λr X Y) b1' b2'
    have hout1 : Sequent.mk (Γr ++ [FormulaN.impl X Y] ++ (K ++ Δ)) (Λr ++ [A]) = Sequent.mk
            ((Γr ++ [FormulaN.impl X Y] ++ K) ++ Δ)
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γr) ++ [FormulaN.impl X Y] ++ (K ++ Δ)) Λr = Sequent.mk
            ([B] ++ (Γr ++ [FormulaN.impl X Y] ++ K) ++ Δ)
            Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (ha1'leaf s') (ha2'leaf s')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hb1'leaf s') (hb2'leaf s')
  · subst Γr
    subst Δr
    injection hXY with hX hY
    subst X
    subst Y
    obtain ⟨p1, hp1depth, hp1leaf⟩ := geqPermuteContexts sub1 (Γ ++ Δ) (Λr ++ [A])
        (List.Perm.refl _) (by exact List.perm_append_comm) hsub1leaf
    refine ⟨p1, sub2, ?_, hp1leaf, hsub2leaf⟩
    omega
  · subst Γr
    subst Δ
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B Γ
        (K ++ Δr) ([X] ++ Λr)
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B
        ([Y] ++ Γ) (K ++ Δr) Λr
        (by simp [List.append_assoc]) hsub2leaf
    have hswapXA : (([X] ++ Λr) ++ [A]).Perm ([X] ++ (Λr ++ [A])) := by
      simp [List.append_assoc]
    obtain ⟨a1', ha1'd, ha1'leaf⟩ := geqPermuteContexts a1 ((Γ ++ K) ++ Δr) ([X] ++ (Λr ++ [A]))
        (by simp [List.append_assoc]) hswapXA ha1leaf
    obtain ⟨a2', ha2'd, ha2'leaf⟩ := geqPermuteContexts a2 ([Y] ++ (Γ ++ K) ++ Δr) (Λr ++ [A])
        (by simp [List.append_assoc])
        (List.Perm.refl _) ha2leaf
    obtain ⟨b1', hb1'd, hb1'leaf⟩ := geqPermuteContexts b1 (([B] ++ Γ ++ K) ++ Δr) ([X] ++ Λr)
        (by simp [List.append_assoc])
        (List.Perm.refl _) hb1leaf
    have hswapBY : ([B] ++ ([Y] ++ Γ) ++ (K ++ Δr)).Perm ([Y] ++ ([B] ++ Γ ++ K) ++ Δr) := by
      simpa [List.append_assoc] using (List.Perm.append_right (Γ ++ K ++ Δr) (List.Perm.swap Y B []))
    obtain ⟨b2', hb2'd, hb2'leaf⟩ := geqPermuteContexts b2 ([Y] ++ ([B] ++ Γ ++ K) ++ Δr) Λr
        hswapBY (List.Perm.refl _) hb2leaf
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft (Γ ++ K) Δr (Λr ++ [A]) X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft ([B] ++ Γ ++ K) Δr Λr X Y) b1' b2'
    have hout1 : Sequent.mk ((Γ ++ K) ++ [FormulaN.impl X Y] ++ Δr) (Λr ++ [A]) = Sequent.mk
            (Γ ++ (K ++ [FormulaN.impl X Y] ++ Δr))
            (Λr ++ [A]) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk (([B] ++ Γ ++ K) ++ [FormulaN.impl X Y] ++ Δr) Λr = Sequent.mk ([B] ++ Γ ++
              (K ++ [FormulaN.impl X Y] ++ Δr)) Λr := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hp1d : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hp2d : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · intro s' hs'
      rw [geqLeaf_transport hout1 r1] at hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (ha1'leaf s') (ha2'leaf s')
    · intro s' hs'
      rw [geqLeaf_transport hout2 r2] at hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hb1'leaf s') (hb2'leaf s')

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_permTwo
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (markedSplit3 : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++
      [X] ++ Q = R ++ [Y] ++ S → (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧
      X = Y ∧ Q = S ∨ ∃ (K : List (FormulaN L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p)
      (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents
      (heq ▸ p) = geqLeafSequents p) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL
      prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc = (Sequent.mk (Γ ++
      [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') →
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL
      (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) (Λ))), 1 + max
      (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  intro prem1 prem2 conc rule sub1 sub2 hsub1depth hsub2depth hconc hsub1leaf hsub2leaf
  cases rule with
  | conjRight Γr Δr Λr X Y =>
    exact geqImplLeft_conjRight L hL n ih geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc
  | disjLeft Γr Δr Λr X Y =>
    exact geqImplLeft_disjLeft L hL n ih markedSplit geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc
  | implLeft Γr Δr Λr X Y =>
    exact geqImplLeft_implLeft L hL n ih markedSplit3 geqDepth_transport geqLeaf_transport A B Γ Δ Λ Γr Δr Λr X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_eqRefl
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (t : Term L) (Γe Λe : List (FormulaN L)) (sub :
      GEqProofTree hL (Sequent.mk (Γe ++ [FormulaN.eq_ hL t t]) (Λe))) (hseq : (Sequent.mk (Γe) (Λe)) =
      (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (hdepth : geqDepth (GEqProofTree.eqRefl t Γe Λe sub) = n)
      (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqRefl t Γe Λe sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqRefl t Γe Λe sub) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γe
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl A B Γ (Δ ++ [FormulaN.eq_ hL t t]) Λe
      (by simp [List.append_assoc]) (by
        simpa [geqLeafSequents] using hleaf)
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ((Γ ++ Δ) ++ [FormulaN.eq_ hL t t]) (Λe ++ [A])
      (by simp [List.append_assoc]) (List.Perm.refl _) hq1leaf
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γ ++ Δ) ++ [FormulaN.eq_ hL t t]) Λe
      (by simp [List.append_assoc]) (List.Perm.refl _) hq2leaf
  let p1 := GEqProofTree.eqRefl t (Γ ++ Δ) (Λe ++ [A]) q1'
  let p2 := GEqProofTree.eqRefl t ([B] ++ Γ ++ Δ) Λe q2'
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    simp only [p1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, geqDepth]
    omega
  refine ⟨p1, p2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1'leaf
  · simpa [p2, geqLeafSequents] using hq2'leaf

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_eqFuncCong
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
      (Γe Λe : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γe ++ [eqCongruenceImplFunc L hL f ss
      ts]) (Λe))) (hseq : (Sequent.mk (Γe) (Λe)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (hdepth : geqDepth
      (GEqProofTree.eqFuncCong f ss ts Γe Λe sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      (GEqProofTree.eqFuncCong f ss ts Γe Λe sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqFuncCong f ss ts Γe Λe sub)
      ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γe
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl A B Γ (Δ ++ [eqCongruenceImplFunc L hL f ss ts]) Λe
      (by simp [List.append_assoc]) (by
        simpa [geqLeafSequents] using hleaf)
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1
      ((Γ ++ Δ) ++ [eqCongruenceImplFunc L hL f ss ts]) (Λe ++ [A])
      (by simp [List.append_assoc]) (List.Perm.refl _) hq1leaf
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2
      (([B] ++ Γ ++ Δ) ++ [eqCongruenceImplFunc L hL f ss ts]) Λe
      (by simp [List.append_assoc]) (List.Perm.refl _) hq2leaf
  let p1 := GEqProofTree.eqFuncCong f ss ts (Γ ++ Δ) (Λe ++ [A]) q1'
  let p2 := GEqProofTree.eqFuncCong f ss ts ([B] ++ Γ ++ Δ) Λe q2'
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    simp only [p1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, geqDepth]
    omega
  refine ⟨p1, p2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1'leaf
  · simpa [p2, geqLeafSequents] using hq2'leaf

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_eqPredCong
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (P : L.predSymbols) (ss ts : Fin
      (L.predArity P) → Term L) (Γe Λe : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γe ++
      [eqCongruenceImplPred L hL P ss ts]) (Λe))) (hseq : (Sequent.mk (Γe) (Λe)) = (Sequent.mk (Γ ++ [A.impl
      B] ++ Δ) (Λ))) (hdepth : geqDepth (GEqProofTree.eqPredCong P ss ts Γe Λe sub) = n) (hleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqPredCong P ss ts Γe Λe sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqPredCong P ss ts Γe Λe
      sub) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γe
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl A B Γ (Δ ++ [eqCongruenceImplPred L hL P ss ts]) Λe
      (by simp [List.append_assoc]) (by
        simpa [geqLeafSequents] using hleaf)
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1
      ((Γ ++ Δ) ++ [eqCongruenceImplPred L hL P ss ts]) (Λe ++ [A])
      (by simp [List.append_assoc]) (List.Perm.refl _) hq1leaf
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2
      (([B] ++ Γ ++ Δ) ++ [eqCongruenceImplPred L hL P ss ts]) Λe
      (by simp [List.append_assoc]) (List.Perm.refl _) hq2leaf
  let p1 := GEqProofTree.eqPredCong P ss ts (Γ ++ Δ) (Λe ++ [A]) q1'
  let p2 := GEqProofTree.eqPredCong P ss ts ([B] ++ Γ ++ Δ) Λe q2'
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    simp only [p1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, geqDepth]
    omega
  refine ⟨p1, p2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1'leaf
  · simpa [p2, geqLeafSequents] using hq2'leaf

-- ATTACH-BLOCKER: private declaration
private theorem geqImplLeft_eqGeneral
    (A B : FormulaN L) (Γ Δ Λ axioms : List (FormulaN L)) (hne : axioms ≠ []) (haxioms : ∀ (A : FormulaN L), A
      ∈ axioms → isEqAxiomInstance hL A) (Γe Λe : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γe ++
      axioms) (Λe))) (hseq : (Sequent.mk (Γe) (Λe)) = (Sequent.mk (Γ ++ [A.impl B] ++ Δ) (Λ))) (hdepth :
      geqDepth (GEqProofTree.eqGeneral axioms hne haxioms Γe Λe sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.eqGeneral axioms hne haxioms Γe Λe sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ
      ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqGeneral axioms hne haxioms
      Γe Λe sub) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γe
  subst Λ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl A B Γ (Δ ++ axioms) Λe
      (by simp [List.append_assoc]) (by
        simpa [geqLeafSequents] using hleaf)
  obtain ⟨q1', hq1'd, hq1'leaf⟩ := geqPermuteContexts q1 ((Γ ++ Δ) ++ axioms) (Λe ++ [A])
      (by simp [List.append_assoc]) (List.Perm.refl _) hq1leaf
  obtain ⟨q2', hq2'd, hq2'leaf⟩ := geqPermuteContexts q2 (([B] ++ Γ ++ Δ) ++ axioms) Λe
      (by simp [List.append_assoc]) (List.Perm.refl _) hq2leaf
  let p1 := GEqProofTree.eqGeneral axioms hne haxioms (Γ ++ Δ) (Λe ++ [A]) q1'
  let p2 := GEqProofTree.eqGeneral axioms hne haxioms ([B] ++ Γ ++ Δ) Λe q2'
  have hp1d : geqDepth p1 = 1 + geqDepth q1 := by
    simp only [p1, geqDepth]
    omega
  have hp2d : geqDepth p2 = 1 + geqDepth q2 := by
    simp only [p2, geqDepth]
    omega
  refine ⟨p1, p2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1'leaf
  · simpa [p2, geqLeafSequents] using hq2'leaf

end
end LCS.CutElim.LKe.Equivalence
end

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper for Lemma 6.3.2: directly commute implication-left to the
root of a G=-proof whose selected occurrence of `A ⊃ B` has arbitrary
antecedent prefix and suffix contexts.  The returned trees are indexed
with the first premise presented as Γ, Δ → Λ, A and the second as
B, Γ, Δ → Λ. Context permutation moves A to the front when assembling
an implication-left rule; equality-rule constructors remain available
throughout the transformation.
This strengthened companion also returns the leaf invariant needed by
the direct G= normalizer to recurse through the two premises. -/
theorem geqPermute_implLeft_withLeaves {L : Language}
    {hL : L.hasEquality = true}
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    (T : GEqProofTree hL
      (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ))
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A])))
      (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) Λ)),
      1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧
      (∀ s' ∈ geqLeafSequents p1,
        seqAllAtomicOrQuantified s') ∧
      (∀ s' ∈ geqLeafSequents p2,
        seqAllAtomicOrQuantified s') := by
-- BEGIN PROOF
  have markedSplit :
      ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L},
        P ++ [X] ++ Q = R ++ [Y] ++ S →
        X ≠ Y →
        (∃ K, R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨
        (∃ K, P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) := by
    exact geqImplLeft_markedSplit L
  have markedSplit3 :
      ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L},
        P ++ [X] ++ Q = R ++ [Y] ++ S →
        (∃ K, R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨
        (P = R ∧ X = Y ∧ Q = S) ∨
        (∃ K, P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) := by
    exact geqImplLeft_markedSplit3 L
  have geqDepth_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
        (p : GEqProofTree hL s₁),
        geqDepth (heq ▸ p) = geqDepth p := by
    exact geqImplLeft_geqDepth_transport L hL
  have geqLeaf_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
        (p : GEqProofTree hL s₁),
        geqLeafSequents (heq ▸ p) = geqLeafSequents p := by
    exact geqImplLeft_geqLeaf_transport L hL
  have implFresh1 :
      ∀ (y : Nat) (A B : FormulaN L)
        (Γ Δ Λ : List (FormulaN L)),
        (∀ F ∈ (Γ ++ [FormulaN.impl A B] ++ Δ) ++ Λ,
          y ∉ Variables.formulaFVN F) →
        ∀ F ∈ (Γ ++ Δ) ++ (Λ ++ [A]),
          y ∉ Variables.formulaFVN F := by
    exact geqImplLeft_implFresh1 L
  have implFresh2 :
      ∀ (y : Nat) (A B : FormulaN L)
        (Γ Δ Λ : List (FormulaN L)),
        (∀ F ∈ (Γ ++ [FormulaN.impl A B] ++ Δ) ++ Λ,
          y ∉ Variables.formulaFVN F) →
        ∀ F ∈ ([B] ++ Γ ++ Δ) ++ Λ,
          y ∉ Variables.formulaFVN F := by
    exact geqImplLeft_implFresh2 L
  suffices h :
      ∀ n : Nat, ∀ {s : Sequent L} (T : GEqProofTree hL s),
        geqDepth T = n →
        ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)),
        s = Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ →
        (∀ s' ∈ geqLeafSequents T,
          seqAllAtomicOrQuantified s') →
        ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A])))
          (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) Λ)),
          1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧
          (∀ s' ∈ geqLeafSequents p1,
            seqAllAtomicOrQuantified s') ∧
          (∀ s' ∈ geqLeafSequents p2,
            seqAllAtomicOrQuantified s') by
    exact h (geqDepth T) T rfl A B Γ Δ Λ rfl hleaf
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s T hdepth A B Γ Δ Λ hseq hleaf
    have permOne :
        ∀ {prem conc : Sequent L}
          (rule : GentzenStep1Ext prem conc)
          (sub : GEqProofTree hL prem),
          geqDepth sub < n →
          conc =
            Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ →
          (∀ s' ∈ geqLeafSequents sub,
            seqAllAtomicOrQuantified s') →
          ∃ (p1 : GEqProofTree hL
                (Sequent.mk (Γ ++ Δ) (Λ ++ [A])))
            (p2 : GEqProofTree hL
                (Sequent.mk ([B] ++ Γ ++ Δ) Λ)),
            1 + max (geqDepth p1) (geqDepth p2) =
                1 + geqDepth sub ∧
            (∀ s' ∈ geqLeafSequents p1,
              seqAllAtomicOrQuantified s') ∧
            (∀ s' ∈ geqLeafSequents p2,
              seqAllAtomicOrQuantified s') := by
      exact geqImplLeft_permOne L hL n ih markedSplit geqDepth_transport geqLeaf_transport implFresh1 implFresh2 A B Γ Δ Λ
    have permTwo :
        ∀ {prem1 prem2 conc : Sequent L}
          (rule : GentzenStep2Ext prem1 prem2 conc)
          (sub1 : GEqProofTree hL prem1)
          (sub2 : GEqProofTree hL prem2),
          geqDepth sub1 < n →
          geqDepth sub2 < n →
          conc =
            Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ →
          (∀ s' ∈ geqLeafSequents sub1,
            seqAllAtomicOrQuantified s') →
          (∀ s' ∈ geqLeafSequents sub2,
            seqAllAtomicOrQuantified s') →
          ∃ (p1 : GEqProofTree hL
                (Sequent.mk (Γ ++ Δ) (Λ ++ [A])))
            (p2 : GEqProofTree hL
                (Sequent.mk ([B] ++ Γ ++ Δ) Λ)),
            1 + max (geqDepth p1) (geqDepth p2) =
                1 + max (geqDepth sub1) (geqDepth sub2) ∧
            (∀ s' ∈ geqLeafSequents p1,
              seqAllAtomicOrQuantified s') ∧
            (∀ s' ∈ geqLeafSequents p2,
              seqAllAtomicOrQuantified s') := by
      exact geqImplLeft_permTwo L hL n ih markedSplit markedSplit3 geqDepth_transport geqLeaf_transport A B Γ Δ Λ
    cases T with
    | base g =>
      exact geqImplLeft_base L hL n s A B _ _ _ hseq permOne permTwo g hdepth hleaf
    | axiom_ s hAx =>
      exact geqImplLeft_axiom_ L hL s A B _ _ _ hseq _ hleaf
    | onePremise rule sub =>
      exact geqImplLeft_onePremise L hL n _ _ _ _ _ _ hseq permOne _ sub rule hdepth hleaf
    | twoPremise rule sub1 sub2 =>
      exact geqImplLeft_twoPremise L hL n _ _ _ _ _ _ hseq permTwo _ _ sub1 sub2 rule hdepth hleaf
    | eqRefl t Γe Λe sub =>
      exact geqImplLeft_eqRefl L hL n ih A B Γ Δ Λ t Γe Λe sub hseq hdepth hleaf
    | eqFuncCong f ss ts Γe Λe sub =>
      exact geqImplLeft_eqFuncCong L hL n ih A B Γ Δ Λ f ss ts Γe Λe sub hseq hdepth hleaf
    | eqPredCong P ss ts Γe Λe sub =>
      exact geqImplLeft_eqPredCong L hL n ih A B Γ Δ Λ P ss ts Γe Λe sub hseq hdepth hleaf
    | eqGeneral axioms hne haxioms Γe Λe sub =>
      exact geqImplLeft_eqGeneral L hL n ih A B Γ Δ Λ axioms hne haxioms Γe Λe sub hseq hdepth hleaf

-- The equality rules are essential here: G= proves reflexivity even
-- though the same conclusion has no pure-G proof tree.  This bounded
-- regression prevents a future helper from restoring the false
-- same-conclusion flattening route.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (hL : L.hasEquality = true) (t : Term L) :
    Nonempty
        (GEqProofTree hL
          (Sequent.mk [] [FormulaN.eq_ hL t t])) ∧
      ¬ Nonempty
        (GProofTreeExt
          (Sequent.mk [] [FormulaN.eq_ hL t t])) := by
  constructor
  · let A := FormulaN.eq_ hL t t
    let ax : GEqProofTree hL (Sequent.mk [A] [A]) :=
      .axiom_ (Sequent.mk [A] [A]) ⟨A, by simp, by simp⟩
    exact ⟨.eqRefl t [] [A] ax⟩
  · have noStep1 :
        ∀ {prem conc : Sequent L},
          GentzenStep1Ext prem conc →
          conc = Sequent.mk [] [FormulaN.eq_ hL t t] → False := by
      intro prem conc rule hconc
      cases rule <;> simp_all [List.append_eq_singleton_iff]
    have noStep2 :
        ∀ {prem1 prem2 conc : Sequent L},
          GentzenStep2Ext prem1 prem2 conc →
          conc = Sequent.mk [] [FormulaN.eq_ hL t t] → False := by
      intro prem1 prem2 conc rule hconc
      cases rule <;> simp_all [List.append_eq_singleton_iff]
    have noTree :
        ∀ {s : Sequent L},
          GProofTreeExt s →
          s = Sequent.mk [] [FormulaN.eq_ hL t t] → False := by
      intro s g
      cases g with
      | axiom_ s hax =>
          intro hs
          subst s
          simp [isAxiom] at hax
      | onePremise rule sub => exact noStep1 rule
      | twoPremise rule sub1 sub2 => exact noStep2 rule
    rintro ⟨g⟩
    exact noTree g rfl

-- ===================================================================
-- Lemma 6.3.2: conjRight_implLeft_permutation
-- ===================================================================

/-- Lemma 6.3.2: (i) Given a G=-proof tree T for a sequent
Gamma -> Delta, A /\ B, Lambda satisfying the conclusion of Lemma 6.3.1,
another G=-proof T' can be constructed with the same depth, where
the root rule is conjunction-right applied to A /\ B.
(ii) Similarly for implication-left applied to A implies B at an
arbitrary occurrence in the antecedent.

The transformation stays inside G= and commutes logical rules directly
through reflexivity, function congruence, predicate congruence, and
general equality-rule nodes. -/
@[blueprint "chap6__lemma_6_3_2" (main := true)]
theorem conjRight_implLeft_permutation {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L}
    (T : GEqProofTree hL s)
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    -- Part (i): conjunction-right permutation
    (∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)),
      s = Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ) →
      ∃ T' : GEqProofTree hL s,
        geqDepth T' = geqDepth T ∧
        rootIsConjRight T' A B Γ Δ Λ) ∧
    -- Part (ii): implication-left permutation
    (∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)),
      s = Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ →
      ∃ T' : GEqProofTree hL s,
        geqDepth T' = geqDepth T ∧
        rootIsImplLeft T' A B Γ Δ Λ) 

-- ===================================================================
-- Lemma 6.3.3 (required def): sequentHasConjImplTarget
-- ===================================================================

/-- Lemma 6.3.3 (required def): A sequent has a pending normalization
target when its succedent contains a conjunction or its antecedent
contains an implication. -/
@[blueprint "chap6__lemma_6_3_3"]
def sequentHasConjImplTarget {L : Language} (s : Sequent L) : Prop :=
  (∃ (A B : FormulaN L), FormulaN.conj A B ∈ s.succedent) ∨
  (∃ (A B : FormulaN L), FormulaN.impl A B ∈ s.antecedent)

-- ===================================================================
-- Lemma 6.3.3 (required def): gIsConjImplNormalized
-- ===================================================================

/-- Lemma 6.3.3 (required def): A G proof is in conjunction/implication
normal form when every non-leaf node with a pending target selects one
actual target occurrence using conjunction-right or implication-left.
The indexed rule constructor fixes the selected formula and its exact
prefix/suffix contexts.  All subtrees satisfy the same condition. -/
@[blueprint "chap6__lemma_6_3_3"]
def gIsConjImplNormalized {L : Language} :
    {s : Sequent L} → GProofTreeExt s → Prop
  | _, .axiom_ _ _ => True
  | s, .onePremise _ sub =>
    ¬ sequentHasConjImplTarget s ∧
    gIsConjImplNormalized sub
  | s, .twoPremise rule sub1 sub2 =>
    (match rule with
     | .conjRight _ _ _ _ _ => True
     | .implLeft _ _ _ _ _ => True
     | _ => ¬ sequentHasConjImplTarget s) ∧
    gIsConjImplNormalized sub1 ∧
    gIsConjImplNormalized sub2

-- ===================================================================
-- Lemma 6.3.3 (required def): geqIsConjImplNormalized
-- ===================================================================

/-- Lemma 6.3.3 (required def): The conjunction/implication progress
invariant for G=.  A pending target at a non-leaf node must be selected
by an indexed conjunction-right or implication-left constructor.
Equality rules and unrelated logical rules may occur only after the
node has no pending target, and the invariant holds recursively. -/
@[blueprint "chap6__lemma_6_3_3"]
def geqIsConjImplNormalized {L : Language}
    {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → Prop
  | _, .base g => gIsConjImplNormalized g
  | _, .axiom_ _ _ => True
  | s, .onePremise _ sub =>
    ¬ sequentHasConjImplTarget s ∧
    geqIsConjImplNormalized sub
  | s, .twoPremise rule sub1 sub2 =>
    (match rule with
     | .conjRight _ _ _ _ _ => True
     | .implLeft _ _ _ _ _ => True
     | _ => ¬ sequentHasConjImplTarget s) ∧
    geqIsConjImplNormalized sub1 ∧
    geqIsConjImplNormalized sub2
  | _, .eqRefl _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqFuncCong _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqPredCong _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqGeneral _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub

-- Both target kinds may occur at a node: the indexed implication-left
-- root selects one of them, and the axiom subtrees end the recursion.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B C D : FormulaN L) :
    let T : GEqProofTree hL
        (Sequent.mk
          ([A] ++ [FormulaN.impl A B] ++ [])
          [B, FormulaN.conj C D]) :=
      .twoPremise
        (.implLeft [A] [] [B, FormulaN.conj C D] A B)
        (.axiom_ _
          ⟨A, by simp, by simp⟩)
        (.axiom_ _
          ⟨B, by simp, by simp⟩)
    geqIsConjImplNormalized T := by
  simp [geqIsConjImplNormalized]

-- Two conjunction-right targets may occur at one node; selecting either
-- actual occurrence is progress and does not require one rule to target both.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B C D : FormulaN L) :
    let T : GEqProofTree hL
        (Sequent.mk [A, B]
          ([] ++ [FormulaN.conj A B] ++ [FormulaN.conj C D])) :=
      .twoPremise
        (.conjRight [A, B] [] [FormulaN.conj C D] A B)
        (.axiom_ _
          ⟨A, by simp, by simp⟩)
        (.axiom_ _
          ⟨B, by simp, by simp⟩)
    geqIsConjImplNormalized T := by
  simp [geqIsConjImplNormalized]

-- An unrelated logical root is rejected while a target remains.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B C X Y : FormulaN L) :
    let T : GEqProofTree hL
        (Sequent.mk
          ([] ++ [FormulaN.disj X Y] ++ [C])
          [C, FormulaN.conj A B]) :=
      .twoPremise
        (.disjLeft [] [C] [C, FormulaN.conj A B] X Y)
        (.axiom_ _
          ⟨C, by simp, by simp⟩)
        (.axiom_ _
          ⟨C, by simp, by simp⟩)
    ¬ geqIsConjImplNormalized T := by
  dsimp
  intro hnorm
  exact hnorm.1 (Or.inl ⟨A, B, by simp⟩)

-- An equality root is likewise rejected while a target remains.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (hL : L.hasEquality = true)
    (t : Term L) (A B : FormulaN L) :
    let E := FormulaN.eq_ hL t t
    let inner : GEqProofTree hL
        (Sequent.mk [A, B, E] [FormulaN.conj A B]) :=
      .twoPremise
        (.conjRight [A, B, E] [] [] A B)
        (.axiom_ _
          ⟨A, by simp, by simp⟩)
        (.axiom_ _
          ⟨B, by simp, by simp⟩)
    let T : GEqProofTree hL
        (Sequent.mk [A, B] [FormulaN.conj A B]) :=
      .eqRefl t [A, B] [FormulaN.conj A B] inner
    ¬ geqIsConjImplNormalized T := by
  simp [geqIsConjImplNormalized, sequentHasConjImplTarget]

-- Leaves have no applied rule, so an axiom is normalized even when its
-- sequent contains a target formula.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L) :
    let C := FormulaN.conj A B
    let T : GEqProofTree hL (Sequent.mk [C] [C]) :=
      .axiom_ _ ⟨C, by simp, by simp⟩
    geqIsConjImplNormalized T := by
  simp [geqIsConjImplNormalized]

end LCS.CutElim.LKe.Equivalence
end

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
section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T →
      seqAllAtomicOrQuantified s') → ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' =
      geqDepth T)
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqNormalize_target
    (s : Sequent L) (T : GEqProofTree hL s) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents T →
      seqAllAtomicOrQuantified s') (htarget : sequentHasConjImplTarget s) (hdepth : geqDepth T = n)
    : ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' = geqDepth T := by
  classical
  rcases s with ⟨Γ, succ⟩
  change (∃ A B : FormulaN L, FormulaN.conj A B ∈ succ) ∨
    (∃ A B : FormulaN L, FormulaN.impl A B ∈ Γ) at htarget
  rcases htarget with
    ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · obtain ⟨Δ, Λ, hsucc⟩ := perm_mem_split (FormulaN.conj A B) succ hAB
    subst succ
    obtain ⟨p1, p2, hpdepth, hp1leaf, hp2leaf⟩ := geqPermute_conjRight_withLeaves A B Γ Δ Λ T hleaf
    have hp1depth : geqDepth p1 < n := by omega
    have hp2depth : geqDepth p2 < n := by omega
    obtain ⟨q1, hq1norm, hq1depth⟩ := ih (geqDepth p1) hp1depth p1 rfl hp1leaf
    obtain ⟨q2, hq2norm, hq2depth⟩ := ih (geqDepth p2) hp2depth p2 rfl hp2leaf
    let p : GEqProofTree hL (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ)) := .twoPremise
        (.conjRight Γ Δ Λ A B) q1 q2
    refine ⟨p, ?_, ?_⟩
    · exact ⟨trivial, hq1norm, hq2norm⟩
    · simp only [p, geqDepth]
      omega
  · obtain ⟨Γ₁, Γ₂, hΓ⟩ := perm_mem_split (FormulaN.impl A B) Γ hAB
    subst Γ
    obtain ⟨p1, p2, hpdepth, hp1leaf, hp2leaf⟩ := geqPermute_implLeft_withLeaves A B Γ₁ Γ₂ succ T hleaf
    obtain ⟨p1, hp1perm, hp1leaf⟩ := geqPermuteContexts p1 (Γ₁ ++ Γ₂) ([A] ++ succ)
        (List.Perm.refl _) (by exact List.perm_append_comm) hp1leaf
    have hp1depth : geqDepth p1 < n := by omega
    have hp2depth : geqDepth p2 < n := by omega
    obtain ⟨q1, hq1norm, hq1depth⟩ := ih (geqDepth p1) hp1depth p1 rfl hp1leaf
    obtain ⟨q2, hq2norm, hq2depth⟩ := ih (geqDepth p2) hp2depth p2 rfl hp2leaf
    let p : GEqProofTree hL (Sequent.mk (Γ₁ ++ [FormulaN.impl A B] ++ Γ₂) succ) := .twoPremise
        (.implLeft Γ₁ Γ₂ succ A B) q1 q2
    refine ⟨p, ?_, ?_⟩
    · exact ⟨trivial, hq1norm, hq2norm⟩
    · simp only [p, geqDepth]
      omega

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqNormalize_other
    (s : Sequent L) (T : GEqProofTree hL s) (hdepth : geqDepth T = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents T → seqAllAtomicOrQuantified s') (normOne : ∀ {prem conc : Sequent L} (rule :
      GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub → seqAllAtomicOrQuantified s') → ¬sequentHasConjImplTarget conc → ∃ (p :
      GEqProofTree hL conc), geqIsConjImplNormalized p ∧ geqDepth p = 1 + geqDepth sub) (normTwo : ∀ {prem1
      prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 :
      GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') → ¬sequentHasConjImplTarget conc → ∃ (p : GEqProofTree hL conc),
      geqIsConjImplNormalized p ∧ geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2)) (htarget :
      ¬sequentHasConjImplTarget s)
    : ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' = geqDepth T := by
  classical
  cases T with
  | base g =>
    cases g with
    | axiom_ s hAx =>
      exact ⟨.base (.axiom_ s hAx), trivial, rfl⟩
    | onePremise rule sub =>
      simpa only [geqDepth, gProofTreeDepth] using normOne rule (.base sub) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          simpa [geqLeafSequents, gProofTreeLeafSequents] using hleaf) htarget
    | twoPremise rule sub1 sub2 =>
      simpa only [geqDepth, gProofTreeDepth] using normTwo rule (.base sub1) (.base sub2) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inl hs')) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inr hs')) htarget
  | axiom_ s hAx =>
    exact ⟨.axiom_ s hAx, trivial, rfl⟩
  | onePremise rule sub =>
    simpa only [geqDepth] using normOne rule sub (by
        simp only [geqDepth] at hdepth
        omega) (by
        simpa [geqLeafSequents] using hleaf) htarget
  | twoPremise rule sub1 sub2 =>
    simpa only [geqDepth] using normTwo rule sub1 sub2 (by
        simp only [geqDepth] at hdepth
        omega) (by
        simp only [geqDepth] at hdepth
        omega) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inl hs')) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inr hs')) htarget
  | eqRefl t Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqRefl t Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqFuncCong f ss ts Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqFuncCong f ss ts Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqPredCong P ss ts Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqPredCong P ss ts Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqGeneral axioms hne haxioms Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqGeneral axioms hne haxioms Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega

end
end LCS.CutElim.LKe.Equivalence
end

