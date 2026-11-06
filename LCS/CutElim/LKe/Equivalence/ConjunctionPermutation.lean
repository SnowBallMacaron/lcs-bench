import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation.PropositionalCases

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
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ
      ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_allLeft
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (ts : List (Term L)) (Γr Δr succ : List (FormulaN L)) (x :
      Nat) (X : FormulaN L) (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub :
      GEqProofTree hL (Sequent.mk (Γr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++
      [FormulaN.all x X] ++ Δr) (succ))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [FormulaN.all x X] ++ Δr)
      (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δr) Δ Λ rfl hsubleaf
  refine ⟨.onePremise (.allLeft ts Γr Δr (Δ ++ [A] ++ Λ) x X hne hfree) q1, .onePremise
      (.allLeft ts Γr Δr (Δ ++ [B] ++ Λ) x X hne hfree) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_allRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (replaceConjFresh : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X :
      FormulaN L), formulaFVN X ⊆ formulaFVN C → (∀ (F : FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈
      formulaFVN F) → ∀ (F : FormulaN L), F ∈ ant ++ (D ++ [X] ++ S) → ¬y ∈ formulaFVN F) (geqDepth_transport
      : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p)
      (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
      (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F : FormulaN L), F ∈
      (Γr) ++ (Δr ++ [FormulaN.all x X] ++ Λr) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x X)
      (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [formulaSubstN X (Term.var y) x] ++ Λr))) (hsubdepth :
      geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr) (Δr ++ [FormulaN.all x X] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++
      Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  have hfreshTarget : ∀ F ∈ Γr ++ (Δ ++ [FormulaN.conj A B] ++ Λ), y ∉ Variables.formulaFVN F := by
    intro F hF
    apply hfresh F
    simpa [hsuc] using hF
  have hfreshTarget1 : ∀ F ∈ Γr ++ (Δ ++ [A] ++ Λ), y ∉ Variables.formulaFVN F :=
    replaceConjFresh y Γr Δ Λ (FormulaN.conj A B) A (fun v hv => Or.inl hv) hfreshTarget
  have hfreshTarget2 : ∀ F ∈ Γr ++ (Δ ++ [B] ++ Λ), y ∉ Variables.formulaFVN F :=
    replaceConjFresh y Γr Δ Λ (FormulaN.conj A B) B (fun v hv => Or.inr hv) hfreshTarget
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ K)
        Λ (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ K) ++ [A] ++ Λ) =
          Sequent.mk Γr (Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ K) ++ [B] ++ Λ) =
          Sequent.mk Γr (Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    have hfresh1 : ∀ F ∈ (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ))).antecedent ++
            (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ))).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget1
    have hfresh2 : ∀ F ∈ (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ))).antecedent ++
            (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ))).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr Δr
        (K ++ [A] ++ Λ) x X hfresh1 hfreeFor) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr Δr
        (K ++ [B] ++ Λ) x X hfresh2 hfreeFor) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.all x X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.all x X] ++ K) ++ [B] ++ Λ) := by
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
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    have hfresh1 : ∀ F ∈ (Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr)).antecedent ++
            (Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr)).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget1
    have hfresh2 : ∀ F ∈ (Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr)).antecedent ++
            (Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr)).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr
        (Δ ++ [A] ++ K) Λr x X hfresh1 hfreeFor) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr
        (Δ ++ [B] ++ K) Λr x X hfresh2 hfreeFor) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.all x X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.all x X] ++ Λr)) := by
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
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_exLeft
    (replaceConjFresh : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X : FormulaN L), formulaFVN X ⊆
      formulaFVN C → (∀ (F : FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN
      L), F ∈ ant ++ (D ++ [X] ++ S) → ¬y ∈ formulaFVN F) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (y :
      Nat) (Γr Δr succ : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F : FormulaN L), F ∈ (Γr
      ++ [FormulaN.ex x X] ++ Δr) ++ (succ) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x X) (sub
      : GEqProofTree hL (Sequent.mk (Γr ++ [formulaSubstN X (Term.var y) x] ++ Δr) (succ))) (hsubdepth :
      geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++
      Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++
        [Substitution.formulaSubstN X (Term.var y) x] ++ Δr)
      Δ Λ rfl hsubleaf
  have hfresh1 : ∀ F ∈ (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (Δ ++ [A] ++ Λ)).antecedent ++ (Sequent.mk
            (Γr ++ [FormulaN.ex x X] ++ Δr)
            (Δ ++ [A] ++ Λ)).succedent,
        y ∉ Variables.formulaFVN F := by
    exact replaceConjFresh y (Γr ++ [FormulaN.ex x X] ++ Δr) Δ Λ (FormulaN.conj A B) A
      (fun v hv => Or.inl hv) hfresh
  have hfresh2 : ∀ F ∈ (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (Δ ++ [B] ++ Λ)).antecedent ++ (Sequent.mk
            (Γr ++ [FormulaN.ex x X] ++ Δr)
            (Δ ++ [B] ++ Λ)).succedent,
        y ∉ Variables.formulaFVN F := by
    exact replaceConjFresh y (Γr ++ [FormulaN.ex x X] ++ Δr) Δ Λ (FormulaN.conj A B) B
      (fun v hv => Or.inr hv) hfresh
  refine ⟨.onePremise (.exLeft y Γr Δr (Δ ++ [A] ++ Λ) x X hfresh1 hfreeFor) q1, .onePremise
      (.exLeft y Γr Δr (Δ ++ [B] ++ Λ) x X hfresh2 hfreeFor) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_exRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (ts : List (Term L)) (Γr Δr
      Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts →
      isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ List.map (fun (t : Term L) =>
      formulaSubstN X t x) ts ++ [FormulaN.ex x X] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr ++
      [FormulaN.ex x X] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
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
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++
          ts.map (fun t => Substitution.formulaSubstN X t x) ++
          [FormulaN.ex x X] ++ K)
        Λ (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ K) ++ [A] ++ Λ) =
          Sequent.mk Γr (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ K) ++ [B] ++ Λ) =
          Sequent.mk Γr (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr Δr (K ++ [A] ++ Λ) x X hne hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr Δr (K ++ [B] ++ Λ) x X hne hfree) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.ex x X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.ex x X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.ex x X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.ex x X] ++ K) ++ [B] ++ Λ) := by
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
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++
          ts.map (fun t => Substitution.formulaSubstN X t x) ++
          [FormulaN.ex x X] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
                [FormulaN.ex x X] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [A] ++ K) ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
                [FormulaN.ex x X] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [B] ++ K) ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr (Δ ++ [A] ++ K) Λr x X hne hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr (Δ ++ [B] ++ K) Λr x X hne hfree) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.ex x X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [A] ++ (K ++ [FormulaN.ex x X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.ex x X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [B] ++ (K ++ [FormulaN.ex x X] ++ Λr)) := by
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
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

private theorem geqConjRight_permOne
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (replaceConjFresh : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X :
      FormulaN L), formulaFVN X ⊆ formulaFVN C → (∀ (F : FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈
      formulaFVN F) → ∀ (F : FormulaN L), F ∈ ant ++ (D ++ [X] ++ S) → ¬y ∈ formulaFVN F) (geqDepth_transport
      : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p)
      (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    : ∀ {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub
      < n → conc = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 :
      GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth
      sub ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  intro prem conc rule sub hsubdepth hconc hsubleaf
  cases rule with
  | conjLeft Γr Δr succ X Y =>
    exact geqConjRight_conjLeft L hL n ih A B Γ Δ Λ Γr Δr succ X Y sub hsubdepth hsubleaf hconc
  | disjRight Γr Δr Λr X Y =>
    exact geqConjRight_disjRight L hL n ih markedSplit geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr Λr X Y sub hsubdepth hsubleaf hconc
  | implRight Γr Δr Λr X Y =>
    exact geqConjRight_implRight L hL n ih markedSplit geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr Λr X Y sub hsubdepth hsubleaf hconc
  | negLeft Γr Δr succ X =>
    exact geqConjRight_negLeft L hL n ih geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr succ X sub hsubdepth hsubleaf hconc
  | negRight Γr Δr Λr X =>
    exact geqConjRight_negRight L hL n ih markedSplit geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr Λr X sub hsubdepth hsubleaf hconc
  | allLeft ts Γr Δr succ x X hne hfree =>
    exact geqConjRight_allLeft L hL n ih A B Γ Δ Λ ts Γr Δr succ x X hne hfree sub hsubdepth hsubleaf hconc
  | allRight y Γr Δr Λr x X hfresh hfreeFor =>
    exact geqConjRight_allRight L hL n ih markedSplit replaceConjFresh geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ y Γr Δr Λr x X hfresh hfreeFor sub hsubdepth hsubleaf hconc
  | exLeft y Γr Δr succ x X hfresh hfreeFor =>
    exact geqConjRight_exLeft L hL n ih replaceConjFresh A B Γ Δ Λ y Γr Δr succ x X hfresh hfreeFor sub hsubdepth hsubleaf hconc
  | exRight ts Γr Δr Λr x X hne hfree =>
    exact geqConjRight_exRight L hL n ih markedSplit geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ ts Γr Δr Λr x X hne hfree sub hsubdepth hsubleaf hconc

private theorem geqConjRight_conjRight
    (markedSplit3 : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → (∃ (K
      : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧ X = Y ∧ Q = S ∨ ∃ (K : List
      (FormulaN L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁
      s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L)
      (sub1 : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X] ++ Λr))) (hsub1depth : geqDepth sub1 < n) (hsub1leaf
      : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') (sub2 : GEqProofTree hL
      (Sequent.mk (Γr) (Δr ++ [Y] ++ Λr))) (hsub2depth : geqDepth sub2 < n) (hsub2leaf : ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr ++ [X.conj Y] ++
      Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit3 hsuc with
    ⟨K, hΔ, hΛr⟩ |
    ⟨hΔr, hXY, hΛr⟩ |
    ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B Γr (Δr ++ [X] ++ K) Λ
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B Γr (Δr ++ [Y] ++ K) Λ
        (by simp [List.append_assoc]) hsub2leaf
    have ha1eq : Sequent.mk Γr ((Δr ++ [X] ++ K) ++ [A] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hb1eq : Sequent.mk Γr ((Δr ++ [X] ++ K) ++ [B] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    have ha2eq : Sequent.mk Γr ((Δr ++ [Y] ++ K) ++ [A] ++ Λ) = Sequent.mk Γr
            (Δr ++ [Y] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hb2eq : Sequent.mk Γr ((Δr ++ [Y] ++ K) ++ [B] ++ Λ) = Sequent.mk Γr
            (Δr ++ [Y] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let a1' := ha1eq ▸ a1
    let b1' := hb1eq ▸ b1
    let a2' := ha2eq ▸ a2
    let b2' := hb2eq ▸ b2
    have hda1 : geqDepth a1' = geqDepth a1 := geqDepth_transport ha1eq a1
    have hdb1 : geqDepth b1' = geqDepth b1 := geqDepth_transport hb1eq b1
    have hda2 : geqDepth a2' = geqDepth a2 := geqDepth_transport ha2eq a2
    have hdb2 : geqDepth b2' = geqDepth b2 := geqDepth_transport hb2eq b2
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight Γr Δr (K ++ [A] ++ Λ) X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight Γr Δr (K ++ [B] ++ Λ) X Y) b1' b2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.conj X Y] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.conj X Y] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.conj X Y] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.conj X Y] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · apply geqLeafProperty_transport hout1 r1
      intro s' hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (geqLeafProperty_transport ha1eq a1 ha1leaf s')
        (geqLeafProperty_transport ha2eq a2 ha2leaf s')
    · apply geqLeafProperty_transport hout2 r2
      intro s' hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (geqLeafProperty_transport hb1eq b1 hb1leaf s')
        (geqLeafProperty_transport hb2eq b2 hb2leaf s')
  · subst Δr
    subst Λr
    injection hXY with hX hY
    subst X
    subst Y
    exact ⟨sub1, sub2, rfl, hsub1leaf, hsub2leaf⟩
  · subst Δr
    subst Λ
    obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B Γr Δ (K ++ [X] ++ Λr)
        (by simp [List.append_assoc]) hsub1leaf
    obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B Γr Δ (K ++ [Y] ++ Λr)
        (by simp [List.append_assoc]) hsub2leaf
    have ha1eq : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [X] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [A] ++ K) ++ [X] ++ Λr) := by
      simp [List.append_assoc]
    have hb1eq : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [X] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [B] ++ K) ++ [X] ++ Λr) := by
      simp [List.append_assoc]
    have ha2eq : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [A] ++ K) ++ [Y] ++ Λr) := by
      simp [List.append_assoc]
    have hb2eq : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [B] ++ K) ++ [Y] ++ Λr) := by
      simp [List.append_assoc]
    let a1' := ha1eq ▸ a1
    let b1' := hb1eq ▸ b1
    let a2' := ha2eq ▸ a2
    let b2' := hb2eq ▸ b2
    have hda1 : geqDepth a1' = geqDepth a1 := geqDepth_transport ha1eq a1
    have hdb1 : geqDepth b1' = geqDepth b1 := geqDepth_transport hb1eq b1
    have hda2 : geqDepth a2' = geqDepth a2 := geqDepth_transport ha2eq a2
    have hdb2 : geqDepth b2' = geqDepth b2 := geqDepth_transport hb2eq b2
    let r1 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight Γr (Δ ++ [A] ++ K) Λr X Y) a1' a2'
    let r2 := GEqProofTree.twoPremise (GentzenStep2Ext.conjRight Γr (Δ ++ [B] ++ K) Λr X Y) b1' b2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.conj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.conj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.conj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.conj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · apply geqLeafProperty_transport hout1 r1
      intro s' hs'
      simp only [r1, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (geqLeafProperty_transport ha1eq a1 ha1leaf s')
        (geqLeafProperty_transport ha2eq a2 ha2leaf s')
    · apply geqLeafProperty_transport hout2 r2
      intro s' hs'
      simp only [r2, geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (geqLeafProperty_transport hb1eq b1 hb1leaf s')
        (geqLeafProperty_transport hb2eq b2 hb2leaf s')

private theorem geqConjRight_disjLeft
    (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List (FormulaN L)) (X Y : FormulaN L) (sub1 : GEqProofTree hL
      (Sequent.mk (Γr ++ [X] ++ Δr) (succ))) (hsub1depth : geqDepth sub1 < n) (hsub1leaf : ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') (sub2 : GEqProofTree hL (Sequent.mk (Γr ++ [Y]
      ++ Δr) (succ))) (hsub2depth : geqDepth sub2 < n) (hsub2leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub2 → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.disj Y] ++ Δr) (succ)) = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B
      (Γr ++ [X] ++ Δr) Δ Λ rfl hsub1leaf
  obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B
      (Γr ++ [Y] ++ Δr) Δ Λ rfl hsub2leaf
  let p1 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft Γr Δr (Δ ++ [A] ++ Λ) X Y) a1 a2
  let p2 := GEqProofTree.twoPremise (GentzenStep2Ext.disjLeft Γr Δr (Δ ++ [B] ++ Λ) X Y) b1 b2
  have hdp1 : geqDepth p1 = 1 + max (geqDepth a1) (geqDepth a2) := rfl
  have hdp2 : geqDepth p2 = 1 + max (geqDepth b1) (geqDepth b2) := rfl
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    simp only [p1, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (ha1leaf s') (ha2leaf s')
  · intro s' hs'
    simp only [p2, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (hb1leaf s') (hb2leaf s')

private theorem geqConjRight_implLeft
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List
      (FormulaN L)) (X Y : FormulaN L) (sub1 : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X] ++ succ)))
      (hsub1depth : geqDepth sub1 < n) (hsub1leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 →
      seqAllAtomicOrQuantified s') (sub2 : GEqProofTree hL (Sequent.mk ([Y] ++ Γr ++ Δr) (succ))) (hsub2depth
      : geqDepth sub2 < n) (hsub2leaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.impl Y] ++ Δr) (succ)) = (Sequent.mk (Γ) (Δ
      ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨a1, b1, hq1, ha1leaf, hb1leaf⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl A B (Γr ++ Δr) ([X] ++ Δ) Λ
      (by simp [List.append_assoc]) hsub1leaf
  obtain ⟨a2, b2, hq2, ha2leaf, hb2leaf⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl A B
      ([Y] ++ Γr ++ Δr) Δ Λ rfl hsub2leaf
  have ha1eq : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [A] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [A] ++ Λ)) := by
    simp [List.append_assoc]
  have hb1eq : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [B] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [B] ++ Λ)) := by
    simp [List.append_assoc]
  let a1' := ha1eq ▸ a1
  let b1' := hb1eq ▸ b1
  have hda1 : geqDepth a1' = geqDepth a1 := geqDepth_transport ha1eq a1
  have hdb1 : geqDepth b1' = geqDepth b1 := geqDepth_transport hb1eq b1
  let p1 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft Γr Δr (Δ ++ [A] ++ Λ) X Y) a1' a2
  let p2 := GEqProofTree.twoPremise (GentzenStep2Ext.implLeft Γr Δr (Δ ++ [B] ++ Λ) X Y) b1' b2
  have hdp1 : geqDepth p1 = 1 + max (geqDepth a1') (geqDepth a2) := rfl
  have hdp2 : geqDepth p2 = 1 + max (geqDepth b1') (geqDepth b2) := rfl
  refine ⟨p1, p2, by omega, ?_, ?_⟩
  · intro s' hs'
    simp only [p1, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (geqLeafProperty_transport ha1eq a1 ha1leaf s') (ha2leaf s')
  · intro s' hs'
    simp only [p2, geqLeafSequents, List.mem_append] at hs'
    exact hs'.elim (geqLeafProperty_transport hb1eq b1 hb1leaf s') (hb2leaf s')

private theorem geqConjRight_permTwo
    (markedSplit3 : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → (∃ (K
      : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧ X = Y ∧ Q = S ∨ ∃ (K : List
      (FormulaN L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq :
      s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁
      s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL
      prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc = (Sequent.mk (Γ) (Δ
      ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') →
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL
      (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max
      (geqDepth p1) (geqDepth p2) = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  intro prem1 prem2 conc rule sub1 sub2 hsub1depth hsub2depth hconc hsub1leaf hsub2leaf
  cases rule with
  | conjRight Γr Δr Λr X Y =>
    exact geqConjRight_conjRight L hL n ih markedSplit3 geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr Λr X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc
  | disjLeft Γr Δr succ X Y =>
    exact geqConjRight_disjLeft L hL n ih A B Γ Δ Λ Γr Δr succ X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc
  | implLeft Γr Δr succ X Y =>
    exact geqConjRight_implLeft L hL n ih geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ Γr Δr succ X Y sub1 hsub1depth hsub1leaf sub2 hsub2depth hsub2leaf hconc

private theorem geqConjRight_eqRefl
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (t : Term L) (Γe succ : List (FormulaN L)) (sub :
      GEqProofTree hL (Sequent.mk (Γe ++ [FormulaN.eq_ hL t t]) (succ))) (hseq : (Sequent.mk (Γe) (succ)) =
      (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (hdepth : geqDepth (GEqProofTree.eqRefl t Γe succ sub) = n)
      (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqRefl t Γe succ sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqRefl t Γe succ sub) ∧ (∀ (s'
      : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γ
  subst succ
  have hsubdepth : geqDepth sub < n := by
    simp only [geqDepth] at hdepth
    omega
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γe ++ [FormulaN.eq_ hL t t]) Δ Λ rfl (by
        simpa [geqLeafSequents] using hleaf)
  let p1 := GEqProofTree.eqRefl t Γe (Δ ++ [A] ++ Λ) q1
  let p2 := GEqProofTree.eqRefl t Γe (Δ ++ [B] ++ Λ) q2
  have hdp1 : geqDepth p1 = 1 + geqDepth q1 := rfl
  have hdp2 : geqDepth p2 = 1 + geqDepth q2 := rfl
  refine ⟨p1, p2, by
    simp only [p1, p2, geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1leaf
  · simpa [p2, geqLeafSequents] using hq2leaf

private theorem geqConjRight_eqFuncCong
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
      (Γe succ : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γe ++ [eqCongruenceImplFunc L hL f ss
      ts]) (succ))) (hseq : (Sequent.mk (Γe) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (hdepth :
      geqDepth (GEqProofTree.eqFuncCong f ss ts Γe succ sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.eqFuncCong f ss ts Γe succ sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqFuncCong f ss ts Γe succ
      sub) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γ
  subst succ
  have hsubdepth : geqDepth sub < n := by
    simp only [geqDepth] at hdepth
    omega
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γe ++ [eqCongruenceImplFunc L hL f ss ts])
      Δ Λ rfl (by simpa [geqLeafSequents] using hleaf)
  let p1 := GEqProofTree.eqFuncCong f ss ts Γe (Δ ++ [A] ++ Λ) q1
  let p2 := GEqProofTree.eqFuncCong f ss ts Γe (Δ ++ [B] ++ Λ) q2
  have hdp1 : geqDepth p1 = 1 + geqDepth q1 := rfl
  have hdp2 : geqDepth p2 = 1 + geqDepth q2 := rfl
  refine ⟨p1, p2, by
    simp only [p1, p2, geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1leaf
  · simpa [p2, geqLeafSequents] using hq2leaf

private theorem geqConjRight_eqPredCong
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (P : L.predSymbols) (ss ts : Fin
      (L.predArity P) → Term L) (Γe succ : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γe ++
      [eqCongruenceImplPred L hL P ss ts]) (succ))) (hseq : (Sequent.mk (Γe) (succ)) = (Sequent.mk (Γ) (Δ ++
      [A.conj B] ++ Λ))) (hdepth : geqDepth (GEqProofTree.eqPredCong P ss ts Γe succ sub) = n) (hleaf : ∀
      (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqPredCong P ss ts Γe succ sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqPredCong P ss ts Γe succ
      sub) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γ
  subst succ
  have hsubdepth : geqDepth sub < n := by
    simp only [geqDepth] at hdepth
    omega
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γe ++ [eqCongruenceImplPred L hL P ss ts])
      Δ Λ rfl (by simpa [geqLeafSequents] using hleaf)
  let p1 := GEqProofTree.eqPredCong P ss ts Γe (Δ ++ [A] ++ Λ) q1
  let p2 := GEqProofTree.eqPredCong P ss ts Γe (Δ ++ [B] ++ Λ) q2
  have hdp1 : geqDepth p1 = 1 + geqDepth q1 := rfl
  have hdp2 : geqDepth p2 = 1 + geqDepth q2 := rfl
  refine ⟨p1, p2, by
    simp only [p1, p2, geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1leaf
  · simpa [p2, geqLeafSequents] using hq2leaf

private theorem geqConjRight_eqGeneral
    (A B : FormulaN L) (Γ Δ Λ axioms : List (FormulaN L)) (hne : axioms ≠ []) (haxioms : ∀ (A : FormulaN L), A
      ∈ axioms → isEqAxiomInstance hL A) (ant succ : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk
      (ant ++ axioms) (succ))) (hseq : (Sequent.mk (ant) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
      (hdepth : geqDepth (GEqProofTree.eqGeneral axioms hne haxioms ant succ sub) = n) (hleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqGeneral axioms hne haxioms ant succ sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.eqGeneral axioms hne haxioms
      ant succ sub) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  injection hseq with hant hsuc
  subst Γ
  subst succ
  have hsubdepth : geqDepth sub < n := by
    simp only [geqDepth] at hdepth
    omega
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (ant ++ axioms) Δ Λ rfl (by
        simpa [geqLeafSequents] using hleaf)
  let p1 := GEqProofTree.eqGeneral axioms hne haxioms ant (Δ ++ [A] ++ Λ) q1
  let p2 := GEqProofTree.eqGeneral axioms hne haxioms ant (Δ ++ [B] ++ Λ) q2
  have hdp1 : geqDepth p1 = 1 + geqDepth q1 := rfl
  have hdp2 : geqDepth p2 = 1 + geqDepth q2 := rfl
  refine ⟨p1, p2, by
    simp only [p1, p2, geqDepth]
    omega, ?_, ?_⟩
  · simpa [p1, geqLeafSequents] using hq1leaf
  · simpa [p2, geqLeafSequents] using hq2leaf

end

/-- Helper for Lemma 6.3.2: directly commute conjunction-right to the
root of a G=-proof whose selected occurrence of `A ∧ B` has arbitrary
succedent prefix and suffix contexts.  The returned trees are indexed
by the two exact premises of `GentzenStep2Ext.conjRight`; equality-rule
constructors remain available throughout the transformation.
This strengthened companion also returns the leaf invariant needed by
the direct G= normalizer to recurse through the two premises. -/
theorem geqPermute_conjRight_withLeaves {L : Language}
    {hL : L.hasEquality = true}
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    (T : GEqProofTree hL
      (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ)))
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ (p1 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [A] ++ Λ)))
      (p2 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [B] ++ Λ))),
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
    exact geqConjRight_markedSplit L
  have markedSplit3 :
      ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L},
        P ++ [X] ++ Q = R ++ [Y] ++ S →
        (∃ K, R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨
        (P = R ∧ X = Y ∧ Q = S) ∨
        (∃ K, P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q) := by
    exact geqConjRight_markedSplit3 L
  have replaceConjFresh :
      ∀ (y : Nat) (ant D S : List (FormulaN L))
        (C X : FormulaN L),
        (Variables.formulaFVN X ⊆ Variables.formulaFVN C) →
        (∀ F ∈ ant ++ (D ++ [C] ++ S), y ∉ Variables.formulaFVN F) →
        ∀ F ∈ ant ++ (D ++ [X] ++ S), y ∉ Variables.formulaFVN F := by
    exact geqConjRight_replaceConjFresh L
  have geqDepth_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
        (p : GEqProofTree hL s₁),
        geqDepth (heq ▸ p) = geqDepth p := by
    exact geqConjRight_geqDepth_transport L hL
  have geqLeaf_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
        (p : GEqProofTree hL s₁),
        geqLeafSequents (heq ▸ p) = geqLeafSequents p := by
    exact geqConjRight_geqLeaf_transport L hL
  have geqLeafProperty_transport :
      ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
        (p : GEqProofTree hL s₁),
        (∀ s' ∈ geqLeafSequents p,
          seqAllAtomicOrQuantified s') →
        ∀ s' ∈ geqLeafSequents (heq ▸ p),
          seqAllAtomicOrQuantified s' := by
    exact geqConjRight_geqLeafProperty_transport L hL geqLeaf_transport
  suffices h :
      ∀ n : Nat, ∀ {s : Sequent L} (T : GEqProofTree hL s),
        geqDepth T = n →
        ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)),
        s = Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ) →
        (∀ s' ∈ geqLeafSequents T,
          seqAllAtomicOrQuantified s') →
        ∃ (p1 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [A] ++ Λ)))
          (p2 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [B] ++ Λ))),
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
          conc = Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ) →
          (∀ s' ∈ geqLeafSequents sub,
            seqAllAtomicOrQuantified s') →
          ∃ (p1 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [A] ++ Λ)))
            (p2 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [B] ++ Λ))),
            1 + max (geqDepth p1) (geqDepth p2) =
              1 + geqDepth sub ∧
            (∀ s' ∈ geqLeafSequents p1,
              seqAllAtomicOrQuantified s') ∧
            (∀ s' ∈ geqLeafSequents p2,
              seqAllAtomicOrQuantified s') := by
      exact geqConjRight_permOne L hL n ih markedSplit replaceConjFresh geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ
    have permTwo :
        ∀ {prem1 prem2 conc : Sequent L}
          (rule : GentzenStep2Ext prem1 prem2 conc)
          (sub1 : GEqProofTree hL prem1)
          (sub2 : GEqProofTree hL prem2),
          geqDepth sub1 < n →
          geqDepth sub2 < n →
          conc = Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ) →
          (∀ s' ∈ geqLeafSequents sub1,
            seqAllAtomicOrQuantified s') →
          (∀ s' ∈ geqLeafSequents sub2,
            seqAllAtomicOrQuantified s') →
          ∃ (p1 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [A] ++ Λ)))
            (p2 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [B] ++ Λ))),
            1 + max (geqDepth p1) (geqDepth p2) =
              1 + max (geqDepth sub1) (geqDepth sub2) ∧
            (∀ s' ∈ geqLeafSequents p1,
              seqAllAtomicOrQuantified s') ∧
            (∀ s' ∈ geqLeafSequents p2,
              seqAllAtomicOrQuantified s') := by
      exact geqConjRight_permTwo L hL n ih markedSplit3 geqDepth_transport geqLeafProperty_transport A B Γ Δ Λ
    cases T with
    | base g =>
      exact geqConjRight_base L hL n s A B _ _ _ hseq permOne permTwo g hdepth hleaf
    | axiom_ s hAx =>
      exact geqConjRight_axiom_ L hL s A B _ _ _ hseq _ hleaf
    | onePremise rule sub =>
      exact geqConjRight_onePremise L hL n _ _ _ _ _ _ hseq permOne _ sub rule hdepth hleaf
    | twoPremise rule sub1 sub2 =>
      exact geqConjRight_twoPremise L hL n _ _ _ _ _ _ hseq permTwo _ _ sub1 sub2 rule hdepth hleaf
    | eqRefl t Γe succ sub =>
      exact geqConjRight_eqRefl L hL n ih A B Γ Δ Λ t Γe succ sub hseq hdepth hleaf
    | eqFuncCong f ss ts Γe succ sub =>
      exact geqConjRight_eqFuncCong L hL n ih A B Γ Δ Λ f ss ts Γe succ sub hseq hdepth hleaf
    | eqPredCong P ss ts Γe succ sub =>
      exact geqConjRight_eqPredCong L hL n ih A B Γ Δ Λ P ss ts Γe succ sub hseq hdepth hleaf
    | eqGeneral axioms hne haxioms ant succ sub =>
      exact geqConjRight_eqGeneral L hL n ih A B Γ Δ Λ axioms hne haxioms ant succ sub hseq hdepth hleaf

/-- Public depth-only projection of the leaf-preserving direct
conjunction-right commuting construction. -/
theorem geqPermute_conjRight {L : Language}
    {hL : L.hasEquality = true}
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    (T : GEqProofTree hL
      (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ)))
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ (p1 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [A] ++ Λ)))
      (p2 : GEqProofTree hL (Sequent.mk Γ (Δ ++ [B] ++ Λ))),
      1 + max (geqDepth p1) (geqDepth p2) = geqDepth T := by
  obtain ⟨p1, p2, hdepth, _, _⟩ :=
    geqPermute_conjRight_withLeaves A B Γ Δ Λ T hleaf
  exact ⟨p1, p2, hdepth⟩

end LCS.CutElim.LKe.Equivalence
end
