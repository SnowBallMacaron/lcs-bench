import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.ProofSubstitution.Basic
import Attach
import LCS.CutElim.Interpolation.ProofSubstitution.Variable.ProofsStamp

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
section
variable (L : Language) (z y : Nat)

theorem folkVar_termSubstVarEqOfNotFree

    : ∀ (t : Term L), ¬y ∈ termFV t → termSubst t (Term.var z) y = t := by
  intro t h
  induction t with
  | var w =>
    simp only [termSubst]
    split
    · rename_i heq
      exact absurd (heq ▸ rfl : y ∈ termFV (Term.var y)) (heq ▸ h)
    · rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (fun hmem => h ⟨i, hmem⟩)

theorem folkVar_formulaSubstVarEqOfNotFree
    (termSubstVarEqOfNotFree : ∀ (t : Term L), ¬y ∈ termFV t → termSubst t (Term.var z) y = t)
    : ∀ (F : FormulaN L), ¬y ∈ formulaFVN F → formulaSubstN F (Term.var z) y = F := by
  intro F h
  induction F with
  | predN P ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i
    exact termSubstVarEqOfNotFree (ts i) (fun hmem => h ⟨i, hmem⟩)
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstN, FormulaN.eq_.injEq]
    exact ⟨termSubstVarEqOfNotFree t₁ (fun hm => h (Or.inl hm)),
        termSubstVarEqOfNotFree t₂ (fun hm => h (Or.inr hm))⟩
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.conj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.disj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.impl.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | neg A ih =>
    simp only [formulaSubstN, FormulaN.neg.injEq]
    exact ih h
  | all w A ih =>
    simp only [formulaSubstN]
    split
    · simp only [FormulaN.all.injEq, true_and]
      exact ih (fun hm => h ⟨hm, bne_iff_ne.mp ‹y != w›⟩)
    · rfl
  | ex w A ih =>
    simp only [formulaSubstN]
    split
    · simp only [FormulaN.ex.injEq, true_and]
      exact ih (fun hm => h ⟨hm, bne_iff_ne.mp ‹y != w›⟩)
    · rfl

theorem folkVar_renamedEigenFresh
    (formulaSubstVarEqOfNotFree : ∀ (F : FormulaN L), ¬y ∈ formulaFVN F → formulaSubstN F (Term.var z) y = F)
      (e : Nat) (F : FormulaN L) (he : ¬e ∈ formulaFVN F) (hz : ¬z ∈ formulaFVN F) (hez : e ≠ z)
    : ¬(if e = y then z else e) ∈ formulaFVN (formulaSubstN F (Term.var z) y) := by
  by_cases hey : e = y
  · subst e
    simp only [if_pos]
    rw [formulaSubstVarEqOfNotFree F he]
    exact hz
  · simp only [if_neg hey]
    exact formulaFV_formulaSubst_ne F y z e he hez

theorem folkVar_sequentFreshAfterSubst
    (renamedEigenFresh : ∀ (e : Nat) (F : FormulaN L), ¬e ∈ formulaFVN F → ¬z ∈ formulaFVN F → e ≠ z → ¬(if e
      = y then z else e) ∈ formulaFVN (formulaSubstN F (Term.var z) y)) (q : Sequent L) (e : Nat) (he : ∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) (hz : sequentVarNotOccurs q z) (hez :
      e ≠ z)
    : ∀ (F : FormulaN L), F ∈ (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e
      = y then z else e) ∈ formulaFVN F := by
  intro F hF
  change F ∈ q.antecedent.map (fun A => formulaSubstN A (.var z) y) ++
      q.succedent.map (fun A => formulaSubstN A (.var z) y) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inl hG)
    exact renamedEigenFresh e G (he G hmem) (hz G hmem).1 hez
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inr hG)
    exact renamedEigenFresh e G (he G hmem) (hz G hmem).1 hez

def folkVar_allLeft
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (formulaSubstN A t₀ x
      :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.allLeft t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.allLeft t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.allLeft
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

def folkVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A (Term.var e) x])) z y)) (hRuleNB : (FOLKStep1.allRight e x A Γ Δ hfresh
      hfree).notBoundIn y) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (.var e') x])) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

def folkVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (formulaSubstN A
      (Term.var e) x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y)
      (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y) (.var e') x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

def folkVar_exRight
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A t₀ x])) z y)) (hRuleNB : (FOLKStep1.exRight t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.exRight t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x])) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.exRight
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

def folkVar_oneRule
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (s : Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem s) (hRuleNB : rule.notBoundIn y)
      (hRuleNO : rule.varNotOccurs z) (transformedTree : FOLKProofTree (sequentSubstVar prem z y))
    : FOLKProofTree (sequentSubstVar s z y) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.weakenLeft (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.weakenRight (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise
        (FOLKStep1.contractRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.orRightL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.orRightR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.implRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise
        (FOLKStep1.negLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise
        (FOLKStep1.negRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact folkVar_allLeft L z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact folkVar_allRight L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact folkVar_exLeft L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact folkVar_exRight L z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO

def folkVar_twoRule
    (s : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 s) (transformedTree₁
      : FOLKProofTree (sequentSubstVar prem1 z y)) (transformedTree₂ : FOLKProofTree (sequentSubstVar prem2 z
      y))
    : FOLKProofTree (sequentSubstVar s z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstVar] using FOLKProofTree.twoPremise (FOLKStep2.cut (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)

end

/-- Lemma 6.5.1 (part a — variable substitution): Given an LK-proof T of
Γ → Δ, for any variable y not occurring bound in T and any variable z not
occurring in T, the result T[z/y] of substituting z for all occurrences of
y in T is a proof tree of the substituted sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def folkProofSubstVar {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKProofTree (sequentSubstVar s z y) := by
  exact transform T z y hNotBound hNotOccurs
where
  transform {L : Language} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKProofTree s) (z y : Nat)
      (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstVar s z y) := by
    have termSubstVarEqOfNotFree :
        ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree :
        ∀ F : FormulaN L, y ∉ formulaFVN F →
          formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉
          formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++
            (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    exact match T with
    | .axiom_ q hax => by
      have hax' : isFOLKAxiom (sequentSubstVar q z y) := by
        rcases hax with ⟨A, hΓ, hΔ⟩
        exact
          ⟨formulaSubstN A (.var z) y,
            by simp [sequentSubstVar, hΓ],
            by simp [sequentSubstVar, hΔ]⟩
      exact FOLKProofTree.axiom_ _ hax'
    | .onePremise rule t => by
      simp only [FOLKProofTree.notBoundIn] at hNotBound
      simp only [FOLKProofTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨hRuleNB, hTreeNB⟩
      rcases hNotOccurs with ⟨hRuleNO, hTreeNO⟩
      have transformedTree :=
        transform t z y hTreeNB hTreeNO
      exact folkVar_oneRule L z y sequentFreshAfterSubst _ _ rule hRuleNB hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKProofTree.notBoundIn] at hNotBound
      simp only [FOLKProofTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨_, hTree₁NB, hTree₂NB⟩
      rcases hNotOccurs with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ :=
        transform t₁ z y hTree₁NB hTree₁NO
      have transformedTree₂ :=
        transform t₂ z y hTree₂NB hTree₂NO
      exact folkVar_twoRule L z y _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural T

section
variable (L : Language) (hL : L.withoutEquality) (z y : Nat)

def dedVar_allLeft
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (formulaSubstN A
      t₀ x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.allLeft t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.allLeft t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.allLeft
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

def dedVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ
      ++ [formulaSubstN A (Term.var e) x])) z y)) (hRuleNB : (FOLKStep1.allRight e x A Γ Δ hfresh
      hfree).notBoundIn y) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (.var e') x])) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

def dedVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (formulaSubstN A
      (Term.var e) x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y)
      (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y) (.var e') x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

def dedVar_exRight
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A t₀ x])) z y)) (hRuleNB : (FOLKStep1.exRight t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.exRight t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x])) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.exRight
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

def dedVar_oneRule
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (s : Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem s) (hRuleNB : rule.notBoundIn y)
      (hRuleNO : rule.varNotOccurs z) (transformedTree : FOLKDeductionTree hL (sequentSubstVar prem z y))
    : FOLKDeductionTree hL (sequentSubstVar s z y) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.orRightL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.orRightR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.implRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise
        (FOLKStep1.negLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise
        (FOLKStep1.negRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact dedVar_allLeft L hL z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact dedVar_allRight L hL z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact dedVar_exLeft L hL z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact dedVar_exRight L hL z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO

def dedVar_twoRule
    (s : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 s) (transformedTree₁
      : FOLKDeductionTree hL (sequentSubstVar prem1 z y)) (transformedTree₂ : FOLKDeductionTree hL
      (sequentSubstVar prem2 z y))
    : FOLKDeductionTree hL (sequentSubstVar s z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.twoPremise (FOLKStep2.cut (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)

end

/-- Variable substitution T[z/y] on LK deduction trees. Every node sequent
and rule annotation is substituted, including arbitrary leaf sequents.
If a quantifier rule's eigenvariable is y, its new eigenvariable is z.
The source variable is not bound in the tree and the target variable is fresh. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.substVar {L : Language}
    {hL : L.withoutEquality} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstVar s z y) := by
  exact transform T z y hNotBound hNotOccurs
where
  transform {L : Language}
      {hL : L.withoutEquality} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z y : Nat)
      (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstVar s z y) := by
    have termSubstVarEqOfNotFree :
        ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree :
        ∀ F : FormulaN L, y ∉ formulaFVN F →
          formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉
          formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++
            (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    exact match T with
    | .leaf q => FOLKDeductionTree.leaf (sequentSubstVar q z y)
    | .onePremise rule t => by
      simp only [FOLKDeductionTree.notBoundIn] at hNotBound
      simp only [FOLKDeductionTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨hRuleNB, hTreeNB⟩
      rcases hNotOccurs with ⟨hRuleNO, hTreeNO⟩
      have transformedTree :=
        transform t z y hTreeNB hTreeNO
      exact dedVar_oneRule L hL z y sequentFreshAfterSubst _ _ rule hRuleNB hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKDeductionTree.notBoundIn] at hNotBound
      simp only [FOLKDeductionTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨_, hTree₁NB, hTree₂NB⟩
      rcases hNotOccurs with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ :=
        transform t₁ z y hTree₁NB hTree₁NO
      have transformedTree₂ :=
        transform t₂ z y hTree₂NB hTree₂NO
      exact dedVar_twoRule L hL z y _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural T

/-- On proof trees, deduction-tree substitution has exactly the proof-tree
image given by `folkProofSubstVar`. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.substVar_proof_image
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    ∃ hp' : (T.substVar z y hNotBound hNotOccurs).isProof,
      (T.substVar z y hNotBound hNotOccurs).toProofTree hp' =
        folkProofSubstVar (T.toProofTree hp) z y
          ((T.notBoundIn_toProofTree hp y).mpr hNotBound)
          ((T.varNotOccurs_toProofTree hp z).mpr hNotOccurs) := by
  -- REPAIR(T6-41a): proof pending
  sorry

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
section
variable (L : Language) (z : Nat) (y : Nat)

def stepVar_allLeft
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotBound : (FOLKStep1.allLeft t x A Γ Δ hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.allLeft t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (formulaSubstN A t x :: Γ) (Δ)) z y) (sequentSubstVar (Sequent.mk
      (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t x y z hxy hzx hfree hNoY hNoZ
  simpa [sequentSubstVar, formulaSubstN, hyx, formulaSubst_var_comm A t x y z hxy hzx hNoY] using
      FOLKStep1.allLeft (termSubst t (.var z) y) x (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree'

def stepVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (hNotBound : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).notBoundIn y)
      (hNotOccurs : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var e) x])) z y)
      (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hNotOccurs.2.1 (Ne.symm hze)
  simpa [sequentSubstVar, formulaSubstN, hyx, hterm,
    formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree'

def stepVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (hNotBound : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ) (Δ)) z y) (sequentSubstVar
      (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hNotOccurs.2.1 (Ne.symm hze)
  simpa [sequentSubstVar, formulaSubstN, hyx, hterm,
    formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree'

def stepVar_exRight
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotBound : (FOLKStep1.exRight t x A Γ Δ hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.exRight t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t x])) z y) (sequentSubstVar
      (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t x y z hxy hzx hfree hNoY hNoZ
  simpa [sequentSubstVar, formulaSubstN, hyx, formulaSubst_var_comm A t x y z hxy hzx hNoY] using
      FOLKStep1.exRight (termSubst t (.var z) y) x (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree'

end

@[blueprint "chap6__lemma_6_5_1"]
def folkStep1SubstVar {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (z y : Nat) (hNotBound : rule.notBoundIn y)
    (hNotOccurs : rule.varNotOccurs z) :
    FOLKStep1 (sequentSubstVar prem z y)
      (sequentSubstVar conc z y) := by
  exact transform rule z y hNotBound hNotOccurs
where
  transform {L : Language}
      {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (z y : Nat) (hNotBound : rule.notBoundIn y)
      (hNotOccurs : rule.varNotOccurs z) :
      FOLKStep1 (sequentSubstVar prem z y)
        (sequentSubstVar conc z y)  := by
    have termSubstVarEqOfNotFree : ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree : ∀ F : FormulaN L, y ∉ formulaFVN F → formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉ formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    cases rule with
    | weakenLeft A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.weakenLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | weakenRight A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.weakenRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | contractLeft A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.contractLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | contractRight A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.contractRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | exchangeLeft Γ A B Δ Λ =>
        simpa [sequentSubstVar] using FOLKStep1.exchangeLeft (Γ.map (fun F => formulaSubstN F (.var z) y))
            (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Δ.map (fun F => formulaSubstN F (.var z) y))
            (Λ.map (fun F => formulaSubstN F (.var z) y))
    | exchangeRight Γ Δ A B Λ =>
        simpa [sequentSubstVar] using FOLKStep1.exchangeRight (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
            (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Λ.map (fun F => formulaSubstN F (.var z) y))
    | andLeftL A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.andLeftL (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | andLeftR A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.andLeftR (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | orRightL A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.orRightL (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | orRightR A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.orRightR (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | implRight A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.implRight (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | negLeft A Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.negLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | negRight A Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.negRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | allLeft t x A Γ Δ hfree =>
        exact stepVar_allLeft L z y t x A Γ Δ hfree hNotBound hNotOccurs
    | allRight e x A Γ Δ hfresh hfree =>
        exact stepVar_allRight L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree hNotBound hNotOccurs
    | exLeft e x A Γ Δ hfresh hfree =>
        exact stepVar_exLeft L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree hNotBound hNotOccurs
    | exRight t x A Γ Δ hfree =>
        exact stepVar_exRight L z y t x A Γ Δ hfree hNotBound hNotOccurs

@[blueprint "chap6__lemma_6_5_1"]
def folkStep2SubstVar {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) (z y : Nat) :
    FOLKStep2 (sequentSubstVar prem₁ z y)
      (sequentSubstVar prem₂ z y) (sequentSubstVar conc z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      simpa [sequentSubstVar] using
        FOLKStep2.cut
          (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y))
  | andRight A B Γ Δ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
  | orLeft A B Γ Δ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
  | implLeft A B Γ Δ Λ Θ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y))

end LCS.CutElim.Interpolation
end
