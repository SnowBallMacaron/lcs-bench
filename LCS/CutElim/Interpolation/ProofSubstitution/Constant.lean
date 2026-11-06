import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.ProofSubstitution.Basic
import Attach
import LCS.CutElim.Interpolation.ProofSubstitution.Constant.ProofsStamp

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
-- ATTACH-BLOCKER: variable
variable (L : Language) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_termComm
    (u : Term L) (t : Term L) (x : Nat) (hzx : z ≠ x)
    : termSubstConst (termSubst u t x) z c = termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
  induction u with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> simp_all [termSubstConst, termSubst]
  | const d =>
    simp only [termSubst, termSubstConst]
    by_cases hdc : d = c
    · subst hdc
      simp [termSubst, hzx]
    · simp [termSubst, hdc]
  | func f ts ih =>
    simp only [termSubst, termSubstConst]
    congr 1
    ext i
    exact ih i

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_formulaComm
    (termComm : ∀ (u t : Term L) (x : Nat), z ≠ x → termSubstConst (termSubst u t x) z c = termSubst
      (termSubstConst u z c) (termSubstConst t z c) x) (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x)
    : formulaSubstConst (formulaSubstN A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t
      z c) x := by
  induction A with
  | predN P ts =>
    simp [formulaSubstN, formulaSubstConst]
    congr 1
    ext i
    exact termComm _ _ _ hzx
  | eq_ _ t₁ t₂ =>
    simp [formulaSubstN, formulaSubstConst, termComm t₁ t x hzx, termComm t₂ t x hzx]
  | conj A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | disj A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | impl A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | neg A ih =>
    simp [formulaSubstN, formulaSubstConst, ih]
  | all w A ih =>
    simp [formulaSubstN, formulaSubstConst]
    split <;> simp [formulaSubstConst, ih]
  | ex w A ih =>
    simp [formulaSubstN, formulaSubstConst]
    split <;> simp [formulaSubstConst, ih]

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_termFreshAfterConst
    (t : Term L) (v : Nat) (hvz : v ≠ z) (h : ¬v ∈ termFV t)
    : ¬v ∈ termFV (termSubstConst t z c) := by
  induction t with
  | var w => exact h
  | const d =>
    simp only [termSubstConst]
    split
    · simp [termFV]
      exact hvz
    · exact fun hm => h hm
  | func f ts ih =>
    simp only [termSubstConst, termFV] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_freeAfterConst
    (termFreshAfterConst : ∀ (t : Term L) (v : Nat), v ≠ z → ¬v ∈ termFV t → ¬v ∈ termFV (termSubstConst t z
      c)) (A : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : ¬z ∈ formulaBVN A)
    : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) := by
  induction A with
  | predN P ts => trivial
  | eq_ _ t₁ t₂ => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | neg A ih =>
    exact ih hfree hNoZ
  | all w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left
      exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right
      exact ⟨termFreshAfterConst t w (Ne.symm hzw) hwtv, ih hff (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left
      exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right
      exact ⟨termFreshAfterConst t w (Ne.symm hzw) hwtv, ih hff (fun h => hNoZ (Or.inl h))⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_formulaFreshAfterConst
    (termFreshAfterConst : ∀ (t : Term L) (v : Nat), v ≠ z → ¬v ∈ termFV t → ¬v ∈ termFV (termSubstConst t z
      c)) (A : FormulaN L) (v : Nat) (hvz : v ≠ z) (h : ¬v ∈ formulaFVN A)
    : ¬v ∈ formulaFVN (formulaSubstConst A z c) := by
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (termFreshAfterConst (ts i) v hvz (fun hm => h ⟨i, hm⟩)).elim hi⟩
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with h₁ | h₂
    · exact (termFreshAfterConst t₁ v hvz (fun hm => h (Or.inl hm))).elim h₁
    · exact (termFreshAfterConst t₂ v hvz (fun hm => h (Or.inr hm))).elim h₂
  | conj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | disj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | impl A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | neg A ih =>
    simp only [formulaSubstConst, formulaFVN]
    exact ih h
  | all w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩
    exact ih (fun hm' => h ⟨hm', hne⟩) hm
  | ex w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩
    exact ih (fun hm' => h ⟨hm', hne⟩) hm

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_sequentFreshAfterConst
    (formulaFreshAfterConst : ∀ (A : FormulaN L) (v : Nat), v ≠ z → ¬v ∈ formulaFVN A → ¬v ∈ formulaFVN
      (formulaSubstConst A z c)) (q : Sequent L) (e : Nat) (he : ∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) (hez : e ≠ z)
    : ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e
      ∈ formulaFVN F := by
  intro F hF
  change F ∈ q.antecedent.map (fun A => formulaSubstConst A z c) ++
      q.succedent.map (fun A => formulaSubstConst A z c) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inl hG)
    exact formulaFreshAfterConst G e hez (he G hmem)
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inr hG)
    exact formulaFreshAfterConst G e hez (he G hmem)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_allLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstConst
      (Sequent.mk (formulaSubstN A t₀ x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.allLeft t₀ x A Γ Δ
      hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (termSubstConst t₀ z c) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.allLeft
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_allRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e)
      x A) (transformedTree : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A
      (Term.var e) x])) z c)) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++
            [formulaSubstN (formulaSubstConst A z c) (.var e) x])) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.allRight e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_exLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x
      A) (transformedTree : FOLKProofTree (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ)
      (Δ)) z c)) (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (.var e) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exLeft e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_exRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstConst
      (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t₀ x])) z c)) (hRuleNO : (FOLKStep1.exRight t₀ x A Γ Δ
      hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++ [formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x])) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exRight
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_oneRule
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (q :
      Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem q) (hRuleNO : rule.varNotOccurs z) (transformedTree
      : FOLKProofTree (sequentSubstConst prem z c))
    : FOLKProofTree (sequentSubstConst q z c) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.weakenLeft (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.weakenRight (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.contractLeft (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.contractRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.orRightL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.orRightR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.implRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.negLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.negRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact folkConst_allLeft L z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact folkConst_allRight L z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact folkConst_exLeft L z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact folkConst_exRight L z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_twoRule
    (q : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 q) (transformedTree₁
      : FOLKProofTree (sequentSubstConst prem1 z c)) (transformedTree₂ : FOLKProofTree (sequentSubstConst
      prem2 z c))
    : FOLKProofTree (sequentSubstConst q z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.cut (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)

end

/-- Constant substitution on LK proofs: for any constant c and a variable z
fresh in T, replace c by z in every node sequent and rule annotation.
The result is a proof of the substituted sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkProofSubstConst {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKProofTree (sequentSubstConst s z c) := by
  exact prepare T z c hNotOccurs
where
  prepare {L : Language} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKProofTree s) (z : Nat) (c : L.constSymbols)
      (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstConst s z c) := by
    have termComm (u t : Term L) (x : Nat) (hzx : z ≠ x) :
        termSubstConst (termSubst u t x) z c =
          termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
      exact folkConst_termComm L z c u _ x hzx
    have formulaComm (A : FormulaN L) (t : Term L) (x : Nat)
        (hzx : z ≠ x) :
        formulaSubstConst (formulaSubstN A t x) z c =
          formulaSubstN (formulaSubstConst A z c)
            (termSubstConst t z c) x := by
      exact folkConst_formulaComm L z c termComm A t x hzx
    have termFreshAfterConst (t : Term L) (v : Nat) (hvz : v ≠ z)
        (h : v ∉ termFV t) :
        v ∉ termFV (termSubstConst t z c) := by
      exact folkConst_termFreshAfterConst L z c t _ hvz h
    have freeAfterConst (A : FormulaN L) (t : Term L) (x : Nat)
        (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A) :
        isFreeForN (termSubstConst t z c) x
          (formulaSubstConst A z c) := by
      exact folkConst_freeAfterConst L z c termFreshAfterConst A t _ hfree hNoZ
    have formulaFreshAfterConst (A : FormulaN L) (v : Nat)
        (hvz : v ≠ z) (h : v ∉ formulaFVN A) :
        v ∉ formulaFVN (formulaSubstConst A z c) := by
      exact folkConst_formulaFreshAfterConst L z c termFreshAfterConst A v hvz h
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++
            (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      exact folkConst_sequentFreshAfterConst L z c formulaFreshAfterConst q e he hez
    exact transform z c formulaComm freeAfterConst sequentFreshAfterConst T hNotOccurs

  transform {L : Language} (z : Nat) (c : L.constSymbols)
      (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x), formulaSubstConst (formulaSubstN
        A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A
        : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A), isFreeForN
        (termSubstConst t z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e :
        Nat) (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F) (hez : e ≠ z), ∀ F ∈
        (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent, e ∉ formulaFVN F)
      {q : Sequent L}
      (U : LCS.CutElim.LK.FOLKProofTree q) (hNO : U.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstConst q z c) :=
    match U with
    | .axiom_ q hax => by
      have hax' : isFOLKAxiom (sequentSubstConst q z c) := by
        rcases hax with ⟨A, hΓ, hΔ⟩
        exact
          ⟨formulaSubstConst A z c,
            by simp [sequentSubstConst, hΓ],
            by simp [sequentSubstConst, hΔ]⟩
      exact FOLKProofTree.axiom_ _ hax'
    | .onePremise rule t => by
      simp only [FOLKProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨hRuleNO, hTreeNO⟩
      have transformedTree := transform z c formulaComm freeAfterConst sequentFreshAfterConst t hTreeNO
      exact folkConst_oneRule L z c formulaComm freeAfterConst sequentFreshAfterConst _ _ rule hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₁ hTree₁NO
      have transformedTree₂ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₂ hTree₂NO
      exact folkConst_twoRule L z c _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural U

section
-- ATTACH-BLOCKER: variable
variable (L : Language) (hL : L.withoutEquality) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_allLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL
      (sequentSubstConst (Sequent.mk (formulaSubstN A t₀ x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.allLeft t₀ x
      A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.allLeft
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_allRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e)
      x A) (transformedTree : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A
      (Term.var e) x])) z c)) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++
            [formulaSubstN (formulaSubstConst A z c) (.var e) x])) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.allRight e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_exLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x
      A) (transformedTree : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e)
      x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (.var e) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exLeft e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_exRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL
      (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t₀ x])) z c)) (hRuleNO : (FOLKStep1.exRight t₀
      x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++ [formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x])) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exRight
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_oneRule
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (q :
      Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem q) (hRuleNO : rule.varNotOccurs z) (transformedTree
      : FOLKDeductionTree hL (sequentSubstConst prem z c))
    : FOLKDeductionTree hL (sequentSubstConst q z c) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.orRightL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.orRightR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.implRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.negLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.negRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact dedConst_allLeft L hL z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact dedConst_allRight L hL z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact dedConst_exLeft L hL z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact dedConst_exRight L hL z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_twoRule
    (q : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 q) (transformedTree₁
      : FOLKDeductionTree hL (sequentSubstConst prem1 z c)) (transformedTree₂ : FOLKDeductionTree hL
      (sequentSubstConst prem2 z c))
    : FOLKDeductionTree hL (sequentSubstConst q z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.cut (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)

end

/-- Constant substitution T[z/c] on LK deduction trees. For any constant c
and a variable z fresh in T, substitute in every leaf sequent and every rule
annotation, retaining the tree's inference structure. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def _root_.LCS.CutElim.LK.FOLKDeductionTree.substConst
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst s z c) := by
  exact prepare T z c hNotOccurs
where
  prepare
      {L : Language} {hL : L.withoutEquality} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
      (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst s z c) := by
    have termComm (u t : Term L) (x : Nat) (hzx : z ≠ x) :
        termSubstConst (termSubst u t x) z c =
          termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
      exact folkConst_termComm L z c u _ x hzx
    have formulaComm (A : FormulaN L) (t : Term L) (x : Nat)
        (hzx : z ≠ x) :
        formulaSubstConst (formulaSubstN A t x) z c =
          formulaSubstN (formulaSubstConst A z c)
            (termSubstConst t z c) x := by
      exact folkConst_formulaComm L z c termComm A t x hzx
    have termFreshAfterConst (t : Term L) (v : Nat) (hvz : v ≠ z)
        (h : v ∉ termFV t) :
        v ∉ termFV (termSubstConst t z c) := by
      exact folkConst_termFreshAfterConst L z c t _ hvz h
    have freeAfterConst (A : FormulaN L) (t : Term L) (x : Nat)
        (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A) :
        isFreeForN (termSubstConst t z c) x
          (formulaSubstConst A z c) := by
      exact folkConst_freeAfterConst L z c termFreshAfterConst A t _ hfree hNoZ
    have formulaFreshAfterConst (A : FormulaN L) (v : Nat)
        (hvz : v ≠ z) (h : v ∉ formulaFVN A) :
        v ∉ formulaFVN (formulaSubstConst A z c) := by
      exact folkConst_formulaFreshAfterConst L z c termFreshAfterConst A v hvz h
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++
            (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      exact folkConst_sequentFreshAfterConst L z c formulaFreshAfterConst q e he hez
    exact transform z c formulaComm freeAfterConst sequentFreshAfterConst T hNotOccurs

  transform {L : Language} {hL : L.withoutEquality} (z : Nat) (c : L.constSymbols)
      (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x), formulaSubstConst (formulaSubstN
        A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A
        : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A), isFreeForN
        (termSubstConst t z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e :
        Nat) (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F) (hez : e ≠ z), ∀ F ∈
        (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent, e ∉ formulaFVN F)
      {q : Sequent L}
      (U : LCS.CutElim.LK.FOLKDeductionTree hL q) (hNO : U.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst q z c) :=
    match U with
    | .leaf q => FOLKDeductionTree.leaf (sequentSubstConst q z c)
    | .onePremise rule t => by
      simp only [FOLKDeductionTree.varNotOccurs] at hNO
      rcases hNO with ⟨hRuleNO, hTreeNO⟩
      have transformedTree := transform z c formulaComm freeAfterConst sequentFreshAfterConst t hTreeNO
      exact dedConst_oneRule L hL z c formulaComm freeAfterConst sequentFreshAfterConst _ _ rule hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKDeductionTree.varNotOccurs] at hNO
      rcases hNO with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₁ hTree₁NO
      have transformedTree₂ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₂ hTree₂NO
      exact dedConst_twoRule L hL z c _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural U

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Deduction-tree constant substitution preserves proof trees, and its
proof-tree image is `folkProofSubstConst`. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.substConst_proof_image
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    ∃ hp' : (T.substConst z c hNotOccurs).isProof,
      (T.substConst z c hNotOccurs).toProofTree hp' =
        folkProofSubstConst (T.toProofTree hp) z c
          ((T.varNotOccurs_toProofTree hp z).mpr hNotOccurs) := by
  -- REPAIR(T6-41b): proof pending
  sorry

-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_allLeft
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotOccurs : (FOLKStep1.allLeft t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (formulaSubstN A t x :: Γ) (Δ)) z c) (sequentSubstConst
      (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t x z c hfree hNoZ
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A t x z c hzx] using
      FOLKStep1.allLeft (termSubstConst t z c) x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_allRight
    (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent
      ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ :
      List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all
      x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x A) (hNotOccurs : (FOLKStep1.allRight e x A
      Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var e) x])) z c)
      (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
    termSubstConst] using FOLKStep1.allRight e x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_exLeft
    (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent
      ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ :
      List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++
      (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x A) (hNotOccurs : (FOLKStep1.exLeft e x A Γ Δ
      hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ) (Δ)) z c)
      (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
    termSubstConst] using FOLKStep1.exLeft e x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_exRight
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotOccurs : (FOLKStep1.exRight t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t x])) z c) (sequentSubstConst
      (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t x z c hfree hNoZ
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A t x z c hzx] using
      FOLKStep1.exRight (termSubstConst t z c) x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree'

end

@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkStep1SubstConst {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (z : Nat) (c : L.constSymbols) (hNotOccurs : rule.varNotOccurs z) :
    FOLKStep1 (sequentSubstConst prem z c)
      (sequentSubstConst conc z c) := by
  exact transform rule z c hNotOccurs
where
  transform {L : Language}
      {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (z : Nat) (c : L.constSymbols) (hNotOccurs : rule.varNotOccurs z) :
      FOLKStep1 (sequentSubstConst prem z c)
        (sequentSubstConst conc z c)  := by
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      intro F hF
      change F ∈ q.antecedent.map (fun A => formulaSubstConst A z c) ++
          q.succedent.map (fun A => formulaSubstConst A z c) at hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
        exact formulaFV_formulaSubstConst G z c e hez (he G (List.mem_append.mpr (Or.inl hG)))
      · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
        exact formulaFV_formulaSubstConst G z c e hez (he G (List.mem_append.mpr (Or.inr hG)))
    cases rule with
    | weakenLeft A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.weakenLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | weakenRight A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.weakenRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | contractLeft A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.contractLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | contractRight A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.contractRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | exchangeLeft Γ A B Δ Λ =>
        simpa [sequentSubstConst] using FOLKStep1.exchangeLeft (Γ.map (fun F => formulaSubstConst F z c))
            (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Δ.map (fun F => formulaSubstConst F z c))
            (Λ.map (fun F => formulaSubstConst F z c))
    | exchangeRight Γ Δ A B Λ =>
        simpa [sequentSubstConst] using FOLKStep1.exchangeRight (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
            (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Λ.map (fun F => formulaSubstConst F z c))
    | andLeftL A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.andLeftL (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | andLeftR A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.andLeftR (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | orRightL A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.orRightL (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | orRightR A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.orRightR (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | implRight A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.implRight (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | negLeft A Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.negLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | negRight A Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.negRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | allLeft t x A Γ Δ hfree =>
        exact stepConst_allLeft L z c t x A Γ Δ hfree hNotOccurs
    | allRight e x A Γ Δ hfresh hfree =>
        exact stepConst_allRight L z c sequentFreshAfterConst e x A Γ Δ hfresh hfree hNotOccurs
    | exLeft e x A Γ Δ hfresh hfree =>
        exact stepConst_exLeft L z c sequentFreshAfterConst e x A Γ Δ hfresh hfree hNotOccurs
    | exRight t x A Γ Δ hfree =>
        exact stepConst_exRight L z c t x A Γ Δ hfree hNotOccurs

@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkStep2SubstConst {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) (z : Nat)
    (c : L.constSymbols) :
    FOLKStep2 (sequentSubstConst prem₁ z c)
      (sequentSubstConst prem₂ z c) (sequentSubstConst conc z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      simpa [sequentSubstConst] using
        FOLKStep2.cut
          (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c))
  | andRight A B Γ Δ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
  | orLeft A B Γ Δ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
  | implLeft A B Γ Δ Λ Θ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c))

end LCS.CutElim.Interpolation
end
