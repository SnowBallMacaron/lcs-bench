import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.HintikkaSets
import LCS.FirstOrder.Gentzen.Hintikka.Branching

/-! # Free substitutions along the search tree (Section 5.4.7)

Bound variables of every node stay among those of the root sequent and the free
variables avoid them, so the substitutions performed by the quantifier rules are
free ("This condition ensures that terms occurring in formulae in the sequent
are free for substitutions").
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- If no free variable of t is a bound variable of A, then t is free
for x in A. Key lemma for Hintikka set condition H6. -/
theorem isFreeForN_of_bv_disjoint {L : Language} (t : Term L) (x : Nat) (A : FormulaN L)
    (h : ∀ v, v ∈ termFV t → v ∉ formulaBVN A) : isFreeForN t x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => trivial
  | neg A ih => exact ih (fun v hv => h v hv)
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    exact ⟨ihA (fun v hv hm => h v hv (Or.inl hm)),
           ihB (fun v hv hm => h v hv (Or.inr hm))⟩
  | all y A ih | ex y A ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨fun hv => h y hv (Or.inr rfl),
                     ih (fun v hv hm => h v hv (Or.inl hm))⟩

/-- Bound variables are preserved (not increased) by substitution. -/
theorem formulaBVN_formulaSubstN {L : Language} (A : FormulaN L) (t : Term L)
    (x : Nat) (v : Nat) :
    v ∈ formulaBVN (formulaSubstN A t x) → v ∈ formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => exact id
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    intro hv; rcases hv with h | h
    · exact Or.inl (ihA h)
    · exact Or.inr (ihB h)
  | all y A ih | ex y A ih =>
    intro hv
    simp only [formulaSubstN] at hv
    split at hv
    · simp only [formulaBVN] at hv ⊢
      rcases hv with h | h
      · exact Or.inl (ih h)
      · exact Or.inr h
    · exact hv

-- ===================================================================
-- FV tracking: termFV_termSubst, formulaFVN_formulaSubstN
-- ===================================================================

/-- FV of term substitution: if y ∈ FV(termSubst t s x), then either
y was already in FV(t) with y ≠ x, or x was in FV(t) and y ∈ FV(s). -/
theorem termFV_termSubst {L : Language} (t s : Term L) (x y : Nat)
    (hy : y ∈ termFV (termSubst t s x)) :
    (y ∈ termFV t ∧ y ≠ x) ∨ (x ∈ termFV t ∧ y ∈ termFV s) := by
-- BEGIN PROOF
  induction t with
  | var i =>
    simp only [termSubst] at hy; split at hy
    · next h => exact Or.inr ⟨h.symm ▸ rfl, hy⟩
    · next h => have hyi : y = i := hy; exact Or.inl ⟨hyi ▸ rfl, hyi ▸ h⟩
  | const c => exact absurd hy id
  | func f ts ih =>
    simp only [termSubst, termFV] at hy; obtain ⟨j, hj⟩ := hy
    rcases ih j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨j, h1⟩, h2⟩
    · exact Or.inr ⟨⟨j, h1⟩, h2⟩

/-- FV of formulaSubstN: if y ∈ FV(A[t/x]), then either y ∈ FV(A) with
y ≠ x, or y ∈ FV(t). This tracks how free variables flow through
substitution. -/
theorem formulaFVN_formulaSubstN {L : Language} (A : FormulaN L) (t : Term L) (x y : Nat)
    (hy : y ∈ formulaFVN (formulaSubstN A t x)) :
    (y ∈ formulaFVN A ∧ y ≠ x) ∨ y ∈ termFV t := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢; obtain ⟨j, hj⟩ := hy
    rcases termFV_termSubst (ts j) t x y hj with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact Or.inl ⟨⟨j, h1⟩, h2⟩
    · exact Or.inr h2
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢
    rcases hy with h1 | h2
    · rcases termFV_termSubst t1 t x y h1 with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr h2
    · rcases termFV_termSubst t2 t x y h2 with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr h2
  | neg A ih => simp only [formulaSubstN, formulaFVN] at hy ⊢; exact ih hy
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢; rcases hy with h | h
    · rcases ihA h with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr h1
    · rcases ihB h with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr h1
  | all i A ih | ex i A ih =>
    simp only [formulaSubstN] at hy; split at hy
    · next hne =>
      simp only [formulaFVN] at hy ⊢; obtain ⟨hA, hni⟩ := hy
      rcases ih hA with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨⟨h1, hni⟩, h2⟩
      · exact Or.inr h1
    · next hne =>
      have hxi : x = i := by simp [bne] at hne; exact hne
      simp only [formulaFVN] at hy ⊢
      exact Or.inl ⟨hy, fun heq => hy.2 (hxi ▸ heq)⟩

end LCS.FirstOrder.Gentzen.Hintikka
end
