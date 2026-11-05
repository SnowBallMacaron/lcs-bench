import LCS.Item
import LCS.FirstOrder.SemanticsN

/-! # FirstOrder.SemanticsN.Substitution
    Substitution-evaluation lemmas for FormulaN (Lemma 5.3.1).
    The canonical location for formulaSubstEvalDirectN.
-/

namespace LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN

-- ===================================================================
-- Lemma 5.3.1 Part (i): Term substitution-evaluation equivalence
-- ===================================================================

/-- Lemma 5.3.1 (companion, Part (i), term form): For any terms r and t,
structure M, and assignment s, evaluating r[t/x] under s equals
evaluating r under s[x := t_M[s]]. -/
theorem termSubstEvalDirect {L : Language} {M : Structure L}
    (s : Assignment M) (r t : Term L) (x : Nat) :
    termEval M s (termSubst r t x) =
    termEval M (assignUpdate s x (termEval M s t)) r := by
-- BEGIN PROOF
  induction r with
  | var y =>
    simp [termSubst, termEval, assignUpdate]
    split
    · subst_vars; rfl
    · rfl
  | const c => simp [termSubst, termEval]
  | func f ts ih =>
    simp [termSubst, termEval]; congr 1; funext j; exact ih j

-- ===================================================================
-- Lemma 5.3.1 Part (ii): Formula substitution-evaluation equivalence
-- ===================================================================

/-- Lemma 5.3.1: For any FormulaN A, term t, structure M, and assignment s,
evaluating A[t/x] under s is equivalent to evaluating A under s[x := t_M[s]], provided t is free for x in A. (Lemma 5.3.1 bundles a term-level and formula-level statement; this is the formula-level primary claim.) -/
theorem formulaSubstEvalDirectN {L : Language} {M : Structure L}
    (s : Assignment M) (A : FormulaN L) (t : Term L) (x : Nat)
    (hfree : isFreeForN t x A) :
    formulaEvalN M (formulaSubstN A t x) s ↔
    formulaEvalN M A (assignUpdate s x (termEval M s t)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P ts =>
    simp only [formulaSubstN, formulaEvalN]
    have : (fun i => termEval M s (termSubst (ts i) t x)) =
           (fun i => termEval M (assignUpdate s x (termEval M s t)) (ts i)) := by
      funext j; exact termSubstEvalDirect s (ts j) t x
    rw [this]
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaEvalN]
    rw [termSubstEvalDirect s t1 t x, termSubstEvalDirect s t2 t x]
  | neg A ih =>
    simp only [formulaSubstN, formulaEvalN]; exact not_congr (ih s hfree)
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN]; exact and_congr (ihA s hfree.1) (ihB s hfree.2)
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN]; exact or_congr (ihA s hfree.1) (ihB s hfree.2)
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN]; exact imp_congr (ihA s hfree.1) (ihB s hfree.2)
  | all j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj; simp [formulaEvalN]
      constructor <;> intro h a
      · rw [show assignUpdate (assignUpdate s x (termEval M s t)) x a = assignUpdate s x a from by
          funext k; simp [assignUpdate]; split <;> rfl]; exact h a
      · rw [show assignUpdate s x a = assignUpdate (assignUpdate s x (termEval M s t)) x a from by
          funext k; simp [assignUpdate]; split <;> rfl]; exact h a
    · simp [hxj, formulaEvalN]
      have ⟨hjt, hfree'⟩ : ¬ (termFV t) j ∧ isFreeForN t x A := by
        rcases hfree with rfl | h; exact absurd rfl hxj; exact h
      have htirrel : ∀ a, termEval M (assignUpdate s j a) t = termEval M s t := by
        intro a; exact termCoincidence M t _ s (fun y hy => by
          simp [assignUpdate]; intro heq; exact absurd (heq ▸ hy) hjt)
      have swap : ∀ a, assignUpdate (assignUpdate s x (termEval M s t)) j a =
                       assignUpdate (assignUpdate s j a) x (termEval M s t) := by
        intro a; funext k; simp [assignUpdate]; split <;> split <;> simp_all
      constructor <;> intro h a
      · rw [swap]; rw [← htirrel a]; exact (ih (assignUpdate s j a) hfree').mp (h a)
      · have ha := h a; rw [swap] at ha; rw [← htirrel a] at ha
        exact (ih (assignUpdate s j a) hfree').mpr ha
  | ex j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj; simp [formulaEvalN]
      constructor <;> intro ⟨a, ha⟩
      · exact ⟨a, by rw [show assignUpdate (assignUpdate s x (termEval M s t)) x a = assignUpdate s x a from by
          funext k; simp [assignUpdate]; split <;> rfl]; exact ha⟩
      · exact ⟨a, by rw [show assignUpdate s x a = assignUpdate (assignUpdate s x (termEval M s t)) x a from by
          funext k; simp [assignUpdate]; split <;> rfl]; exact ha⟩
    · simp [hxj, formulaEvalN]
      have ⟨hjt, hfree'⟩ : ¬ (termFV t) j ∧ isFreeForN t x A := by
        rcases hfree with rfl | h; exact absurd rfl hxj; exact h
      have htirrel : ∀ a, termEval M (assignUpdate s j a) t = termEval M s t := by
        intro a; exact termCoincidence M t _ s (fun y hy => by
          simp [assignUpdate]; intro heq; exact absurd (heq ▸ hy) hjt)
      have swap : ∀ a, assignUpdate (assignUpdate s x (termEval M s t)) j a =
                       assignUpdate (assignUpdate s j a) x (termEval M s t) := by
        intro a; funext k; simp [assignUpdate]; split <;> split <;> simp_all
      constructor <;> intro ⟨a, ha⟩
      · exact ⟨a, by rw [swap]; rw [← htirrel a]; exact (ih (assignUpdate s j a) hfree').mp ha⟩
      · exact ⟨a, by rw [swap] at ha; rw [← htirrel a] at ha; exact (ih (assignUpdate s j a) hfree').mpr ha⟩

end LCS.FirstOrder.SemanticsN.Substitution
