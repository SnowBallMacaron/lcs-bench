import LCS.FirstOrder.Semantics.Subformulae.RenamingBoundVariables

section

namespace LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

helper /-- Lemma 5.3.4 (companion): Substitution of a variable free for i
agrees with updating the assignment at i to the value of that variable. -/
theorem formulaVarSubstEvalF {L : Language} (M : Structure L)
    (s : Assignment M) (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A) :
    formulaEval M (formulaSubst A (Term.var j) i) s ↔
    formulaEval M A (assignUpdate s i (s j)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | falsum => simp [formulaSubst, formulaEval]
  | pred0 _ _ => simp [formulaSubst, formulaEval]
  | predN P _ ts =>
    simp only [formulaSubst, formulaEval]
    have : (fun k => termEval M s (termSubst (ts k) (Term.var j) i)) =
           (fun k => termEval M (assignUpdate s i (s j)) (ts k)) :=
      funext fun k => termVarSubstEval M s (ts k) i j
    rw [this]
  | eq_ _ t1 t2 =>
    simp only [formulaSubst, formulaEval]
    rw [termVarSubstEval M s t1 i j, termVarSubstEval M s t2 i j]
  | conj A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact and_congr (ihA s hFree.1) (ihB s hFree.2)
  | disj A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact or_congr (ihA s hFree.1) (ihB s hFree.2)
  | impl A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact imp_congr (ihA s hFree.1) (ihB s hFree.2)
  | equiv_ A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact iff_congr (ihA s hFree.1) (ihB s hFree.2)
  | neg A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact not_congr (ih s hFree)
  | all k A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact h a
    · have hFreeA : isFreeFor (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro h a
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        rw [swap]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp (h a)
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have ha := h a
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha
  | ex k A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact ha
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact ha
    · have hFreeA : isFreeFor (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [swap, ← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp ha
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha

proof_of alphaEquivUnivF := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro h a
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mp (h a)
      · intro h a
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mpr (h a)
    · have hjNotFree : j ∉ formulaFV A := by
        intro hmem
        exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
      constructor
      · intro h a
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by
          unfold assignUpdate; simp
        rw [step2] at step1
        apply step1.mpr
        exact (coincidenceLemma M A
          (assignUpdate s i a) (assignUpdate (assignUpdate s j a) i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp (h a)
      · intro h a
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by
          unfold assignUpdate; simp
        rw [step2] at step1
        have from_subst := step1.mp (h a)
        exact (coincidenceLemma M A
          (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp from_subst

proof_of alphaEquivExF := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mp ha
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mpr ha
    · have hjNotFree : j ∉ formulaFV A := by
        intro hmem; exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
      constructor
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
        rw [step2] at step1
        apply step1.mpr
        exact (coincidenceLemma M A
          (assignUpdate s i a) (assignUpdate (assignUpdate s j a) i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp ha
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
        rw [step2] at step1
        have from_subst := step1.mp ha
        exact (coincidenceLemma M A
          (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp from_subst

end LCS.FirstOrder.Semantics.Subformulae

end
