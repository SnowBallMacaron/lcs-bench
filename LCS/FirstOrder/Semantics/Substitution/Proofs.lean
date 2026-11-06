import LCS.FirstOrder.Semantics.Substitution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Semantics

namespace LCS.FirstOrder.Semantics.Substitution

proof_of termSubstEval := by
  -- BEGIN PROOF
    induction t with
    | var x =>
      by_cases h : x = i <;>
        simp [termSubst, termEval, assignUpdate, h, namingConst, extendedInterp] <;> rfl
    | const c =>
      simp [termSubst, termEval]
    | func f ts ih =>
      simp [termSubst, termEval]
      congr 1; funext j; exact ih j


proof_of formulaSubstEval := by
  -- BEGIN PROOF
    induction A generalizing s with
    | falsum => simp [formulaSubst, formulaEval]
    | pred0 P h => simp [formulaSubst, formulaEval]
    | predN P _ ts =>
      constructor <;> intro h
      · simp only [formulaSubst, formulaEval] at h ⊢
        have : ∀ j, termEval (extendedInterp S) (assignUpdate s i m) (ts j) =
               termEval (extendedInterp S) s (termSubst (ts j) (namingConst m) i) :=
          fun j => termSubstEval S (ts j) s m i
        exact Eq.mp (congrArg (fun args => S.interpPred P args) (funext this)) h
      · simp only [formulaSubst, formulaEval] at h ⊢
        have : ∀ j, termEval (extendedInterp S) (assignUpdate s i m) (ts j) =
               termEval (extendedInterp S) s (termSubst (ts j) (namingConst m) i) :=
          fun j => termSubstEval S (ts j) s m i
        exact Eq.mpr (congrArg (fun args => S.interpPred P args) (funext this)) h
    | eq_ _ t1 t2 =>
      simp [formulaSubst, formulaEval]
      constructor <;> intro h
      · rw [← termSubstEval S t1 s m i, ← termSubstEval S t2 s m i]; exact h
      · rw [termSubstEval S t1 s m i, termSubstEval S t2 s m i]; exact h
    | conj A B ihA ihB =>
      simp [formulaSubst, formulaEval]; exact and_congr (ihA s) (ihB s)
    | disj A B ihA ihB =>
      simp [formulaSubst, formulaEval]; exact or_congr (ihA s) (ihB s)
    | impl A B ihA ihB =>
      simp [formulaSubst, formulaEval]; exact imp_congr (ihA s) (ihB s)
    | equiv_ A B ihA ihB =>
      simp [formulaSubst, formulaEval]; exact iff_congr (ihA s) (ihB s)
    | neg A ih =>
      simp [formulaSubst, formulaEval]; exact not_congr (ih s)
    | all j A ih =>
      simp [formulaSubst, formulaEval]
      by_cases hij : i = j
      · subst hij; simp; constructor <;> intro h a
        · have := h a
          rwa [show assignUpdate (assignUpdate s i m) i a = assignUpdate s i a from
            funext fun k => by unfold assignUpdate; split <;> simp_all] at this
        · rw [show assignUpdate (assignUpdate s i m) i a = assignUpdate s i a from
            funext fun k => by unfold assignUpdate; split <;> simp_all]
          exact h a
      · simp [hij]
        have swap : ∀ (a : (extendedInterp S).carrier),
            assignUpdate (assignUpdate s i m) j a =
              assignUpdate (assignUpdate s j a) i m :=
          fun a => funext fun k => by
            by_cases hki : k = i <;> by_cases hkj : k = j <;>
              simp_all [assignUpdate] <;> rfl
        constructor <;> intro h a
        · have h' := h a; rw [swap] at h'; exact (ih (assignUpdate s j a)).mp h'
        · rw [show assignUpdate (assignUpdate s i m) j a =
                assignUpdate (assignUpdate s j a) i m from swap a]
          exact (ih (assignUpdate s j a)).mpr (h a)
    | ex j A ih =>
      simp [formulaSubst, formulaEval]
      by_cases hij : i = j
      · subst hij; simp; constructor <;> intro ⟨a, ha⟩ <;> exact ⟨a, by
          rwa [show assignUpdate (assignUpdate s i m) i a = assignUpdate s i a from
            funext fun k => by unfold assignUpdate; split <;> simp_all] at *⟩
      · simp [hij]
        have swap : ∀ (a : (extendedInterp S).carrier),
            assignUpdate (assignUpdate s i m) j a =
              assignUpdate (assignUpdate s j a) i m :=
          fun a => funext fun k => by
            by_cases hki : k = i <;> by_cases hkj : k = j <;>
              simp_all [assignUpdate] <;> rfl
        constructor <;> intro ⟨a, ha⟩
        · rw [swap a] at ha; exact ⟨a, (ih (assignUpdate s j a)).mp ha⟩
        · refine ⟨a, ?_⟩; rw [swap a]; exact (ih (assignUpdate s j a)).mpr ha


proof_of forallSemantics := by
  -- BEGIN PROOF
    constructor
    · intro h m
      exact (formulaSubstEval S B s m i).mp (h m)
    · intro h m
      exact (formulaSubstEval S B s m i).mpr (h m)


proof_of existsSemantics := by
  -- BEGIN PROOF
    constructor
    · intro ⟨m, hm⟩; exact ⟨m, (formulaSubstEval S B s m i).mp hm⟩
    · intro ⟨m, hm⟩; exact ⟨m, (formulaSubstEval S B s m i).mpr hm⟩


helper /-- Helper for Lemma 5.3.3: term evaluation depends only on the values
of free variables in the term. -/
theorem termCoincidence {L : Language} (S : Structure L)
    (t : Term L) (s1 s2 : Assignment S)
    (h : ∀ y, y ∈ termFV t → s1 y = s2 y) :
    termEval S s1 t = termEval S s2 t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp [termEval]
    exact h x rfl
  | const c =>
    simp [termEval]
  | func f ts ih =>
    simp [termEval]
    congr 1; funext j
    exact ih j (fun y hy => h y ⟨j, hy⟩)

proof_of coincidenceLemma := by
  -- BEGIN PROOF
    induction A generalizing s1 s2 with
    | falsum => simp [formulaEval]
    | pred0 P hp => simp [formulaEval]
    | predN P _ ts =>
      simp only [formulaEval]
      have : (fun i => termEval S s1 (ts i)) = (fun i => termEval S s2 (ts i)) := by
        funext j; exact termCoincidence S (ts j) s1 s2 (fun y hy => h y ⟨j, hy⟩)
      rw [this]
    | eq_ _ t1 t2 =>
      simp only [formulaEval]
      rw [termCoincidence S t1 s1 s2 (fun y hy => h y (Or.inl hy)),
          termCoincidence S t2 s1 s2 (fun y hy => h y (Or.inr hy))]
    | conj A B ihA ihB =>
      simp only [formulaEval]
      exact and_congr
        (ihA _ _ fun y hy => h y (Or.inl hy))
        (ihB _ _ fun y hy => h y (Or.inr hy))
    | disj A B ihA ihB =>
      simp only [formulaEval]
      exact or_congr
        (ihA _ _ fun y hy => h y (Or.inl hy))
        (ihB _ _ fun y hy => h y (Or.inr hy))
    | impl A B ihA ihB =>
      simp only [formulaEval]
      exact imp_congr
        (ihA _ _ fun y hy => h y (Or.inl hy))
        (ihB _ _ fun y hy => h y (Or.inr hy))
    | equiv_ A B ihA ihB =>
      simp only [formulaEval]
      exact iff_congr
        (ihA _ _ fun y hy => h y (Or.inl hy))
        (ihB _ _ fun y hy => h y (Or.inr hy))
    | neg A ih =>
      simp only [formulaEval]
      exact not_congr (ih _ _ h)
    | all j A ih =>
      simp only [formulaEval]; constructor <;> intro ha a
      · exact (ih _ _ (fun y hy => by
          show assignUpdate s1 j a y = assignUpdate s2 j a y
          unfold assignUpdate; split
          · rfl
          · rename_i hne; exact h y ⟨hy, hne⟩)).mp (ha a)
      · exact (ih _ _ (fun y hy => by
          show assignUpdate s1 j a y = assignUpdate s2 j a y
          unfold assignUpdate; split
          · rfl
          · rename_i hne; exact h y ⟨hy, hne⟩)).mpr (ha a)
    | ex j A ih =>
      simp only [formulaEval]; constructor <;> intro ⟨a, ha⟩
      · exact ⟨a, (ih _ _ (fun y hy => by
          show assignUpdate s1 j a y = assignUpdate s2 j a y
          unfold assignUpdate; split
          · rfl
          · rename_i hne; exact h y ⟨hy, hne⟩)).mp ha⟩
      · exact ⟨a, (ih _ _ (fun y hy => by
          show assignUpdate s1 j a y = assignUpdate s2 j a y
          unfold assignUpdate; split
          · rfl
          · rename_i hne; exact h y ⟨hy, hne⟩)).mpr ha⟩

end LCS.FirstOrder.Semantics.Substitution
