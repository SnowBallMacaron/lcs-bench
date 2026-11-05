import LCS.FirstOrder.Semantics.Substitution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Semantics

namespace LCS.FirstOrder.Semantics.Substitution

helper /-- Definition 5.3.8 (companion): Binary sequences admit no surjective
enumeration by natural numbers, by Cantor's diagonal argument. -/
theorem binarySequences_not_countable : ¬ Nonempty (Countable (Nat → Bool)) := by
  rintro ⟨e⟩
  obtain ⟨n, hn⟩ := e.enumerate_surj (fun k => !(e.enumerate k k))
  have h := congrFun hn n
  cases hv : e.enumerate n n <;> simp [hv] at h

helper /-- Definition 5.3.8 (companion): Every signature has a structure on
binary sequences; functions and constants take the constant-false sequence,
and predicate symbols are interpreted as false. -/
def binarySequenceStructure (L : Language) : Structure L where
  carrier := Nat → Bool
  carrierNonempty := ⟨fun _ => false⟩
  interpFunc := fun _ _ _ => false
  interpConst := fun _ _ => false
  interpPred := fun _ _ => False

proof_of extendedConstants_not_countable := by
  refine ⟨binarySequenceStructure L, ?_⟩
  rintro ⟨e⟩
  letI : Countable (L.constSymbols ⊕ (Nat → Bool)) := e
  let decode : L.constSymbols ⊕ (Nat → Bool) → (Nat → Bool)
    | .inl _ => fun _ => false
    | .inr f => f
  apply binarySequences_not_countable
  exact ⟨Countable.ofSurjection decode (fun f => ⟨Sum.inr f, rfl⟩)⟩


proof_of extendedFormulae_not_countable := by
  refine ⟨binarySequenceStructure L, ?_⟩
  rintro ⟨e⟩
  letI : Countable (Formula (extendedLanguage L (Nat → Bool))) := e
  let decode : Formula (extendedLanguage L (Nat → Bool)) → (Nat → Bool)
    | .eq_ _ (.const (.inr f)) _ => f
    | .predN _ hP ts =>
      match ts ⟨0, hP⟩ with
      | .const (.inr f) => f
      | _ => fun _ => false
    | _ => fun _ => false
  apply binarySequences_not_countable
  refine ⟨Countable.ofSurjection decode ?_⟩
  intro f
  rcases h with hEq | ⟨P, hP⟩
  · exact ⟨Formula.eq_ hEq (namingConst f) (namingConst f), rfl⟩
  · exact ⟨Formula.predN P hP (fun _ => namingConst f), rfl⟩


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


helper /-- Lemma 5.3.3 (companion, consequence): For a sentence (FV = empty set), the
truth value is the same for all assignments. Since a sentence has no
free variables, the agreement condition is vacuously satisfied. -/
theorem sentenceTruthIndep {L : Language} (S : Structure L)
    (A : Formula L) (hSent : Formula.isSentence A)
    (s1 s2 : Assignment S) :
    formulaEval S A s1 ↔ formulaEval S A s2 :=
-- BEGIN PROOF
by
  exact coincidenceLemma S A s1 s2 (fun y hy => by
    have hfv : formulaFV A = ∅ := hSent
    have : ¬ (formulaFV A y) := by rw [hfv]; exact id
    exact absurd hy this)

proof_of sentenceExcludedMiddle := by
  classical
  by_cases h : validIn S A
  · exact Or.inl h
  · right
    intro s hs
    apply h
    intro s'
    exact (sentenceTruthIndep S A hSent s s').mp hs


helper /-- Pointwise excluded middle for a sentence under a fixed assignment. -/
theorem excludedMiddleAt {L : Language} (S : Structure L)
    (A : Formula L) (_hSent : Formula.isSentence A)
    (s : Assignment S) :
    formulaEval S A s ∨ formulaEval S (Formula.neg A) s :=
-- BEGIN PROOF
by
  simp [formulaEval]
  exact Classical.em (formulaEval S A s)

end LCS.FirstOrder.Semantics.Substitution
