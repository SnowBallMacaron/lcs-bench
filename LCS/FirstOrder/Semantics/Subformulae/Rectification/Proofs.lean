import LCS.FirstOrder.Semantics.Subformulae.Rectification

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

helper /-- Example 5.3.3: The displayed formula B is rectified: its free and
bound variables are disjoint, and its quantifier variables are distinct. -/
theorem exampleRectified_5_3_3_isRectified :
    isRectified exampleRectified_5_3_3 := by
  constructor
  · intro x
    dsimp [boundVarsFresh, exampleRectified_5_3_3, formulaFVN, formulaBVN,
      termFV, exampleLang_5_3_3, Set.iUnion, Set.union, Set.diff,
      Set.singleton, Set.empty, Membership.mem]
    simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
    rintro ⟨hFV, hBV⟩
    simp only [false_or] at hBV
    rcases hBV with rfl | rfl | rfl <;> simp at hFV
  · simp [distinctQuantifierBindings, exampleRectified_5_3_3, formulaBVN,
      Membership.mem, Set.union, Set.singleton, Set.empty]

proof_of exampleRectified_5_3_3_equiv := by
  intro M s
  have evalPair (t : Assignment M) (x y : Nat) :
      (fun i : Fin (exampleLang_5_3_3.predArity ExPred_5_3_3.R) => termEval M t (vec2 (Term.var x) (Term.var y) i)) =
        vec2 (t x) (t y) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  simp [exampleNonRectified_5_3_3, exampleRectified_5_3_3, formulaEvalN,
    evalPair, termEval, assignUpdate]

end LCS.FirstOrder.Semantics.Subformulae

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

helper /-- Lemma 5.3.4 (companion): The rectification traversal never decreases its counter. -/
theorem rectifyAuxF_counter_le {L : Language} (A : Formula L)
    (sigma : Nat → Nat) (n : Nat) :
    n ≤ (rectifyAuxF A sigma n).2 := by
-- BEGIN PROOF
  induction A generalizing sigma n with
  | falsum | pred0 _ _ | predN _ _ _ | eq_ _ _ _ => simp [rectifyAuxF]
  | neg A ih => exact ih sigma n
  | conj A B ihA ihB | disj A B ihA ihB
  | impl A B ihA ihB | equiv_ A B ihA ihB =>
    exact Nat.le_trans (ihA sigma n) (ihB sigma _)
  | all i A ih | ex i A ih =>
    exact Nat.le_trans (Nat.le_succ n) (ih _ (n + 1))

helper /-- Lemma 5.3.4 (companion): Every free variable index is bounded by formulaMaxVarF. -/
theorem formulaFV_le_maxVarF {L : Language} (A : Formula L) :
    ∀ x, x ∈ formulaFV A → x ≤ formulaMaxVarF A := by
-- BEGIN PROOF
  induction A with
  | falsum | pred0 _ _ =>
    intro x hx; exact hx.elim
  | predN P _ ts =>
    intro x hx; simp only [formulaFV] at hx
    obtain ⟨j, hj⟩ := hx
    unfold formulaMaxVarF
    exact Nat.le_trans (termFV_le_maxVar (ts j) x hj)
      (finMax_ge _ (fun j => termMaxVar (ts j)) j)
  | eq_ _ t1 t2 =>
    intro x hx; simp only [formulaFV] at hx
    rcases hx with h1 | h2
    · exact Nat.le_trans (termFV_le_maxVar t1 x h1)
        (Nat.le_max_left _ _)
    · exact Nat.le_trans (termFV_le_maxVar t2 x h2)
        (Nat.le_max_right _ _)
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro x hx; simp only [formulaFV] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | disj A B ihA ihB =>
    intro x hx; simp only [formulaFV] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    intro x hx; simp only [formulaFV] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | equiv_ A B ihA ihB =>
    intro x hx; simp only [formulaFV] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | all i A ih =>
    intro x hx; simp only [formulaFV] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)
  | ex i A ih =>
    intro x hx; simp only [formulaFV] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)

helper /-- Lemma 5.3.4 (companion): Evaluation of the Formula rectification
traversal agrees with evaluation under the renamed assignment, when the
initial counter is greater than every renamed free-variable index. -/
theorem rectifyAuxF_eval {L : Language} (A : Formula L)
    (sigma : Nat → Nat) (n : Nat)
    (hFresh : ∀ x, x ∈ formulaFV A → sigma x < n)
    (M : Structure L) (s : Assignment M) :
    formulaEval M (rectifyAuxF A sigma n).1 s ↔
    formulaEval M A (fun x => s (sigma x)) := by
-- BEGIN PROOF
  induction A generalizing sigma n s with
  | falsum | pred0 _ _ => simp [rectifyAuxF, formulaEval]
  | predN P _ ts =>
    simp only [rectifyAuxF, formulaEval]
    constructor <;> intro h
    · have : (fun i => termEval M s (termVarMap sigma (ts i))) =
          (fun i => termEval M (fun x => s (sigma x)) (ts i)) :=
        funext (fun j => termVarMap_eval M s sigma (ts j))
      rw [this] at h; exact h
    · have : (fun i => termEval M s (termVarMap sigma (ts i))) =
          (fun i => termEval M (fun x => s (sigma x)) (ts i)) :=
        funext (fun j => termVarMap_eval M s sigma (ts j))
      rw [this]; exact h
  | eq_ _ t1 t2 =>
    simp only [rectifyAuxF, formulaEval]
    rw [termVarMap_eval, termVarMap_eval]
  | neg A ih =>
    simp only [rectifyAuxF, formulaEval]
    exact not_congr (ih sigma n hFresh s)
  | conj A B ihA ihB =>
    simp only [rectifyAuxF, formulaEval]
    exact and_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAuxF_counter_le A sigma n)) s)
  | disj A B ihA ihB =>
    simp only [rectifyAuxF, formulaEval]
    exact or_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAuxF_counter_le A sigma n)) s)
  | impl A B ihA ihB =>
    simp only [rectifyAuxF, formulaEval]
    exact imp_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAuxF_counter_le A sigma n)) s)
  | equiv_ A B ihA ihB =>
    simp only [rectifyAuxF, formulaEval]
    exact iff_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAuxF_counter_le A sigma n)) s)
  | all i A ih =>
    simp only [rectifyAuxF, formulaEval]
    let sigma' := funUpdate sigma i n
    have hFresh' : ∀ x, x ∈ formulaFV A → sigma' x < n + 1 := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; simp [sigma', funUpdate]
      · simp [sigma', funUpdate, hxi]
        exact Nat.lt_succ_of_lt (hFresh x ⟨hx, hxi⟩)
    constructor <;> intro h a
    · have step := (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mp (h a)
      exact (coincidenceLemma M A
        (fun x => (assignUpdate s n a) (sigma' x))
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp step
    · apply (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mpr
      exact (coincidenceLemma M A
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun x => (assignUpdate s n a) (sigma' x))
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp (h a)
  | ex i A ih =>
    simp only [rectifyAuxF, formulaEval]
    let sigma' := funUpdate sigma i n
    have hFresh' : ∀ x, x ∈ formulaFV A → sigma' x < n + 1 := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; simp [sigma', funUpdate]
      · simp [sigma', funUpdate, hxi]
        exact Nat.lt_succ_of_lt (hFresh x ⟨hx, hxi⟩)
    constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
    · have step := (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mp ha
      exact (coincidenceLemma M A
        (fun x => (assignUpdate s n a) (sigma' x))
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp step
    · apply (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mpr
      exact (coincidenceLemma M A
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun x => (assignUpdate s n a) (sigma' x))
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp ha

proof_of rectifyF_equiv := by
  -- BEGIN PROOF
    intro M s
    change formulaEval M A s ↔
      formulaEval M (rectifyAuxF A id (formulaMaxVarF A + 1)).1 s
    have hFresh : ∀ x, x ∈ formulaFV A → id x < formulaMaxVarF A + 1 := by
      intro x hx
      exact Nat.lt_succ_of_le (formulaFV_le_maxVarF A x hx)
    exact (rectifyAuxF_eval A id (formulaMaxVarF A + 1) hFresh M s).symm

end LCS.FirstOrder.Semantics.Subformulae

end
