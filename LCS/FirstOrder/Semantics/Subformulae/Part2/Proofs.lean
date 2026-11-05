import LCS.FirstOrder.Semantics.Subformulae.Part2

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

helper /-- Lemma 5.3.4 (companion, Part i, universal): For every formula A,
variable x (index i), and variable y (index j) where y is free for x
in A and j is not in FV(A) minus {i}, the formula (forall x A) is
semantically equivalent to (forall y A[y/x]). That is,
|= (forall x_i A) equiv (forall x_j A[x_j/x_i]). -/
theorem alphaEquivUniv {L : Language} (A : FormulaN L)
    (i j : Nat)
    (hFree : isFreeForN (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFVN A \ Set.singleton i))) :
    universallyValidN
      (FormulaN.conj
        (FormulaN.impl
          (FormulaN.all i A)
          (FormulaN.all j (formulaSubstN A (Term.var j) i)))
        (FormulaN.impl
          (FormulaN.all j (formulaSubstN A (Term.var j) i))
          (FormulaN.all i A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  by_cases hij : i = j
  · subst hij
    constructor
    · intro h a
      have key := (formulaVarSubstEvalN M (assignUpdate s i a) A i i hFree).symm
      have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
      rw [this] at key
      have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
        funext fun x => by unfold assignUpdate; split <;> simp_all
      rw [idem] at key; exact key.mp (h a)
    · intro h a
      have key := (formulaVarSubstEvalN M (assignUpdate s i a) A i i hFree).symm
      have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
      rw [this] at key
      have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
        funext fun x => by unfold assignUpdate; split <;> simp_all
      rw [idem] at key; exact key.mpr (h a)
  · have hjNotFree : j ∉ formulaFVN A := by
      intro hmem
      exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
    constructor
    · intro h a
      have step1 := formulaVarSubstEvalN M (assignUpdate s j a) A i j hFree
      have step2 : (assignUpdate s j a) j = a := by
        unfold assignUpdate; simp
      rw [step2] at step1
      apply step1.mpr
      exact (coincidenceLemmaN M A
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
      have step1 := formulaVarSubstEvalN M (assignUpdate s j a) A i j hFree
      have step2 : (assignUpdate s j a) j = a := by
        unfold assignUpdate; simp
      rw [step2] at step1
      have from_subst := step1.mp (h a)
      exact (coincidenceLemmaN M A
        (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
        (fun y hy => by
          unfold assignUpdate
          by_cases hyi : y = i
          · subst hyi; simp
          · simp [hyi]
            by_cases hyj : y = j
            · subst hyj; exact absurd hy hjNotFree
            · simp [hyj])).mp from_subst

helper /-- Lemma 5.3.4 (companion, Part i, existential): For every formula A,
variable x (index i), and variable y (index j) where y is free for x
in A and j is not in FV(A) minus {i}, the formula (exists x A) is
semantically equivalent to (exists y A[y/x]). That is,
|= (exists x_i A) equiv (exists x_j A[x_j/x_i]). -/
theorem alphaEquivEx {L : Language} (A : FormulaN L)
    (i j : Nat)
    (hFree : isFreeForN (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFVN A \ Set.singleton i))) :
    universallyValidN
      (FormulaN.conj
        (FormulaN.impl
          (FormulaN.ex i A)
          (FormulaN.ex j (formulaSubstN A (Term.var j) i)))
        (FormulaN.impl
          (FormulaN.ex j (formulaSubstN A (Term.var j) i))
          (FormulaN.ex i A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  by_cases hij : i = j
  · subst hij
    constructor
    · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
      have key := (formulaVarSubstEvalN M (assignUpdate s i a) A i i hFree).symm
      have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
      rw [this] at key
      have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
        funext fun x => by unfold assignUpdate; split <;> simp_all
      rw [idem] at key; exact key.mp ha
    · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
      have key := (formulaVarSubstEvalN M (assignUpdate s i a) A i i hFree).symm
      have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
      rw [this] at key
      have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
        funext fun x => by unfold assignUpdate; split <;> simp_all
      rw [idem] at key; exact key.mpr ha
  · have hjNotFree : j ∉ formulaFVN A := by
      intro hmem; exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
    constructor
    · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
      have step1 := formulaVarSubstEvalN M (assignUpdate s j a) A i j hFree
      have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
      rw [step2] at step1
      apply step1.mpr
      exact (coincidenceLemmaN M A
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
      have step1 := formulaVarSubstEvalN M (assignUpdate s j a) A i j hFree
      have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
      rw [step2] at step1
      have from_subst := step1.mp ha
      exact (coincidenceLemmaN M A
        (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
        (fun y hy => by
          unfold assignUpdate
          by_cases hyi : y = i
          · subst hyi; simp
          · simp [hyi]
            by_cases hyj : y = j
            · subst hyj; exact absurd hy hjNotFree
            · simp [hyj])).mp from_subst























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

helper /-- Lemma 5.3.4 (companion): Every bound variable in the traversal output lies between
the initial counter and the next unused counter. -/
theorem rectifyAuxF_bv_range {L : Language} (A : Formula L)
    (sigma : Nat → Nat) (ctr : Nat) :
    ∀ x, x ∈ formulaBV (rectifyAuxF A sigma ctr).1 →
      ctr ≤ x ∧ x < (rectifyAuxF A sigma ctr).2 := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | falsum | pred0 _ _ | predN _ _ _ =>
    intro x hx; unfold rectifyAuxF formulaBV at hx; exact absurd hx id
  | eq_ _ _ _ =>
    intro x hx; unfold rectifyAuxF formulaBV at hx; exact absurd hx id
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB | disj A B ihA ihB
  | impl A B ihA ihB | equiv_ A B ihA ihB =>
    intro x hx; unfold rectifyAuxF at hx; simp only [formulaBV] at hx
    rcases hx with hxA | hxB
    · exact ⟨(ihA sigma ctr x hxA).1,
        Nat.lt_of_lt_of_le (ihA sigma ctr x hxA).2
          (rectifyAuxF_counter_le B sigma _)⟩
    · exact ⟨Nat.le_trans (rectifyAuxF_counter_le A sigma ctr)
          (ihB sigma _ x hxB).1, (ihB sigma _ x hxB).2⟩
  | all i A ih =>
    intro x hx
    let body := (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).1
    let ctr' := (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).2
    have hx' : x ∈ formulaBV body ∨ x = ctr := by
      change x ∈ formulaBV (Formula.all ctr body) at hx
      simp only [formulaBV] at hx; exact hx
    have goal_snd : (rectifyAuxF (Formula.all i A) sigma ctr).2 = ctr' :=
      rfl
    rw [goal_snd]
    rcases hx' with hBody | hEq
    · have := ih (funUpdate sigma i ctr) (ctr + 1) x hBody; omega
    · rw [hEq]; constructor; · omega
      · exact Nat.lt_of_lt_of_le (Nat.lt_add_one ctr)
          (rectifyAuxF_counter_le A _ (ctr + 1))
  | ex i A ih =>
    intro x hx
    let body := (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).1
    let ctr' := (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).2
    have hx' : x ∈ formulaBV body ∨ x = ctr := by
      change x ∈ formulaBV (Formula.ex ctr body) at hx
      simp only [formulaBV] at hx; exact hx
    have goal_snd : (rectifyAuxF (Formula.ex i A) sigma ctr).2 = ctr' :=
      rfl
    rw [goal_snd]
    rcases hx' with hBody | hEq
    · have := ih (funUpdate sigma i ctr) (ctr + 1) x hBody; omega
    · rw [hEq]; constructor; · omega
      · exact Nat.lt_of_lt_of_le (Nat.lt_add_one ctr)
          (rectifyAuxF_counter_le A _ (ctr + 1))

helper /-- Lemma 5.3.4 (companion): The traversal assigns distinct indices to all quantifier
occurrences, including vacuous quantifiers. -/
theorem rectifyAuxF_dqb {L : Language} (A : Formula L)
    (sigma : Nat → Nat) (ctr : Nat) :
    distinctQuantifierBindingsF (rectifyAuxF A sigma ctr).1 := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | falsum | pred0 _ _ | predN _ _ _ | eq_ _ _ _ => exact trivial
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB =>
    suffices h : distinctQuantifierBindingsF (Formula.conj
        (rectifyAuxF A sigma ctr).1
        (rectifyAuxF B sigma (rectifyAuxF A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAuxF_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAuxF_bv_range B sigma
      (rectifyAuxF A sigma ctr).2 x hxB).1
    omega
  | disj A B ihA ihB =>
    suffices h : distinctQuantifierBindingsF (Formula.disj
        (rectifyAuxF A sigma ctr).1
        (rectifyAuxF B sigma (rectifyAuxF A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAuxF_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAuxF_bv_range B sigma
      (rectifyAuxF A sigma ctr).2 x hxB).1
    omega
  | impl A B ihA ihB =>
    suffices h : distinctQuantifierBindingsF (Formula.impl
        (rectifyAuxF A sigma ctr).1
        (rectifyAuxF B sigma (rectifyAuxF A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAuxF_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAuxF_bv_range B sigma
      (rectifyAuxF A sigma ctr).2 x hxB).1
    omega
  | equiv_ A B ihA ihB =>
    suffices h : distinctQuantifierBindingsF (Formula.equiv_
        (rectifyAuxF A sigma ctr).1
        (rectifyAuxF B sigma (rectifyAuxF A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAuxF_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAuxF_bv_range B sigma
      (rectifyAuxF A sigma ctr).2 x hxB).1
    omega
  | all i A ih =>
    suffices h : distinctQuantifierBindingsF (Formula.all ctr
        (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ih _ _, fun hBVn => ?_⟩
    have := (rectifyAuxF_bv_range A (funUpdate sigma i ctr)
      (ctr + 1) ctr hBVn).1; omega
  | ex i A ih =>
    suffices h : distinctQuantifierBindingsF (Formula.ex ctr
        (rectifyAuxF A (funUpdate sigma i ctr) (ctr + 1)).1) from h
    simp only [distinctQuantifierBindingsF]
    refine ⟨ih _ _, fun hBVn => ?_⟩
    have := (rectifyAuxF_bv_range A (funUpdate sigma i ctr)
      (ctr + 1) ctr hBVn).1; omega

helper /-- Lemma 5.3.4 (companion): Every free variable in the traversal output is the image
under sigma of a free variable in its input. -/
theorem rectifyAuxF_fv_source {L : Language} (A : Formula L)
    (sigma : Nat → Nat) (ctr : Nat) :
    ∀ x, x ∈ formulaFV (rectifyAuxF A sigma ctr).1 →
      ∃ y, y ∈ formulaFV A ∧ x = sigma y := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | falsum | pred0 _ _ =>
    intro x hx; exact hx.elim
  | predN P hP ts =>
    intro x hx
    change x ∈ formulaFV (Formula.predN P hP
      (fun j => termVarMap sigma (ts j))) at hx
    simp only [formulaFV] at hx
    obtain ⟨j, hj⟩ := hx
    obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma (ts j) x hj
    exact ⟨y, ⟨j, hy⟩, hxy⟩
  | eq_ hL t1 t2 =>
    intro x hx
    change x ∈ formulaFV (Formula.eq_ hL (termVarMap sigma t1)
      (termVarMap sigma t2)) at hx
    simp only [formulaFV] at hx
    rcases hx with h1 | h2
    · obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma t1 x h1
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma t2 x h2
      exact ⟨y, Or.inr hy, hxy⟩
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB =>
    intro x hx; unfold rectifyAuxF at hx; simp only [formulaFV] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | disj A B ihA ihB =>
    intro x hx; unfold rectifyAuxF at hx; simp only [formulaFV] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | impl A B ihA ihB =>
    intro x hx; unfold rectifyAuxF at hx; simp only [formulaFV] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | equiv_ A B ihA ihB =>
    intro x hx; unfold rectifyAuxF at hx; simp only [formulaFV] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | all i A ih =>
    intro x hx
    let sigma' := funUpdate sigma i ctr
    change x ∈ formulaFV (Formula.all ctr
      (rectifyAuxF A sigma' (ctr + 1)).1) at hx
    simp only [formulaFV] at hx
    obtain ⟨hFV, hNeq⟩ := hx
    obtain ⟨y, hy, hxy⟩ := ih sigma' (ctr + 1) x hFV
    by_cases hyi : y = i
    · subst hyi; simp [sigma', funUpdate] at hxy
      exact absurd hxy hNeq
    · refine ⟨y, ⟨hy, hyi⟩, ?_⟩
      simp [sigma', funUpdate, hyi] at hxy; exact hxy
  | ex i A ih =>
    intro x hx
    let sigma' := funUpdate sigma i ctr
    change x ∈ formulaFV (Formula.ex ctr
      (rectifyAuxF A sigma' (ctr + 1)).1) at hx
    simp only [formulaFV] at hx
    obtain ⟨hFV, hNeq⟩ := hx
    obtain ⟨y, hy, hxy⟩ := ih sigma' (ctr + 1) x hFV
    by_cases hyi : y = i
    · subst hyi; simp [sigma', funUpdate] at hxy
      exact absurd hxy hNeq
    · refine ⟨y, ⟨hy, hyi⟩, ?_⟩
      simp [sigma', funUpdate, hyi] at hxy; exact hxy

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

helper /-- Lemma 5.3.4 (companion): The computed output of rectifyF satisfies both
conditions of isRectifiedF. -/
theorem rectifyF_isRectified {L : Language} (A : Formula L) :
    isRectifiedF (rectifyF A) := by
-- BEGIN PROOF
  unfold isRectifiedF rectifyF
  constructor
  · -- boundVarsFreshF: FV ∩ BV = ∅
    intro x ⟨hFV, hBV⟩
    have hBV_ge := (rectifyAuxF_bv_range A id (formulaMaxVarF A + 1)
      x hBV).1
    obtain ⟨y, hyFV, hxy⟩ := rectifyAuxF_fv_source A id
      (formulaMaxVarF A + 1) x hFV
    -- hxy : x = id y, i.e., x = y
    have hxy' : x = y := hxy
    have hle := formulaFV_le_maxVarF A y hyFV
    omega
  · -- distinctQuantifierBindingsF
    exact rectifyAuxF_dqb A id (formulaMaxVarF A + 1)





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




helper /-- Proof of Lemma 5.3.5: Evaluating a propositional substitution agrees
with the valuation that evaluates each substituted first-order formula. -/
theorem propSubst_correspondence {L : Language} (M : Structure L)
    (s : Assignment M) (sigma : PS0 L → Formula L)
    (B : PropFormulaOver (PS0 L)) :
    evalProp (fun p => formulaEval M (sigma p) s) B ↔
      formulaEval M (propSubst sigma B) s := by
  induction B with
  | fls => exact Iff.rfl
  | var p => exact Iff.rfl
  | neg B ih => exact not_congr ih
  | conj B C ihB ihC => exact and_congr ihB ihC
  | disj B C ihB ihC => exact or_congr ihB ihC
  | impl B C ihB ihC => exact imp_congr ihB ihC
  | equiv_ B C ihB ihC => exact iff_congr ihB ihC

proof_of propInstanceValid := by
  rintro ⟨B, sigma, hValid, rfl⟩ M s
  exact (propSubst_correspondence M s sigma B).mp
    (hValid (fun p => formulaEval M (sigma p) s))


helper /-- Structural induction correspondence
between normalized propositional evaluation and first-order evaluation
under a substitution sigma. For a normalized propositional formula C
and valuation v agreeing with sigma, evalExtN v C = T iff
formulaEvalN M (propSubstN sigma C) s. Used in the proof of
propInstanceValidN. -/
theorem propSubstN_correspondence {L : Language} (M : Structure L)
    (s : Assignment M) (sigma : Nat → FormulaN L) (v : Valuation)
    (hv : ∀ n, v n = BoolVal.T ↔ formulaEvalN M (sigma n) s)
    (C : PropFormulaNormalized) :
    evalExtN v C = BoolVal.T ↔ formulaEvalN M (propSubstN sigma C) s :=
-- BEGIN PROOF
by
  induction C with
  | var n => exact hv n
  | neg C ih =>
    simp only [evalExtN, propSubstN, formulaEvalN, Basic.negM]
    rw [show (¬formulaEvalN M (propSubstN sigma C) s) ↔
          ¬(evalExtN v C = BoolVal.T) from not_congr ih.symm]
    cases evalExtN v C <;> simp [hNeg]
  | conj C D ihC ihD =>
    simp only [evalExtN, propSubstN, formulaEvalN, Basic.andM]
    rw [show formulaEvalN M (propSubstN sigma C) s ↔
          (evalExtN v C = BoolVal.T) from ihC.symm,
        show formulaEvalN M (propSubstN sigma D) s ↔
          (evalExtN v D = BoolVal.T) from ihD.symm]
    cases evalExtN v C <;> cases evalExtN v D <;> simp [hAnd]
  | disj C D ihC ihD =>
    simp only [evalExtN, propSubstN, formulaEvalN, Basic.orM]
    rw [show formulaEvalN M (propSubstN sigma C) s ↔
          (evalExtN v C = BoolVal.T) from ihC.symm,
        show formulaEvalN M (propSubstN sigma D) s ↔
          (evalExtN v D = BoolVal.T) from ihD.symm]
    cases evalExtN v C <;> cases evalExtN v D <;> simp [hOr]
  | impl C D ihC ihD =>
    simp only [evalExtN, propSubstN, formulaEvalN, Basic.implM]
    rw [show formulaEvalN M (propSubstN sigma C) s ↔
          (evalExtN v C = BoolVal.T) from ihC.symm,
        show formulaEvalN M (propSubstN sigma D) s ↔
          (evalExtN v D = BoolVal.T) from ihD.symm]
    cases evalExtN v C <;> cases evalExtN v D <;> simp [hImplies]

helper /-- Every first-order FormulaN that is a tautology instance
(isPropInstanceN A) is universally valid. -/
theorem propInstanceValidN {L : Language} (A : FormulaN L)
    (hInst : isPropInstanceN A) :
    universallyValidN A :=
-- BEGIN PROOF
by
  obtain ⟨B, sigma, hValid, rfl⟩ := hInst
  intro M s
  have dec := Classical.propDecidable
  let v : Valuation := fun n =>
    if formulaEvalN M (sigma n) s then BoolVal.T else BoolVal.F
  have hv : ∀ n, v n = BoolVal.T ↔ formulaEvalN M (sigma n) s := by
    intro n; simp only [v]
    by_cases h : formulaEvalN M (sigma n) s
    · simp [h]
    · simp [h]
  exact (propSubstN_correspondence M s sigma v hv B).mp (hValid v)

end LCS.FirstOrder.Semantics.Subformulae

end
