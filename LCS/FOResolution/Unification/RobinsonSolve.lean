import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers
import LCS.FOResolution.Unification.RobinsonStep

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

/-- Membership in the variable-index accumulator used by
    `termVarIndicesList`. -/
theorem mem_foldl_append_termVarIndices {L : Language} (x : Nat)
    {β : Type} (f : β → Term L) :
    ∀ (indices : List β) (acc : List Nat),
      x ∈ indices.foldl
          (fun vars i => vars ++ termVarIndicesList (f i)) acc ↔
        x ∈ acc ∨ ∃ i ∈ indices, x ∈ termVarIndicesList (f i) := by
-- BEGIN PROOF
  intro indices
  induction indices with
  | nil =>
      intro acc
      simp
  | cons i indices ih =>
      intro acc
      simp only [List.foldl]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro ((hx | hx) | ⟨j, hj, hx⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨i, Or.inl rfl, hx⟩
        · exact Or.inr ⟨j, Or.inr hj, hx⟩
      · rintro (hx | ⟨j, rfl | hj, hx⟩)
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨j, hj, hx⟩

/-- The computable variable-index list of a term enumerates exactly its free
    variables. -/
theorem mem_termVarIndicesList_iff {L : Language}
    (t : Term L) (x : Nat) :
    x ∈ termVarIndicesList t ↔ termFV t x := by
-- BEGIN PROOF
  induction t with
  | var y =>
      simp only [termVarIndicesList, List.mem_singleton, termFV]
      change x = y ↔ x = y
      rfl
  | const c =>
      simp [termVarIndicesList, termFV, Set.empty]
  | func f args ih =>
      simp only [termVarIndicesList]
      constructor
      · intro hx
        rcases (mem_foldl_append_termVarIndices x args _ []).mp hx with
          hx | ⟨i, _, hi⟩
        · exact (List.not_mem_nil hx).elim
        · exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        apply (mem_foldl_append_termVarIndices x args _ []).mpr
        exact Or.inr
          ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, (ih i).mpr hi⟩

/-- Variable indices occurring in a finite equation system, before duplicate
    removal. -/
def equationVarIndicesList {L : Language} :
    List (Term L × Term L) → List Nat
  | [] => []
  | (s, t) :: rest =>
      (termVarIndicesList s ++ termVarIndicesList t) ++
        equationVarIndicesList rest

/-- The duplicate-free list of variables occurring in a finite equation
    system. -/
def equationVariables {L : Language}
    (equations : List (Term L × Term L)) : List Nat :=
  (equationVarIndicesList equations).eraseDups

/-- The number of distinct variables occurring in an equation system. -/
def equationVariableCount {L : Language}
    (equations : List (Term L × Term L)) : Nat :=
  (equationVariables equations).length

/-- Total structural term complexity on both sides of an equation system. -/
def equationComplexity {L : Language} :
    List (Term L × Term L) → Nat
  | [] => 0
  | (s, t) :: rest =>
      termSize s + termSize t + equationComplexity rest

/-- The final component of the Robinson measure. It is one exactly when the
    head equation has a non-variable on the left and a variable on the right,
    so an orientation step changes it to zero. -/
def robinsonOrientationPenalty {L : Language} :
    List (Term L × Term L) → Nat
  | (Term.const _, Term.var _) :: _ => 1
  | (Term.func _ _, Term.var _) :: _ => 1
  | _ => 0

/-- Lexicographic termination measure for Robinson simplification:
    distinct variables, then total term complexity, then orientation. -/
def robinsonMeasure {L : Language}
    (equations : List (Term L × Term L)) : Nat × Nat × Nat :=
  (equationVariableCount equations, equationComplexity equations,
    robinsonOrientationPenalty equations)

/-- The explicit lexicographic decrease relation induced by
    `robinsonMeasure`. -/
def RobinsonMeasureDecreases {L : Language}
    (next current : List (Term L × Term L)) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (robinsonMeasure next) (robinsonMeasure current)

theorem equationVarIndicesList_mem_iff {L : Language}
    (equations : List (Term L × Term L)) (x : Nat) :
    x ∈ equationVarIndicesList equations ↔
      termPairSetVars equations x := by
-- BEGIN PROOF
  induction equations with
  | nil =>
      simp [equationVarIndicesList, termPairSetVars]
  | cons p rest ih =>
      rcases p with ⟨s, t⟩
      simp only [equationVarIndicesList, List.mem_append,
        mem_termVarIndicesList_iff, ih, termPairSetVars_cons_iff]

theorem eraseDups_nodup_nat (l : List Nat) :
    l.eraseDups.Nodup := by
-- BEGIN PROOF
  suffices h : ∀ (n : Nat) (l : List Nat),
      l.length ≤ n → l.eraseDups.Nodup by
    exact h l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro l hLen
      cases l with
      | nil => exact List.nodup_nil
      | cons _ _ => simp at hLen
  | succ n ih =>
      intro l hLen
      cases l with
      | nil => exact List.nodup_nil
      | cons head tail =>
          rw [List.eraseDups_cons]
          apply List.nodup_cons.mpr
          refine ⟨?_, ?_⟩
          · rw [List.mem_eraseDups, List.mem_filter]
            intro ⟨_, hne⟩
            simp at hne
          · apply ih
            exact Nat.le_trans (List.length_filter_le _ _)
              (by
                simp only [List.length_cons] at hLen
                omega)

theorem equationVariables_nodup {L : Language}
    (equations : List (Term L × Term L)) :
    (equationVariables equations).Nodup :=
  eraseDups_nodup_nat _

/-- The finite variable list represents exactly `termPairSetVars`. -/
theorem equationVariables_mem_iff {L : Language}
    (equations : List (Term L × Term L)) (x : Nat) :
    x ∈ equationVariables equations ↔
      termPairSetVars equations x := by
-- BEGIN PROOF
  rw [equationVariables, List.mem_eraseDups,
    equationVarIndicesList_mem_iff]

theorem nodup_length_le_of_subset
    {xs ys : List Nat} (hNodup : xs.Nodup)
    (hSubset : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
-- BEGIN PROOF
  induction xs generalizing ys with
  | nil =>
      exact Nat.zero_le _
  | cons head tail ih =>
      have hParts := List.nodup_cons.mp hNodup
      have hHead : head ∈ ys := hSubset head List.mem_cons_self
      have hTailSubset : ∀ x, x ∈ tail → x ∈ ys.erase head := by
        intro x hx
        apply (List.mem_erase_of_ne ?_).mpr
          (hSubset x (List.mem_cons.mpr (Or.inr hx)))
        intro hEq
        subst x
        exact hParts.1 hx
      have hTailLe := ih hParts.2 hTailSubset
      have hLength := (List.perm_cons_erase hHead).length_eq
      simp only [List.length_cons] at hLength ⊢
      omega

theorem nodup_length_lt_of_subset_of_missing
    {xs ys : List Nat} (hNodup : xs.Nodup)
    (hSubset : ∀ x, x ∈ xs → x ∈ ys)
    (missing : Nat) (hMissingMem : missing ∈ ys)
    (hMissingNotMem : missing ∉ xs) :
    xs.length < ys.length := by
-- BEGIN PROOF
  have hSubsetErase : ∀ x, x ∈ xs → x ∈ ys.erase missing := by
    intro x hx
    apply (List.mem_erase_of_ne ?_).mpr (hSubset x hx)
    intro hEq
    subst x
    exact hMissingNotMem hx
  have hLe :=
    nodup_length_le_of_subset hNodup hSubsetErase
  have hLength := (List.perm_cons_erase hMissingMem).length_eq
  simp only [List.length_cons] at hLength
  omega

/-- Inclusion of equation-variable sets gives monotonicity of their finite
    distinct-variable counts. -/
theorem equationVariableCount_le_of_subset {L : Language}
    {next current : List (Term L × Term L)}
    (hSubset : termPairSetVars next ⊆ termPairSetVars current) :
    equationVariableCount next ≤ equationVariableCount current := by
-- BEGIN PROOF
  apply nodup_length_le_of_subset (equationVariables_nodup next)
  intro x hx
  apply (equationVariables_mem_iff current x).mpr
  exact hSubset x ((equationVariables_mem_iff next x).mp hx)

/-- A missing variable makes inclusion of finite equation-variable sets
    strictly decrease their distinct-variable counts. -/
theorem equationVariableCount_lt_of_missing {L : Language}
    {next current : List (Term L × Term L)} (x : Nat)
    (hSubset : termPairSetVars next ⊆ termPairSetVars current)
    (hCurrent : termPairSetVars current x)
    (hNext : ¬ termPairSetVars next x) :
    equationVariableCount next < equationVariableCount current := by
-- BEGIN PROOF
  apply nodup_length_lt_of_subset_of_missing
    (equationVariables_nodup next)
    (fun y hy => (equationVariables_mem_iff current y).mpr
      (hSubset y ((equationVariables_mem_iff next y).mp hy))) x
    ((equationVariables_mem_iff current x).mpr hCurrent)
    (fun hx => hNext ((equationVariables_mem_iff next x).mp hx))

theorem equationVariableCount_eq_of_iff {L : Language}
    (left right : List (Term L × Term L))
    (hVars :
      ∀ x, termPairSetVars left x ↔ termPairSetVars right x) :
    equationVariableCount left = equationVariableCount right := by
-- BEGIN PROOF
  apply Nat.le_antisymm
  · apply equationVariableCount_le_of_subset
    intro x hx
    exact (hVars x).mp hx
  · apply equationVariableCount_le_of_subset
    intro x hx
    exact (hVars x).mpr hx

theorem termSize_pos {L : Language} (t : Term L) :
    0 < termSize t := by
-- BEGIN PROOF
  cases t <;> simp only [termSize] <;> omega

theorem equationComplexity_append {L : Language}
    (left right : List (Term L × Term L)) :
    equationComplexity (left ++ right) =
      equationComplexity left + equationComplexity right := by
-- BEGIN PROOF
  induction left with
  | nil =>
      simp [equationComplexity]
  | cons p left ih =>
      rcases p with ⟨s, t⟩
      simp only [List.cons_append, equationComplexity, ih]
      omega

theorem equationComplexity_ofFn {L : Language} {n : Nat}
    (ss ts : Fin n → Term L) :
    equationComplexity (List.ofFn fun i => (ss i, ts i)) =
      (List.ofFn fun i => termSize (ss i)).sum +
        (List.ofFn fun i => termSize (ts i)).sum := by
-- BEGIN PROOF
  induction n with
  | zero =>
      simp [List.ofFn_zero, equationComplexity]
  | succ n ih =>
      simp only [List.ofFn_succ, equationComplexity, List.sum_cons,
        ih (fun i => ss i.succ) (fun i => ts i.succ)]
      omega

theorem equationComplexity_functionEquationPairs_add_two
    {L : Language} {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L) :
    equationComplexity (functionEquationPairs hfg ss ts) + 2 =
      termSize (Term.func f ss) + termSize (Term.func g ts) := by
-- BEGIN PROOF
  subst g
  simp only [functionEquationPairs, equationComplexity_ofFn, termSize]
  rw [← List.sum_eq_foldl, ← List.sum_eq_foldl]
  omega

/-- Deleting a reflexive equation decreases the Robinson measure. -/
theorem robinsonDelete_measure_decreases {L : Language}
    (t : Term L) (rest : List (Term L × Term L)) :
    RobinsonMeasureDecreases rest ((t, t) :: rest) := by
-- BEGIN PROOF
  have hVars :
      equationVariableCount rest ≤
        equationVariableCount ((t, t) :: rest) := by
    apply equationVariableCount_le_of_subset
    intro x hx
    exact (termPairSetVars_cons_iff (t, t) rest x).mpr
      (Or.inr hx)
  have hComplexity :
      equationComplexity rest <
        equationComplexity ((t, t) :: rest) := by
    simp only [equationComplexity]
    have := termSize_pos t
    omega
  unfold RobinsonMeasureDecreases robinsonMeasure
  rcases Nat.lt_or_eq_of_le hVars with hVars | hVars
  · exact Prod.Lex.left _ _ hVars
  · rw [hVars]
    exact Prod.Lex.right _
      (Prod.Lex.left _ _ hComplexity)

/-- Orienting a non-variable/variable equation decreases the final component
    of the Robinson measure. -/
theorem robinsonOrient_measure_decreases {L : Language}
    (x : Nat) (s : Term L) (rest : List (Term L × Term L))
    (hNonvar : ∀ y, s ≠ Term.var y) :
    RobinsonMeasureDecreases
      ((Term.var x, s) :: rest)
      ((s, Term.var x) :: rest) := by
-- BEGIN PROOF
  have hVars :
      equationVariableCount ((Term.var x, s) :: rest) =
        equationVariableCount ((s, Term.var x) :: rest) := by
    apply equationVariableCount_eq_of_iff
    intro y
    rw [termPairSetVars_cons_iff, termPairSetVars_cons_iff]
    constructor
    · rintro ((hy | hy) | hy)
      · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl hy)
      · exact Or.inr hy
    · rintro ((hy | hy) | hy)
      · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl hy)
      · exact Or.inr hy
  unfold RobinsonMeasureDecreases robinsonMeasure
  rw [hVars]
  apply Prod.Lex.right
  have hComplexity :
      equationComplexity ((Term.var x, s) :: rest) =
        equationComplexity ((s, Term.var x) :: rest) := by
    simp only [equationComplexity, termSize]
    omega
  rw [hComplexity]
  apply Prod.Lex.right
  cases s with
  | var y =>
      exact (hNonvar y rfl).elim
  | const c =>
      simp [robinsonOrientationPenalty]
  | func f args =>
      simp [robinsonOrientationPenalty]

/-- Eliminating a variable that does not occur in its right-hand term
    strictly decreases the distinct-variable component. -/
theorem robinsonEliminate_measure_decreases {L : Language}
    (x : Nat) (t : Term L) (rest : List (Term L × Term L))
    (hNot : ¬ termFV t x) :
    RobinsonMeasureDecreases
      (substEquationSystem (elementarySubst x t) rest)
      ((Term.var x, t) :: rest) := by
-- BEGIN PROOF
  unfold RobinsonMeasureDecreases robinsonMeasure
  apply Prod.Lex.left
  apply equationVariableCount_lt_of_missing x
  · exact elementarySubst_system_vars_subset x t rest
  · exact (termPairSetVars_cons_iff
      (Term.var x, t) rest x).mpr
      (Or.inl (Or.inl rfl))
  · exact elementarySubst_removed_var x t rest hNot

/-- Decomposing equal function heads decreases total term complexity by two
    while preserving the equation-variable set. -/
theorem robinsonDecompose_measure_decreases {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L)
    (rest : List (Term L × Term L)) :
    RobinsonMeasureDecreases
      (functionEquationPairs hfg ss ts ++ rest)
      ((Term.func f ss, Term.func g ts) :: rest) := by
-- BEGIN PROOF
  have hVars :
      equationVariableCount
          (functionEquationPairs hfg ss ts ++ rest) =
        equationVariableCount
          ((Term.func f ss, Term.func g ts) :: rest) := by
    apply equationVariableCount_eq_of_iff
    intro x
    rw [termPairSetVars_append_iff, termPairSetVars_cons_iff,
      termPairSetVars_functionEquationPairs_iff]
  have hComplexity :
      equationComplexity
          (functionEquationPairs hfg ss ts ++ rest) <
        equationComplexity
          ((Term.func f ss, Term.func g ts) :: rest) := by
    rw [equationComplexity_append]
    simp only [equationComplexity]
    have hCost :=
      equationComplexity_functionEquationPairs_add_two hfg ss ts
    omega
  unfold RobinsonMeasureDecreases robinsonMeasure
  rw [hVars]
  exact Prod.Lex.right _
    (Prod.Lex.left _ _ hComplexity)

/-- Every successful deterministic Robinson step strictly decreases the
    lexicographic termination measure. -/
theorem robinsonStep_next_measure_decreases {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations) :
    RobinsonMeasureDecreases nextEquations equations := by
-- BEGIN PROOF
  classical
  cases equations with
  | nil =>
      simp [robinsonStep] at hStep
  | cons p rest =>
      rcases p with ⟨s, t⟩
      by_cases hEq : s = t
      · subst t
        simp [robinsonStep] at hStep
        rcases hStep with ⟨rfl, rfl, rfl⟩
        exact robinsonDelete_measure_decreases s rest
      · cases s with
        | var x =>
            by_cases hOccurs : termOccurs x t = true
            · simp [robinsonStep, hEq, hOccurs] at hStep
            · have hNot : ¬ termFV t x := by
                intro hx
                exact hOccurs
                  ((termOccurs_eq_true_iff x t).mpr hx)
              simp [robinsonStep, hEq, hOccurs] at hStep
              rcases hStep with ⟨rfl, rfl, rfl⟩
              exact
                robinsonEliminate_measure_decreases x t rest hNot
        | const c =>
            cases t with
            | var x =>
                simp [robinsonStep, hEq] at hStep
                rcases hStep with ⟨rfl, rfl, rfl⟩
                exact robinsonOrient_measure_decreases
                  x (Term.const c) rest (fun _ => nofun)
            | const d =>
                simp [robinsonStep, hEq] at hStep
            | func f args =>
                simp [robinsonStep, hEq] at hStep
        | func f args =>
            cases t with
            | var x =>
                simp [robinsonStep, hEq] at hStep
                rcases hStep with ⟨rfl, rfl, rfl⟩
                exact robinsonOrient_measure_decreases
                  x (Term.func f args) rest (fun _ => nofun)
            | const c =>
                simp [robinsonStep, hEq] at hStep
            | func g args' =>
                by_cases hfg : f = g
                · simp [robinsonStep, hEq, hfg] at hStep
                  rcases hStep with ⟨rfl, rfl, rfl⟩
                  exact robinsonDecompose_measure_decreases
                    hfg args args' rest
                · simp [robinsonStep, hEq, hfg] at hStep

/-- Result of the terminating Robinson solver. Success returns the composed
    substitution; failure retains the first genuine failure reason. -/
inductive RobinsonSolveResult (L : Language) : Type where
  | solved (substitution : Nat → Term L)
  | failure (reason : RobinsonFailure)

/-- Fuel-free Robinson equation simplification. Recursive calls are justified
    by the proved lexicographic decrease of every successful one-step
    transformation. -/
noncomputable def robinsonSolve {L : Language}
    (equations : List (Term L × Term L)) : RobinsonSolveResult L :=
  match _hStep : robinsonStep equations with
  | .solved =>
      .solved identitySubst
  | .failure reason =>
      .failure reason
  | .next _kind delta nextEquations =>
      match robinsonSolve nextEquations with
      | .solved theta =>
          .solved (SubstitutionCore.substCompose theta delta)
      | .failure reason =>
          .failure reason
termination_by robinsonMeasure equations
decreasing_by
  exact robinsonStep_next_measure_decreases
    equations nextEquations _kind delta _hStep

/-- Operational equation for a solver call whose first step is solved. -/
theorem robinsonSolve_of_step_solved {L : Language}
    (equations : List (Term L × Term L))
    (hStep : robinsonStep equations = RobinsonStepResult.solved) :
    robinsonSolve equations = RobinsonSolveResult.solved identitySubst := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def, hStep]

/-- Operational equation for a solver call whose first step fails. -/
theorem robinsonSolve_of_step_failure {L : Language}
    (equations : List (Term L × Term L))
    (reason : RobinsonFailure)
    (hStep :
      robinsonStep equations = RobinsonStepResult.failure reason) :
    robinsonSolve equations = RobinsonSolveResult.failure reason := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def, hStep]

/-- Operational equation for a solver call whose first step succeeds. -/
theorem robinsonSolve_of_step_next {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations) :
    robinsonSolve equations =
      match robinsonSolve nextEquations with
      | .solved theta =>
          .solved (SubstitutionCore.substCompose theta delta)
      | .failure reason =>
          .failure reason := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def, hStep]

/-- The terminating solver's complete semantic invariant: a returned
    substitution unifies the original system, while a returned failure means
    that no substitution unifies it. -/
theorem robinsonSolve_spec {L : Language}
    (equations : List (Term L × Term L)) :
    match robinsonSolve equations with
    | .solved mu =>
        IsPairwiseUnifier mu equations
    | .failure _ =>
        ¬ ∃ sigma : Nat → Term L,
          IsPairwiseUnifier sigma equations := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def]
  cases hStep : robinsonStep equations with
  | solved =>
      have hNil := (robinsonStep_solved_iff equations).mp hStep
      subst equations
      intro p hp
      exact (List.not_mem_nil hp).elim
  | failure reason =>
      exact robinsonStep_failure_not_unifiable
        equations reason hStep
  | next kind delta nextEquations =>
      have hNext := robinsonSolve_spec nextEquations
      cases hSolve : robinsonSolve nextEquations with
      | solved theta =>
          simp only [hSolve]
          rw [hSolve] at hNext
          apply (robinsonStep_next_solutions
            equations nextEquations kind delta
            (SubstitutionCore.substCompose theta delta) hStep).mpr
          exact ⟨theta, hNext, fun _ => rfl⟩
      | failure reason =>
          simp only [hSolve]
          rw [hSolve] at hNext
          rintro ⟨sigma, hSigma⟩
          obtain ⟨theta, hTheta, _⟩ :=
            (robinsonStep_next_solutions
              equations nextEquations kind delta sigma hStep).mp hSigma
          exact hNext ⟨theta, hTheta⟩
termination_by robinsonMeasure equations
decreasing_by
  exact robinsonStep_next_measure_decreases
    equations nextEquations kind delta hStep

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Completeness.Substitutions
/-- Every substitution returned by `robinsonSolve` unifies the input
    equation system. -/
theorem robinsonSolve_solved_is_unifier {L : Language}
    (equations : List (Term L × Term L)) (mu : Nat → Term L)
    (hSolve :
      robinsonSolve equations = RobinsonSolveResult.solved mu) :
    IsPairwiseUnifier mu equations := by
-- BEGIN PROOF
  have hSpec := robinsonSolve_spec equations
  rw [hSolve] at hSpec
  exact hSpec

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Completeness.Substitutions
/-- Every failure returned by the terminating solver is genuine. -/
theorem robinsonSolve_failure_not_unifiable {L : Language}
    (equations : List (Term L × Term L))
    (reason : RobinsonFailure)
    (hSolve :
      robinsonSolve equations = RobinsonSolveResult.failure reason) :
    ¬ ∃ sigma : Nat → Term L,
      IsPairwiseUnifier sigma equations := by
-- BEGIN PROOF
  have hSpec := robinsonSolve_spec equations
  rw [hSolve] at hSpec
  exact hSpec

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Completeness.Substitutions
/-- Completeness of the terminating simplifier: every unifiable finite
    equation system reaches a solved result, and the returned substitution is
    itself a unifier of the original system. -/
theorem robinsonSolve_complete {L : Language}
    (equations : List (Term L × Term L))
    (sigma : Nat → Term L)
    (hUnif : IsPairwiseUnifier sigma equations) :
    ∃ mu : Nat → Term L,
      robinsonSolve equations = RobinsonSolveResult.solved mu ∧
      IsPairwiseUnifier mu equations := by
-- BEGIN PROOF
  cases hSolve : robinsonSolve equations with
  | solved mu =>
      exact ⟨mu, rfl,
        robinsonSolve_solved_is_unifier equations mu hSolve⟩
  | failure reason =>
      exact (robinsonSolve_failure_not_unifiable
        equations reason hSolve ⟨sigma, hUnif⟩).elim

/-- The empty equation system has the identity substitution as an MGU. This
    is the base case required by a later terminating Robinson iteration. -/
theorem identitySubst_isPairwiseMGU_nil {L : Language} :
    IsPairwiseMGU (L := L) identitySubst [] := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact (List.not_mem_nil hp).elim
  · intro x hx
    exact (hx rfl).elim
  · intro sigma _
    exact ⟨sigma,
      congrFun (SubstitutionCore.substCompose_identity_right sigma).symm⟩

/-- Every successful call to the terminating Robinson solver returns an MGU
    of its original equation system. In particular, the returned substitution
    solves the system, changes only variables occurring in that system, and
    every other solution factors through it in `SubstitutionCore.substCompose` orientation. -/
theorem robinsonSolve_solved_isPairwiseMGU {L : Language}
    (equations : List (Term L × Term L)) (mu : Nat → Term L)
    (hSolve :
      robinsonSolve equations = RobinsonSolveResult.solved mu) :
    IsPairwiseMGU mu equations := by
-- BEGIN PROOF
  cases hStep : robinsonStep equations with
  | solved =>
      rw [robinsonSolve_of_step_solved equations hStep] at hSolve
      cases hSolve
      have hNil := (robinsonStep_solved_iff equations).mp hStep
      subst equations
      exact identitySubst_isPairwiseMGU_nil
  | failure reason =>
      rw [robinsonSolve_of_step_failure
        equations reason hStep] at hSolve
      cases hSolve
  | next kind delta nextEquations =>
      rw [robinsonSolve_of_step_next
        equations nextEquations kind delta hStep] at hSolve
      cases hNextSolve : robinsonSolve nextEquations with
      | solved theta =>
          simp only [hNextSolve] at hSolve
          cases hSolve
          exact robinsonStep_next_isPairwiseMGU
            equations nextEquations kind delta theta hStep
              (robinsonSolve_solved_isPairwiseMGU
                nextEquations theta hNextSolve)
      | failure reason =>
          simp only [hNextSolve] at hSolve
          cases hSolve
termination_by robinsonMeasure equations
decreasing_by
  exact robinsonStep_next_measure_decreases
    equations nextEquations kind delta hStep

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Completeness.Substitutions
/-- Theorem 8.4.1 (pairwise variant, for Term L): If a list of term PAIRS is
    simultaneously unifiable — i.e., some `sigma` solves every pair-equation
    `termSubstAll p.1 sigma = termSubstAll p.2 sigma` — then a pairwise MGU
    exists. This is the pairwise analogue of `mgu_exists_of_unifiable`;
    needed by SLD-resolution where unification at each argument position
    of a predicate is a distinct equation (per-position problem), not a
    single flat-list collapse. The witness is the output of the terminating
    Robinson solver, whose complete MGU invariant is proved above. -/
theorem mgu_exists_of_pairwise_unifiable {L : Language}
    (pairs : List (Term L × Term L))
    (sigma : Nat → Term L) (hUnif : IsPairwiseUnifier sigma pairs) :
    ∃ mu : Nat → Term L, IsPairwiseUnifier mu pairs ∧ IsPairwiseMGU mu pairs := by
-- BEGIN PROOF
  obtain ⟨mu, hSolve, hMu⟩ :=
    robinsonSolve_complete pairs sigma hUnif
  exact ⟨mu, hMu,
    robinsonSolve_solved_isPairwiseMGU pairs mu hSolve⟩

end LCS.FOResolution.Unification
end
