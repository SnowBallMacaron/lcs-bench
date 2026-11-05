import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Part1
import Attach
import LCS.FOResolution.Unification.Part2.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables
-- ATTACH-BLOCKER: private declaration
/-- Factoring through the identity substitution does not change a
    substitution property. -/
private theorem exists_factor_identity_iff {L : Language}
    (P : (Nat → Term L) → Prop) (sigma : Nat → Term L) :
    (∃ theta : Nat → Term L,
        P theta ∧
        ∀ x, sigma x = SubstitutionCore.substCompose theta identitySubst x) ↔
      P sigma := by
-- BEGIN PROOF
  simp only [SubstitutionCore.substCompose_identity_right]
  constructor
  · rintro ⟨theta, hTheta, hFactor⟩
    have hEq : sigma = theta := by
      funext x
      exact hFactor x
    rwa [hEq]
  · intro hSigma
    exact ⟨sigma, hSigma, fun _ => rfl⟩
-- ATTACH-BLOCKER: private declaration
private def RobinsonStepSound {L : Language}
    (equations : List (Term L × Term L)) :
    RobinsonStepResult L → Prop
  | .solved => equations = []
  | .next _ delta nextEquations =>
      (∀ sigma : Nat → Term L,
        IsPairwiseUnifier sigma equations ↔
          ∃ theta : Nat → Term L,
            IsPairwiseUnifier theta nextEquations ∧
            ∀ x, sigma x = SubstitutionCore.substCompose theta delta x) ∧
      SubstitutionCore.substSupport delta ⊆ termPairSetVars equations ∧
      termPairSetVars nextEquations ⊆ termPairSetVars equations
  | .failure _ =>
      ¬ ∃ sigma : Nat → Term L, IsPairwiseUnifier sigma equations
-- ATTACH-BLOCKER: private declaration
private theorem robinsonDelete_sound {L : Language}
    (t : Term L) (rest : List (Term L × Term L)) :
    RobinsonStepSound ((t, t) :: rest)
      (.next .delete identitySubst rest) := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · intro sigma
    rw [exists_factor_identity_iff]
    exact isPairwiseUnifier_delete_iff t rest sigma
  · intro x hx
    exact (hx rfl).elim
  · intro x hx
    exact (termPairSetVars_cons_iff (t, t) rest x).mpr (Or.inr hx)
-- ATTACH-BLOCKER: private declaration
private theorem robinsonOrient_sound {L : Language}
    (x : Nat) (t : Term L) (rest : List (Term L × Term L)) :
    RobinsonStepSound ((t, Term.var x) :: rest)
      (.next .orient identitySubst ((Term.var x, t) :: rest)) := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · intro sigma
    rw [exists_factor_identity_iff]
    exact isPairwiseUnifier_orient_iff x t rest sigma
  · intro y hy
    exact (hy rfl).elim
  · intro y hy
    apply (termPairSetVars_cons_iff (t, Term.var x) rest y).mpr
    rcases (termPairSetVars_cons_iff
      (Term.var x, t) rest y).mp hy with hHead | hRest
    · exact Or.inl (hHead.elim Or.inr Or.inl)
    · exact Or.inr hRest
-- ATTACH-BLOCKER: private declaration
private theorem robinsonEliminate_sound {L : Language}
    (x : Nat) (t : Term L) (rest : List (Term L × Term L))
    (hNot : ¬ termFV t x) :
    RobinsonStepSound ((Term.var x, t) :: rest)
      (.next .eliminate (elementarySubst x t)
        (substEquationSystem (elementarySubst x t) rest)) := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · exact fun sigma =>
      isPairwiseUnifier_eliminate_iff x t rest hNot sigma
  · intro y hy
    have hyx := elementarySubst_support_subset x t y hy
    subst y
    exact ⟨(Term.var x, t), List.mem_cons_self, Or.inl rfl⟩
  · exact elementarySubst_system_vars_subset x t rest
-- ATTACH-BLOCKER: private declaration
private theorem robinsonDecompose_sound {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L)
    (rest : List (Term L × Term L)) :
    RobinsonStepSound ((Term.func f ss, Term.func g ts) :: rest)
      (.next .decompose identitySubst
        (functionEquationPairs hfg ss ts ++ rest)) := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · intro sigma
    rw [exists_factor_identity_iff]
    exact (isPairwiseUnifier_decompose_iff
      hfg ss ts rest sigma).symm
  · intro x hx
    exact (hx rfl).elim
  · intro x hx
    apply (termPairSetVars_cons_iff
      (Term.func f ss, Term.func g ts) rest x).mpr
    rcases (termPairSetVars_append_iff
      (functionEquationPairs hfg ss ts) rest x).mp hx with hHead | hRest
    · exact Or.inl
        ((termPairSetVars_functionEquationPairs_iff
          hfg ss ts x).mp hHead)
    · exact Or.inr hRest
-- ATTACH-BLOCKER: private declaration
private theorem robinsonOccursFailure_sound {L : Language}
    (x : Nat) (t : Term L) (rest : List (Term L × Term L))
    (hNe : t ≠ Term.var x) (hOccurs : termOccurs x t = true) :
    RobinsonStepSound ((Term.var x, t) :: rest)
      (.failure .occursCheck) := by
-- BEGIN PROOF
  rintro ⟨sigma, hUnifier⟩
  exact var_occurs_not_unifiable x t hNe hOccurs
    ⟨sigma, hUnifier (Term.var x, t) List.mem_cons_self⟩
-- ATTACH-BLOCKER: private declaration
private theorem robinsonClashFailure_sound {L : Language}
    (s t : Term L) (rest : List (Term L × Term L))
    (hIncompatible : ¬ TermHeadsCompatible s t) :
    RobinsonStepSound ((s, t) :: rest) (.failure .symbolClash) :=
  incompatible_head_not_pairwise_unifiable s t rest hIncompatible
-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_sound {L : Language}
    (equations : List (Term L × Term L)) :
    RobinsonStepSound equations (robinsonStep equations) := by
-- BEGIN PROOF
  classical
  cases equations with
  | nil =>
      rfl
  | cons p rest =>
      rcases p with ⟨s, t⟩
      by_cases hEq : s = t
      · subst t
        simpa [robinsonStep] using robinsonDelete_sound s rest
      · cases s with
        | var x =>
            by_cases hOccurs : termOccurs x t = true
            · simpa [robinsonStep, hEq, hOccurs] using
                robinsonOccursFailure_sound x t rest
                  (fun h => hEq h.symm) hOccurs
            · have hNot : ¬ termFV t x := by
                intro hx
                exact hOccurs ((termOccurs_eq_true_iff x t).mpr hx)
              simpa [robinsonStep, hEq, hOccurs] using
                robinsonEliminate_sound x t rest hNot
        | const c =>
            cases t with
            | var x =>
                simpa [robinsonStep, hEq] using
                  robinsonOrient_sound x (Term.const c) rest
            | const d =>
                have hcd : c ≠ d := by
                  intro h
                  subst d
                  exact hEq rfl
                simpa [robinsonStep, hEq] using
                  robinsonClashFailure_sound
                    (Term.const c) (Term.const d) rest hcd
            | func f args =>
                simpa [robinsonStep, hEq] using
                  robinsonClashFailure_sound
                    (Term.const c) (Term.func f args) rest nofun
        | func f args =>
            cases t with
            | var x =>
                simpa [robinsonStep, hEq] using
                  robinsonOrient_sound x (Term.func f args) rest
            | const c =>
                simpa [robinsonStep, hEq] using
                  robinsonClashFailure_sound
                    (Term.func f args) (Term.const c) rest nofun
            | func g args' =>
                by_cases hfg : f = g
                · simpa [robinsonStep, hEq, hfg] using
                    robinsonDecompose_sound hfg args args' rest
                · simpa [robinsonStep, hEq, hfg] using
                    robinsonClashFailure_sound
                      (Term.func f args) (Term.func g args') rest hfg
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every successful Robinson step preserves all solutions, with the old
    solution factoring through the substitution recorded by the step. -/
theorem robinsonStep_next_solutions {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta sigma : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations) :
    IsPairwiseUnifier sigma equations ↔
      ∃ theta : Nat → Term L,
        IsPairwiseUnifier theta nextEquations ∧
        ∀ x, sigma x = SubstitutionCore.substCompose theta delta x := by
-- BEGIN PROOF
  have hSound := robinsonStep_sound equations
  rw [hStep] at hSound
  exact hSound.1 sigma
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The substitution recorded by a successful step only changes variables
    already present in the current equation system. -/
theorem robinsonStep_next_delta_support {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations) :
    SubstitutionCore.substSupport delta ⊆ termPairSetVars equations := by
-- BEGIN PROOF
  have hSound := robinsonStep_sound equations
  rw [hStep] at hSound
  exact hSound.2.1
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A successful Robinson step cannot introduce an equation variable that was
    absent from the current system. -/
theorem robinsonStep_next_vars_subset {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations) :
    termPairSetVars nextEquations ⊆ termPairSetVars equations := by
-- BEGIN PROOF
  have hSound := robinsonStep_sound equations
  rw [hStep] at hSound
  exact hSound.2.2
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- An MGU of the next equation system composes with the substitution recorded
    by a successful Robinson step to give an MGU of the current system. This
    simultaneously propagates unification, support, and universal
    factorization across delete, orient, eliminate, and decompose steps. -/
theorem robinsonStep_next_isPairwiseMGU {L : Language}
    (equations nextEquations : List (Term L × Term L))
    (kind : RobinsonStepKind) (delta theta : Nat → Term L)
    (hStep :
      robinsonStep equations =
        RobinsonStepResult.next kind delta nextEquations)
    (hNextMGU : IsPairwiseMGU theta nextEquations) :
    IsPairwiseMGU (SubstitutionCore.substCompose theta delta) equations := by
-- BEGIN PROOF
  refine ⟨?_, ?_, ?_⟩
  · apply (robinsonStep_next_solutions
      equations nextEquations kind delta
      (SubstitutionCore.substCompose theta delta) hStep).mpr
    exact ⟨theta, hNextMGU.1, fun _ => rfl⟩
  · intro x hx
    rcases SubstitutionCore.substSupport_compose_subset theta delta x hx with
      hxTheta | hxDelta
    · exact robinsonStep_next_vars_subset
        equations nextEquations kind delta hStep
          x (hNextMGU.2.1 x hxTheta)
    · exact robinsonStep_next_delta_support
        equations nextEquations kind delta hStep x hxDelta
  · intro sigma hSigma
    obtain ⟨rho, hRho, hSigmaFactor⟩ :=
      (robinsonStep_next_solutions
        equations nextEquations kind delta sigma hStep).mp hSigma
    obtain ⟨eta, hRhoFactor⟩ := hNextMGU.2.2 rho hRho
    refine ⟨eta, fun x => ?_⟩
    calc
      sigma x = SubstitutionCore.substCompose rho delta x := hSigmaFactor x
      _ = SubstitutionCore.substCompose (SubstitutionCore.substCompose eta theta) delta x := by
        rw [show rho = SubstitutionCore.substCompose eta theta from funext hRhoFactor]
      _ = SubstitutionCore.substCompose eta (SubstitutionCore.substCompose theta delta) x :=
        congrFun (SubstitutionCore.substCompose_assoc eta theta delta).symm x
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every failure reported by a Robinson step is genuine: the current equation
    system has no pairwise unifier. -/
theorem robinsonStep_failure_not_unifiable {L : Language}
    (equations : List (Term L × Term L))
    (reason : RobinsonFailure)
    (hStep :
      robinsonStep equations = RobinsonStepResult.failure reason) :
    ¬ ∃ sigma : Nat → Term L, IsPairwiseUnifier sigma equations := by
-- BEGIN PROOF
  have hSound := robinsonStep_sound equations
  rw [hStep] at hSound
  exact hSound
-- ATTACH-BLOCKER: private declaration
/-- Membership in the variable-index accumulator used by
    `termVarIndicesList`. -/
private theorem mem_foldl_append_termVarIndices {L : Language} (x : Nat)
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
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Variable indices occurring in a finite equation system, before duplicate
    removal. -/
def equationVarIndicesList {L : Language} :
    List (Term L × Term L) → List Nat
  | [] => []
  | (s, t) :: rest =>
      (termVarIndicesList s ++ termVarIndicesList t) ++
        equationVarIndicesList rest
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The duplicate-free list of variables occurring in a finite equation
    system. -/
def equationVariables {L : Language}
    (equations : List (Term L × Term L)) : List Nat :=
  (equationVarIndicesList equations).eraseDups
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The number of distinct variables occurring in an equation system. -/
def equationVariableCount {L : Language}
    (equations : List (Term L × Term L)) : Nat :=
  (equationVariables equations).length

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Total structural term complexity on both sides of an equation system. -/
def equationComplexity {L : Language} :
    List (Term L × Term L) → Nat
  | [] => 0
  | (s, t) :: rest =>
      termSize s + termSize t + equationComplexity rest

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The final component of the Robinson measure. It is one exactly when the
    head equation has a non-variable on the left and a variable on the right,
    so an orientation step changes it to zero. -/
def robinsonOrientationPenalty {L : Language} :
    List (Term L × Term L) → Nat
  | (Term.const _, Term.var _) :: _ => 1
  | (Term.func _ _, Term.var _) :: _ => 1
  | _ => 0

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lexicographic termination measure for Robinson simplification:
    distinct variables, then total term complexity, then orientation. -/
def robinsonMeasure {L : Language}
    (equations : List (Term L × Term L)) : Nat × Nat × Nat :=
  (equationVariableCount equations, equationComplexity equations,
    robinsonOrientationPenalty equations)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The explicit lexicographic decrease relation induced by
    `robinsonMeasure`. -/
def RobinsonMeasureDecreases {L : Language}
    (next current : List (Term L × Term L)) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (robinsonMeasure next) (robinsonMeasure current)



-- ATTACH-BLOCKER: private declaration
private theorem equationVarIndicesList_mem_iff {L : Language}
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

-- ATTACH-BLOCKER: private declaration
private theorem eraseDups_nodup_nat (l : List Nat) :
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

-- ATTACH-BLOCKER: private declaration
private theorem equationVariables_nodup {L : Language}
    (equations : List (Term L × Term L)) :
    (equationVariables equations).Nodup :=
  eraseDups_nodup_nat _

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The finite variable list represents exactly `termPairSetVars`. -/
theorem equationVariables_mem_iff {L : Language}
    (equations : List (Term L × Term L)) (x : Nat) :
    x ∈ equationVariables equations ↔
      termPairSetVars equations x := by
-- BEGIN PROOF
  rw [equationVariables, List.mem_eraseDups,
    equationVarIndicesList_mem_iff]

-- ATTACH-BLOCKER: private declaration
private theorem nodup_length_le_of_subset
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

-- ATTACH-BLOCKER: private declaration
private theorem nodup_length_lt_of_subset_of_missing
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: private declaration
private theorem equationVariableCount_eq_of_iff {L : Language}
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

-- ATTACH-BLOCKER: private declaration
private theorem termSize_pos {L : Language} (t : Term L) :
    0 < termSize t := by
-- BEGIN PROOF
  cases t <;> simp only [termSize] <;> omega

-- ATTACH-BLOCKER: private declaration
private theorem equationComplexity_append {L : Language}
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

-- ATTACH-BLOCKER: private declaration
private theorem equationComplexity_ofFn {L : Language} {n : Nat}
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

-- ATTACH-BLOCKER: private declaration
private theorem equationComplexity_functionEquationPairs_add_two
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A one-step result is solved exactly for the empty equation system. -/
theorem robinsonStep_solved_iff {L : Language}
    (equations : List (Term L × Term L)) :
    robinsonStep equations = RobinsonStepResult.solved ↔
      equations = [] := by
-- BEGIN PROOF
  constructor
  · intro hStep
    have hSound := robinsonStep_sound equations
    rw [hStep] at hSound
    exact hSound
  · rintro rfl
    rfl

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Result of the terminating Robinson solver. Success returns the composed
    substitution; failure retains the first genuine failure reason. -/
inductive RobinsonSolveResult (L : Language) : Type where
  | solved (substitution : Nat → Term L)
  | failure (reason : RobinsonFailure)

-- ATTACH-BLOCKER: termination suffix
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Operational equation for a solver call whose first step is solved. -/
theorem robinsonSolve_of_step_solved {L : Language}
    (equations : List (Term L × Term L))
    (hStep : robinsonStep equations = RobinsonStepResult.solved) :
    robinsonSolve equations = RobinsonSolveResult.solved identitySubst := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def, hStep]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Operational equation for a solver call whose first step fails. -/
theorem robinsonSolve_of_step_failure {L : Language}
    (equations : List (Term L × Term L))
    (reason : RobinsonFailure)
    (hStep :
      robinsonStep equations = RobinsonStepResult.failure reason) :
    robinsonSolve equations = RobinsonSolveResult.failure reason := by
-- BEGIN PROOF
  rw [robinsonSolve.eq_def, hStep]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: termination suffix
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ATTACH-BLOCKER: termination suffix
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

-- ===================================================================
-- Example 8.4.1: Unification examples
-- ===================================================================

/-- Example 8.4.1 (companion): Function symbols for the unification example language:
f (binary or ternary), g (unary), and h (unary). -/
@[blueprint "chap8__example_8_4_1"]
inductive UnifExFunc : Type where
  /-- Binary function symbol f (also used as ternary in part iii) -/
  | f : UnifExFunc
  /-- Unary function symbol g -/
  | g : UnifExFunc
  /-- Unary function symbol h (for symbol clash example) -/
  | h : UnifExFunc

/-- Example 8.4.1 (companion): A language with function symbols f (arity 2), g (arity 1),
h (arity 1), and no constants. Variables x, y, z, u are represented as
Nat indices 0, 1, 2, 3 respectively. -/
@[blueprint "chap8__example_8_4_1"]
def unificationExampleLanguage : Language where
  funSymbols := UnifExFunc
  funArity := fun
    | .f => 2
    | .g => 1
    | .h => 1
  constSymbols := Empty
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := false

-- Variable assignments: x = 0, y = 1, z = 2, u = 3

/-- Example 8.4.1 (companion): build a Fin 1 -> alpha function from a single value. -/
@[blueprint "chap8__example_8_4_1"]
def unifVec1 (a : α) : Fin 1 → α
  | ⟨0, _⟩ => a

/-- Example 8.4.1 (companion): build a Fin 2 -> alpha function from two values. -/
@[blueprint "chap8__example_8_4_1"]
def unifVec2 (a b : α) : Fin 2 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

-- ATTACH-BLOCKER: private declaration
private inductive RobinsonRegressionConst : Type where
  | left
  | right

-- ATTACH-BLOCKER: private declaration
private def robinsonConstantRegressionLanguage : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := RobinsonRegressionConst
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := false

-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_var_self_regression :
    robinsonStep
      (L := unificationExampleLanguage)
      [(Term.var 0, Term.var 0)] =
        RobinsonStepResult.next
          RobinsonStepKind.delete identitySubst [] := by
-- BEGIN PROOF
  simp [robinsonStep]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_occurs_regression :
    robinsonStep
      (L := unificationExampleLanguage)
      [(Term.var 0,
        Term.func UnifExFunc.g (unifVec1 (Term.var 0)))] =
        RobinsonStepResult.failure RobinsonFailure.occursCheck := by
-- BEGIN PROOF
  have hOccurs :
      termOccurs 0
        (Term.func UnifExFunc.g (unifVec1 (Term.var 0)) :
          Term unificationExampleLanguage) = true := by
    apply (termOccurs_eq_true_iff 0 _).mpr
    exact ⟨⟨0, by simp [unificationExampleLanguage]⟩, rfl⟩
  simp [robinsonStep, hOccurs]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_distinct_constants_regression :
    robinsonStep
      (L := robinsonConstantRegressionLanguage)
      [(Term.const RobinsonRegressionConst.left,
        Term.const RobinsonRegressionConst.right)] =
        RobinsonStepResult.failure RobinsonFailure.symbolClash := by
-- BEGIN PROOF
  simp [robinsonStep]
  intro h
  cases Term.const.inj h

-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_distinct_functions_regression :
    robinsonStep
      (L := unificationExampleLanguage)
      [(Term.func UnifExFunc.g (unifVec1 (Term.var 0)),
        Term.func UnifExFunc.h (unifVec1 (Term.var 0)))] =
        RobinsonStepResult.failure RobinsonFailure.symbolClash := by
-- BEGIN PROOF
  simp [robinsonStep]
  intro h
  cases (Term.func.inj h).1

-- ATTACH-BLOCKER: private declaration
private theorem robinsonStep_binary_decomposition_regression :
    robinsonStep
      (L := unificationExampleLanguage)
      [(Term.func UnifExFunc.f
          (unifVec2 (Term.var 0) (Term.var 1)),
        Term.func UnifExFunc.f
          (unifVec2 (Term.var 2) (Term.var 3)))] =
        RobinsonStepResult.next RobinsonStepKind.decompose identitySubst
          [(Term.var 0, Term.var 2), (Term.var 1, Term.var 3)] := by
-- BEGIN PROOF
  have hNe :
      (Term.func UnifExFunc.f
          (unifVec2 (Term.var 0) (Term.var 1)) :
          Term unificationExampleLanguage) ≠
        (Term.func UnifExFunc.f
          (unifVec2 (Term.var 2) (Term.var 3)) :
          Term unificationExampleLanguage) := by
    intro h
    have hArgs := eq_of_heq (Term.func.inj h).2
    have h0 := congrFun hArgs (0 : Fin 2)
    simp [unifVec2] at h0
  simp only [robinsonStep]
  rw [dif_neg hNe]
  simp [functionEquationPairs, unificationExampleLanguage,
    List.ofFn_succ, List.ofFn_zero, unifVec2]
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_delete_regression :
    robinsonSolve
      (L := unificationExampleLanguage)
      [(Term.var 0, Term.var 0)] =
        RobinsonSolveResult.solved identitySubst := by
-- BEGIN PROOF
  rw [robinsonSolve_of_step_next _ _ _ _
    robinsonStep_var_self_regression]
  rw [robinsonSolve_of_step_solved [] (by rfl)]
  simp only [SubstitutionCore.substCompose_identity_left]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_eliminate_regression :
    robinsonSolve
      (L := unificationExampleLanguage)
      [(Term.var 0, Term.var 1)] =
        RobinsonSolveResult.solved
          (elementarySubst 0 (Term.var 1)) := by
-- BEGIN PROOF
  have hStep :
      robinsonStep
        (L := unificationExampleLanguage)
        [(Term.var 0, Term.var 1)] =
          RobinsonStepResult.next RobinsonStepKind.eliminate
            (elementarySubst 0 (Term.var 1)) [] := by
    simp [robinsonStep, termOccurs, substEquationSystem]
  rw [robinsonSolve_of_step_next _ _ _ _ hStep]
  rw [robinsonSolve_of_step_solved [] (by rfl)]
  simp only
  rw [SubstitutionCore.substCompose_identity_left]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_empty_mgu_regression :
    robinsonSolve
        (L := unificationExampleLanguage) [] =
          RobinsonSolveResult.solved identitySubst ∧
      IsPairwiseUnifier
          (L := unificationExampleLanguage) identitySubst [] ∧
      SubstitutionCore.substSupport
          (L := unificationExampleLanguage) identitySubst ⊆
        termPairSetVars
          (L := unificationExampleLanguage) [] ∧
      ∀ sigma : Nat → Term unificationExampleLanguage,
        IsPairwiseUnifier sigma [] →
          ∃ theta : Nat → Term unificationExampleLanguage,
            ∀ x, sigma x =
              SubstitutionCore.substCompose theta identitySubst x := by
-- BEGIN PROOF
  have hSolve :
      robinsonSolve
          (L := unificationExampleLanguage) [] =
        RobinsonSolveResult.solved identitySubst :=
    robinsonSolve_of_step_solved [] (by rfl)
  have hMGU :=
    robinsonSolve_solved_isPairwiseMGU
      (L := unificationExampleLanguage) [] identitySubst hSolve
  exact ⟨hSolve, hMGU⟩

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_eliminate_mgu_regression :
    robinsonSolve
        (L := unificationExampleLanguage)
        [(Term.var 0, Term.var 1)] =
          RobinsonSolveResult.solved
            (elementarySubst 0 (Term.var 1)) ∧
      IsPairwiseUnifier
          (L := unificationExampleLanguage)
          (elementarySubst
            (L := unificationExampleLanguage) 0 (Term.var 1))
          [(Term.var 0, Term.var 1)] ∧
      SubstitutionCore.substSupport
          (L := unificationExampleLanguage)
          (elementarySubst 0 (Term.var 1)) ⊆
        termPairSetVars
          (L := unificationExampleLanguage)
          [(Term.var 0, Term.var 1)] ∧
      ∀ sigma : Nat → Term unificationExampleLanguage,
        IsPairwiseUnifier sigma
            [(Term.var 0, Term.var 1)] →
          ∃ theta : Nat → Term unificationExampleLanguage,
            ∀ x, sigma x =
              SubstitutionCore.substCompose theta
                (elementarySubst 0 (Term.var 1)) x := by
-- BEGIN PROOF
  have hMGU :=
    robinsonSolve_solved_isPairwiseMGU
      [(Term.var 0, Term.var 1)]
      (elementarySubst 0 (Term.var 1))
      robinsonSolve_eliminate_regression
  exact ⟨robinsonSolve_eliminate_regression, hMGU⟩

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_chain_regression :
    robinsonSolve
        (L := unificationExampleLanguage)
        [(Term.var 0, Term.var 1),
          (Term.var 1, Term.var 2)] =
      RobinsonSolveResult.solved
        (SubstitutionCore.substCompose
          (elementarySubst 1 (Term.var 2))
          (elementarySubst 0 (Term.var 1))) := by
-- BEGIN PROOF
  have hFirst :
      robinsonStep
          (L := unificationExampleLanguage)
          [(Term.var 0, Term.var 1),
            (Term.var 1, Term.var 2)] =
        RobinsonStepResult.next RobinsonStepKind.eliminate
          (elementarySubst 0 (Term.var 1))
          [(Term.var 1, Term.var 2)] := by
    simp [robinsonStep, termOccurs, substEquationSystem,
      termSubstAll, elementarySubst]
  have hSecond :
      robinsonStep
          (L := unificationExampleLanguage)
          [(Term.var 1, Term.var 2)] =
        RobinsonStepResult.next RobinsonStepKind.eliminate
          (elementarySubst 1 (Term.var 2)) [] := by
    simp [robinsonStep, termOccurs, substEquationSystem]
  rw [robinsonSolve_of_step_next _ _ _ _ hFirst]
  rw [robinsonSolve_of_step_next _ _ _ _ hSecond]
  rw [robinsonSolve_of_step_solved [] (by rfl)]
  simp only
  rw [SubstitutionCore.substCompose_identity_left]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_chain_mgu_regression :
    let mu : Nat → Term unificationExampleLanguage :=
      SubstitutionCore.substCompose
        (elementarySubst 1 (Term.var 2))
        (elementarySubst 0 (Term.var 1))
    let equations : List
        (Term unificationExampleLanguage ×
          Term unificationExampleLanguage) :=
      [(Term.var 0, Term.var 1),
        (Term.var 1, Term.var 2)]
    robinsonSolve equations = RobinsonSolveResult.solved mu ∧
      IsPairwiseUnifier mu equations ∧
      SubstitutionCore.substSupport mu ⊆ termPairSetVars equations ∧
      ∀ sigma : Nat → Term unificationExampleLanguage,
        IsPairwiseUnifier sigma equations →
          ∃ theta : Nat → Term unificationExampleLanguage,
            ∀ x, sigma x = SubstitutionCore.substCompose theta mu x := by
-- BEGIN PROOF
  dsimp only
  have hMGU :=
    robinsonSolve_solved_isPairwiseMGU
      [(Term.var 0, Term.var 1),
        (Term.var 1, Term.var 2)]
      (SubstitutionCore.substCompose
        (elementarySubst 1 (Term.var 2))
        (elementarySubst 0 (Term.var 1)))
      robinsonSolve_chain_regression
  exact ⟨robinsonSolve_chain_regression, hMGU⟩

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_orient_regression :
    robinsonSolve
      (L := robinsonConstantRegressionLanguage)
      [(Term.const RobinsonRegressionConst.left, Term.var 0)] =
        RobinsonSolveResult.solved
          (elementarySubst 0
            (Term.const RobinsonRegressionConst.left)) := by
-- BEGIN PROOF
  have hOrient :
      robinsonStep
        (L := robinsonConstantRegressionLanguage)
        [(Term.const RobinsonRegressionConst.left, Term.var 0)] =
          RobinsonStepResult.next RobinsonStepKind.orient identitySubst
            [(Term.var 0, Term.const RobinsonRegressionConst.left)] := by
    simp [robinsonStep]
  have hEliminate :
      robinsonStep
        (L := robinsonConstantRegressionLanguage)
        [(Term.var 0, Term.const RobinsonRegressionConst.left)] =
          RobinsonStepResult.next RobinsonStepKind.eliminate
            (elementarySubst 0
              (Term.const RobinsonRegressionConst.left)) [] := by
    simp [robinsonStep, termOccurs, substEquationSystem]
  rw [robinsonSolve_of_step_next _ _ _ _ hOrient]
  rw [robinsonSolve_of_step_next _ _ _ _ hEliminate]
  rw [robinsonSolve_of_step_solved [] (by rfl)]
  simp only
  rw [SubstitutionCore.substCompose_identity_left, SubstitutionCore.substCompose_identity_right]

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_decompose_regression :
    robinsonSolve
      (L := unificationExampleLanguage)
      [(Term.func UnifExFunc.f
          (unifVec2 (Term.var 0) (Term.var 1)),
        Term.func UnifExFunc.f
          (unifVec2 (Term.var 0) (Term.var 2)))] =
        RobinsonSolveResult.solved
          (elementarySubst 1 (Term.var 2)) := by
-- BEGIN PROOF
  let left : Term unificationExampleLanguage :=
    Term.func UnifExFunc.f
      (unifVec2 (Term.var 0) (Term.var 1))
  let right : Term unificationExampleLanguage :=
    Term.func UnifExFunc.f
      (unifVec2 (Term.var 0) (Term.var 2))
  have hNe : left ≠ right := by
    intro h
    have hArgs := eq_of_heq (Term.func.inj h).2
    have h1 := congrFun hArgs (1 : Fin 2)
    simp [unifVec2] at h1
  have hDecompose :
      robinsonStep [(left, right)] =
        RobinsonStepResult.next RobinsonStepKind.decompose identitySubst
          [(Term.var 0, Term.var 0), (Term.var 1, Term.var 2)] := by
    simp only [robinsonStep]
    rw [dif_neg hNe]
    simp [left, right, functionEquationPairs,
      unificationExampleLanguage, List.ofFn_succ, List.ofFn_zero,
      unifVec2]
    rfl
  have hDelete :
      robinsonStep
        (L := unificationExampleLanguage)
        [(Term.var 0, Term.var 0), (Term.var 1, Term.var 2)] =
          RobinsonStepResult.next RobinsonStepKind.delete identitySubst
            [(Term.var 1, Term.var 2)] := by
    simp [robinsonStep]
  have hEliminate :
      robinsonStep
        (L := unificationExampleLanguage)
        [(Term.var 1, Term.var 2)] =
          RobinsonStepResult.next RobinsonStepKind.eliminate
            (elementarySubst 1 (Term.var 2)) [] := by
    simp [robinsonStep, termOccurs, substEquationSystem]
  change robinsonSolve [(left, right)] = _
  rw [robinsonSolve_of_step_next _ _ _ _ hDecompose]
  rw [robinsonSolve_of_step_next _ _ _ _ hDelete]
  rw [robinsonSolve_of_step_next _ _ _ _ hEliminate]
  rw [robinsonSolve_of_step_solved [] (by rfl)]
  simp only
  rw [SubstitutionCore.substCompose_identity_left, SubstitutionCore.substCompose_identity_right]
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_occurs_failure_regression :
    robinsonSolve
      (L := unificationExampleLanguage)
      [(Term.var 0,
        Term.func UnifExFunc.g (unifVec1 (Term.var 0)))] =
        RobinsonSolveResult.failure RobinsonFailure.occursCheck :=
  robinsonSolve_of_step_failure _ _
    robinsonStep_occurs_regression

-- ATTACH-BLOCKER: private declaration
private theorem robinsonSolve_symbol_clash_regression :
    robinsonSolve
      (L := robinsonConstantRegressionLanguage)
      [(Term.const RobinsonRegressionConst.left,
        Term.const RobinsonRegressionConst.right)] =
        RobinsonSolveResult.failure RobinsonFailure.symbolClash :=
  robinsonSolve_of_step_failure _ _
    robinsonStep_distinct_constants_regression

/-- Example 8.4.1: t_1 = f(x, g(y)) from subcase (i), the first term in
the unifiable pair. Variables: x = 0, y = 1. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t1_i : Term unificationExampleLanguage :=
  Term.func UnifExFunc.f
    (unifVec2 (Term.var 0)
      (Term.func UnifExFunc.g (unifVec1 (Term.var 1))))

/-- Example 8.4.1: t_2 = f(g(u), g(z)) from subcase (i), the second term
in the unifiable pair. Variables: z = 2, u = 3. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t2_i : Term unificationExampleLanguage :=
  Term.func UnifExFunc.f
    (unifVec2
      (Term.func UnifExFunc.g (unifVec1 (Term.var 3)))
      (Term.func UnifExFunc.g (unifVec1 (Term.var 2))))

/-- Example 8.4.1: The mgu substitution (g(u)/x, y/z) from subcase (i);
maps x to g(u), z to y (i.e., var 1), and all others to themselves. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_mgu_i : Nat → Term unificationExampleLanguage
  | 0 => Term.func UnifExFunc.g (unifVec1 (Term.var 3))  -- x -> g(u)
  | 2 => Term.var 1                                        -- z -> y
  | n => Term.var n                                        -- others -> identity

/-- Example 8.4.1: The most common instance f(g(u), g(y)) from subcase (i),
obtained by applying the mgu to t_1 (or equivalently t_2). -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_mci_i : Term unificationExampleLanguage :=
  termSubstAll unifEx_t1_i unifEx_mgu_i

/-- Example 8.4.1(i) (companion): the stored substitution has the explicit
    finite support witness [x,z] = [0,2], with the original variable map. -/
@[blueprint "chap8__example_8_4_1"]
def unifEx_finite_mgu_i : FiniteSubstitution unificationExampleLanguage where
  support := [0, 2]
  map := unifEx_mgu_i
  outsideSupport := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
    match x with
    | 0 => exact (hx.1 rfl).elim
    | 1 => rfl
    | 2 => exact (hx.2 rfl).elim
    | n + 3 => rfl

/-- Example 8.4.1(i) (companion): both stored input terms have the stored
    common image under the displayed finite substitution. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_common_images_i :
    termSubstAll unifEx_t1_i unifEx_finite_mgu_i = unifEx_mci_i ∧
    termSubstAll unifEx_t2_i unifEx_finite_mgu_i = unifEx_mci_i 

/-- Example 8.4.1(i) (companion): the stored common image is exactly the
    printed term f(g(u),g(y)), with u = 3 and y = 1. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_mci_i_eq :
    unifEx_mci_i = Term.func (L := unificationExampleLanguage) UnifExFunc.f
      (unifVec2 (Term.func (L := unificationExampleLanguage) UnifExFunc.g (unifVec1 (Term.var 3)))
        (Term.func (L := unificationExampleLanguage) UnifExFunc.g (unifVec1 (Term.var 1)))) 

end LCS.FOResolution.Unification
end

