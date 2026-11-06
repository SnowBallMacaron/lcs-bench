import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

-- retained: used by LCS.FOResolution.Unification.Part2
/-- The elementary substitution `[t/x]`: replace `x` by `t` and leave every
    other variable fixed. -/
def elementarySubst {L : Language} (x : Nat) (t : Term L) :
    Nat → Term L :=
  fun y => if y = x then t else Term.var y

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Apply a substitution to both sides of every equation in a finite system. -/
def substEquationSystem {L : Language} (sigma : Nat → Term L)
    (pairs : List (Term L × Term L)) : List (Term L × Term L) :=
  pairs.map fun p => (termSubstAll p.1 sigma, termSubstAll p.2 sigma)

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Computable occurs check for a variable in a concrete first-order term. -/
def termOccurs {L : Language} (x : Nat) : Term L → Bool
  | .var y => x == y
  | .const _ => false
  | .func _ args => (List.ofFn fun i => termOccurs x (args i)).any id

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Compatibility of the outer constructors of two terms. Variables are
    compatible with every term; constants and functions must have the same
    symbol, and constants cannot be compatible with function applications. -/
def TermHeadsCompatible {L : Language} : Term L → Term L → Prop
  | .var _, _ => True
  | _, .var _ => True
  | .const c, .const d => c = d
  | .func f _, .func g _ => f = g
  | _, _ => False

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- The four successful transformations performed by one Robinson step. -/
inductive RobinsonStepKind : Type where
  | delete
  | orient
  | eliminate
  | decompose

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Visible failure reasons for one Robinson step. -/
inductive RobinsonFailure : Type where
  | occursCheck
  | symbolClash

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Result of one deterministic Robinson transformation. A successful
    transformation records its elementary substitution and the next equation
    system; it does not claim that repeated stepping terminates. -/
inductive RobinsonStepResult (L : Language) : Type where
  | solved
  | next (kind : RobinsonStepKind)
      (substitution : Nat → Term L)
      (equations : List (Term L × Term L))
  | failure (reason : RobinsonFailure)

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Pair corresponding arguments of two applications of the same function
    symbol. The equality proof transports the second argument vector to the
    arity of the first symbol. -/
def functionEquationPairs {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L) :
    List (Term L × Term L) :=
  match hfg with
  | rfl => List.ofFn fun i => (ss i, ts i)

-- retained: used by LCS.FOResolution.Unification.Part2
/-- One deterministic Robinson transformation on a finite equation system.
    It deletes a reflexive equation, orients a variable to the left, eliminates
    a non-occurring variable, decomposes equal function symbols position-wise,
    and reports symbol-clash or occurs-check failures explicitly. -/
noncomputable def robinsonStep {L : Language}
    (pairs : List (Term L × Term L)) : RobinsonStepResult L := by
  classical
  exact match pairs with
  | [] => .solved
  | (s, t) :: rest =>
      if hst : s = t then
        .next .delete identitySubst rest
      else
        match s, t with
        | .var x, t =>
            if termOccurs x t then
              .failure .occursCheck
            else
              let delta := elementarySubst x t
              .next .eliminate delta (substEquationSystem delta rest)
        | s, .var x =>
            .next .orient identitySubst ((Term.var x, s) :: rest)
        | .const _, .const _ =>
            .failure .symbolClash
        | .const _, .func _ _ =>
            .failure .symbolClash
        | .func _ _, .const _ =>
            .failure .symbolClash
        | .func f ss, .func g ts =>
            if hfg : f = g then
              .next .decompose identitySubst
                (functionEquationPairs hfg ss ts ++ rest)
            else
              .failure .symbolClash

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Correctness of the computable occurs check. -/
theorem termOccurs_eq_true_iff {L : Language} (x : Nat) (t : Term L) :
    termOccurs x t = true ↔ termFV t x := by
-- BEGIN PROOF
  induction t with
  | var y =>
      change (x == y) = true ↔ x = y
      exact beq_iff_eq
  | const c =>
      simp [termOccurs, termFV, Set.empty]
  | func f args ih =>
      simp only [termOccurs, List.any_eq_true, id_eq, termFV, Set.iUnion]
      constructor
      · rintro ⟨b, hbMem, hb⟩
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hbMem
        exact ⟨i, (ih i).mp (hi.trans hb)⟩
      · rintro ⟨i, hi⟩
        exact ⟨termOccurs x (args i),
          List.mem_ofFn.mpr ⟨i, rfl⟩, (ih i).mpr hi⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Substituting into a term cannot change its outer rigid constructor or
    symbol. Consequently, equal substitution instances have compatible heads. -/
theorem termHeadsCompatible_of_subst_eq {L : Language}
    (s t : Term L) (sigma : Nat → Term L)
    (hEq : termSubstAll s sigma = termSubstAll t sigma) :
    TermHeadsCompatible s t := by
-- BEGIN PROOF
  cases s with
  | var x => trivial
  | const c =>
      cases t with
      | var y => trivial
      | const d => exact Term.const.inj hEq
      | func g args =>
          simp only [termSubstAll] at hEq
          cases hEq
  | func f args =>
      cases t with
      | var y => trivial
      | const d =>
          simp only [termSubstAll] at hEq
          cases hEq
      | func g args' => exact (Term.func.inj hEq).1

-- retained: used by LCS.FOResolution.Unification.Part2
/-- An elementary substitution fixes a term in which its variable does not
    occur. -/
theorem termSubstAll_elementary_of_not_fv {L : Language}
    (x : Nat) (u t : Term L) (hNot : ¬ termFV t x) :
    termSubstAll t (elementarySubst x u) = t := by
-- BEGIN PROOF
  calc
    termSubstAll t (elementarySubst x u) =
        termSubstAll t identitySubst := by
      apply termSubstAll_ext_on_fv
      intro y hy
      unfold elementarySubst identitySubst
      split
      · next hEq =>
        subst y
        exact (hNot hy).elim
      · rfl
    _ = t := termSubstAll_identity t

-- retained: used by LCS.FOResolution.Unification.Part2
/-- The support of an elementary substitution is contained in its bound
    variable. -/
theorem elementarySubst_support_subset {L : Language}
    (x : Nat) (t : Term L) :
    SubstitutionCore.substSupport (elementarySubst x t) ⊆ Set.singleton x := by
-- BEGIN PROOF
  intro y hy
  unfold SubstitutionCore.substSupport elementarySubst at hy
  by_cases hxy : y = x
  · exact hxy
  · simp only [if_neg hxy] at hy
    exact (hy rfl).elim

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Every unifier of the equation `x = t` factors through its elementary
    substitution, with the original unifier as the residual substitution. -/
theorem elementarySubst_factor_of_var_eq {L : Language}
    (x : Nat) (t : Term L) (sigma : Nat → Term L)
    (hEq : sigma x = termSubstAll t sigma) :
    ∀ y, sigma y = SubstitutionCore.substCompose sigma (elementarySubst x t) y := by
-- BEGIN PROOF
  intro y
  unfold SubstitutionCore.substCompose elementarySubst
  by_cases hyx : y = x
  · subst y
    simp only [if_pos]
    exact hEq
  · simp only [if_neg hyx, termSubstAll]

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Pairwise unification of a nonempty equation system splits into its head
    equation and tail system. -/
theorem isPairwiseUnifier_cons_iff {L : Language}
    (sigma : Nat → Term L) (p : Term L × Term L)
    (pairs : List (Term L × Term L)) :
    IsPairwiseUnifier sigma (p :: pairs) ↔
      termSubstAll p.1 sigma = termSubstAll p.2 sigma ∧
      IsPairwiseUnifier sigma pairs := by
-- BEGIN PROOF
  constructor
  · intro h
    exact ⟨h p List.mem_cons_self,
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))⟩
  · rintro ⟨hp, hrest⟩ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hrest q hq

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Pairwise unification distributes over concatenated equation systems. -/
theorem isPairwiseUnifier_append_iff {L : Language}
    (sigma : Nat → Term L)
    (left right : List (Term L × Term L)) :
    IsPairwiseUnifier sigma (left ++ right) ↔
      IsPairwiseUnifier sigma left ∧ IsPairwiseUnifier sigma right := by
-- BEGIN PROOF
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append.mpr (Or.inl hp)),
      fun p hp => h p (List.mem_append.mpr (Or.inr hp))⟩
  · rintro ⟨hleft, hright⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hleft p hp
    · exact hright p hp

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Variables of a nonempty equation system split into the variables of its
    head equation and those of its tail. -/
theorem termPairSetVars_cons_iff {L : Language}
    (p : Term L × Term L) (pairs : List (Term L × Term L)) (x : Nat) :
    termPairSetVars (p :: pairs) x ↔
      (termFV p.1 x ∨ termFV p.2 x) ∨ termPairSetVars pairs x := by
-- BEGIN PROOF
  constructor
  · rintro ⟨q, hq, hVars⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inl hVars
    · exact Or.inr ⟨q, hq, hVars⟩
  · rintro (hHead | ⟨q, hq, hVars⟩)
    · exact ⟨p, List.mem_cons_self, hHead⟩
    · exact ⟨q, List.mem_cons.mpr (Or.inr hq), hVars⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Variables of concatenated equation systems are the union of the variables
    of the two component systems. -/
theorem termPairSetVars_append_iff {L : Language}
    (left right : List (Term L × Term L)) (x : Nat) :
    termPairSetVars (left ++ right) x ↔
      termPairSetVars left x ∨ termPairSetVars right x := by
-- BEGIN PROOF
  constructor
  · rintro ⟨p, hp, hVars⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl ⟨p, hp, hVars⟩
    · exact Or.inr ⟨p, hp, hVars⟩
  · rintro (⟨p, hp, hVars⟩ | ⟨p, hp, hVars⟩)
    · exact ⟨p, List.mem_append.mpr (Or.inl hp), hVars⟩
    · exact ⟨p, List.mem_append.mpr (Or.inr hp), hVars⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Unifying a substituted equation system by `theta` is equivalent to
    unifying the original system by the composed substitution. -/
theorem isPairwiseUnifier_substEquationSystem_iff {L : Language}
    (pairs : List (Term L × Term L))
    (sigma theta : Nat → Term L) :
    IsPairwiseUnifier theta (substEquationSystem sigma pairs) ↔
      IsPairwiseUnifier (SubstitutionCore.substCompose theta sigma) pairs := by
-- BEGIN PROOF
  constructor
  · intro h p hp
    have hMem :
        (termSubstAll p.1 sigma, termSubstAll p.2 sigma) ∈
          substEquationSystem sigma pairs := by
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hEq := h _ hMem
    simpa only [SubstitutionCore.termSubstAll_compose] using hEq
  · intro h q hq
    obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
    subst q
    simpa only [SubstitutionCore.termSubstAll_compose] using h p hp

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Exact free-variable characterization for a substituted equation system. -/
theorem termPairSetVars_substEquationSystem_iff {L : Language}
    (pairs : List (Term L × Term L))
    (sigma : Nat → Term L) (y : Nat) :
    termPairSetVars (substEquationSystem sigma pairs) y ↔
      ∃ x, termPairSetVars pairs x ∧ termFV (sigma x) y := by
-- BEGIN PROOF
  constructor
  · rintro ⟨q, hq, hqVars⟩
    obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
    subst q
    rcases hqVars with hleft | hright
    · obtain ⟨x, hx, hy⟩ :=
        (termFV_termSubstAll p.1 sigma y).mp hleft
      exact ⟨x, ⟨p, hp, Or.inl hx⟩, hy⟩
    · obtain ⟨x, hx, hy⟩ :=
        (termFV_termSubstAll p.2 sigma y).mp hright
      exact ⟨x, ⟨p, hp, Or.inr hx⟩, hy⟩
  · rintro ⟨x, ⟨p, hp, hpVars⟩, hy⟩
    refine ⟨(termSubstAll p.1 sigma, termSubstAll p.2 sigma),
      List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    rcases hpVars with hleft | hright
    · exact Or.inl ((termFV_termSubstAll p.1 sigma y).mpr
        ⟨x, hleft, hy⟩)
    · exact Or.inr ((termFV_termSubstAll p.2 sigma y).mpr
        ⟨x, hright, hy⟩)

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Eliminating `x` cannot introduce variables outside the original equation
    `x = t` and the remaining system. -/
theorem elementarySubst_system_vars_subset {L : Language}
    (x : Nat) (t : Term L) (pairs : List (Term L × Term L)) :
    termPairSetVars
        (substEquationSystem (elementarySubst x t) pairs) ⊆
      termPairSetVars ((Term.var x, t) :: pairs) := by
-- BEGIN PROOF
  intro y hy
  obtain ⟨z, hzPairs, hyImage⟩ :=
    (termPairSetVars_substEquationSystem_iff
      pairs (elementarySubst x t) y).mp hy
  unfold elementarySubst at hyImage
  by_cases hzx : z = x
  · subst z
    simp only [if_pos] at hyImage
    exact ⟨(Term.var x, t), List.mem_cons_self, Or.inr hyImage⟩
  · simp only [if_neg hzx, termFV, Set.singleton] at hyImage
    subst y
    obtain ⟨p, hp, hpVars⟩ := hzPairs
    exact ⟨p, List.mem_cons.mpr (Or.inr hp), hpVars⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- When the occurs check succeeds, eliminating `x` removes `x` from the
    transformed tail system. -/
theorem elementarySubst_removed_var {L : Language}
    (x : Nat) (t : Term L) (pairs : List (Term L × Term L))
    (hNot : ¬ termFV t x) :
    ¬ termPairSetVars
      (substEquationSystem (elementarySubst x t) pairs) x := by
-- BEGIN PROOF
  intro hx
  obtain ⟨z, _, hxImage⟩ :=
    (termPairSetVars_substEquationSystem_iff
      pairs (elementarySubst x t) x).mp hx
  unfold elementarySubst at hxImage
  by_cases hzx : z = x
  · subst z
    simp only [if_pos] at hxImage
    exact hNot hxImage
  · simp only [if_neg hzx, termFV, Set.singleton] at hxImage
    exact hzx hxImage.symm

-- retained: used by LCS.FOResolution.Unification.Part2, LCS.FOResolution.Unification.Part3
/-- An occurrence of `x` in `t` makes the substituted image of `x` no larger
    than the substituted image of `t`. -/
theorem termSize_le_subst_of_fv {L : Language}
    (t : Term L) (sigma : Nat → Term L) (x : Nat)
    (hx : termFV t x) :
    termSize (sigma x) ≤ termSize (termSubstAll t sigma) := by
-- BEGIN PROOF
  induction t with
  | var y =>
      have hxy : x = y := hx
      subst y
      exact Nat.le_refl _
  | const c =>
      exact hx.elim
  | func f args ih =>
      obtain ⟨i, hi⟩ := hx
      exact Nat.le_trans (ih i hi)
        (Nat.le_of_lt
          (term_sizeOf_func_gt f
            (fun j => termSubstAll (args j) sigma) i))

-- retained: used by LCS.FOResolution.Unification.Part2, LCS.FOResolution.Unification.Part3
/-- A proper occurrence is strictly smaller after every simultaneous
    substitution. This is the finite-term core of the occurs check. -/
theorem termSize_lt_subst_of_proper_fv {L : Language}
    (t : Term L) (sigma : Nat → Term L) (x : Nat)
    (hNe : t ≠ Term.var x) (hx : termFV t x) :
    termSize (sigma x) < termSize (termSubstAll t sigma) := by
-- BEGIN PROOF
  cases t with
  | var y =>
      have hxy : x = y := hx
      subst y
      exact (hNe rfl).elim
  | const c =>
      exact hx.elim
  | func f args =>
      obtain ⟨i, hi⟩ := hx
      exact Nat.lt_of_le_of_lt
        (termSize_le_subst_of_fv (args i) sigma x hi)
        (term_sizeOf_func_gt f
          (fun j => termSubstAll (args j) sigma) i)

-- retained: used by LCS.FOResolution.Unification.Part2, LCS.FOResolution.Unification.Part3
/-- A genuine occurs-check equation `x = t`, where `t ≠ x`, has no unifier. -/
theorem var_occurs_not_unifiable {L : Language}
    (x : Nat) (t : Term L)
    (hNe : t ≠ Term.var x) (hOccurs : termOccurs x t = true) :
    ¬ ∃ sigma : Nat → Term L,
      termSubstAll (Term.var x) sigma = termSubstAll t sigma := by
-- BEGIN PROOF
  rintro ⟨sigma, hEq⟩
  have hlt := termSize_lt_subst_of_proper_fv t sigma x hNe
    ((termOccurs_eq_true_iff x t).mp hOccurs)
  simp only [termSubstAll] at hEq
  rw [← hEq] at hlt
  exact Nat.lt_irrefl _ hlt

-- retained: used by LCS.FOResolution.Unification.Part2
/-- A system whose head equation has incompatible rigid constructors is not
    unifiable. -/
theorem incompatible_head_not_pairwise_unifiable {L : Language}
    (s t : Term L) (pairs : List (Term L × Term L))
    (hIncompatible : ¬ TermHeadsCompatible s t) :
    ¬ ∃ sigma : Nat → Term L,
      IsPairwiseUnifier sigma ((s, t) :: pairs) := by
-- BEGIN PROOF
  rintro ⟨sigma, hUnif⟩
  exact hIncompatible
    (termHeadsCompatible_of_subst_eq s t sigma
      (hUnif (s, t) List.mem_cons_self))

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Unifying the position-wise decomposition of equal function symbols is
    equivalent to unifying the original function equation. -/
theorem isPairwiseUnifier_functionEquationPairs_iff {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L)
    (sigma : Nat → Term L) :
    IsPairwiseUnifier sigma (functionEquationPairs hfg ss ts) ↔
      termSubstAll (Term.func f ss) sigma =
        termSubstAll (Term.func g ts) sigma := by
-- BEGIN PROOF
  subst g
  constructor
  · intro h
    simp only [termSubstAll]
    congr 1
    funext i
    exact h (ss i, ts i)
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    subst p
    simp only [termSubstAll] at h
    have hArgs := eq_of_heq (Term.func.inj h).2
    exact congrFun hArgs i

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Position-wise decomposition contains exactly the variables of the two
    original function applications. -/
theorem termPairSetVars_functionEquationPairs_iff {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L)
    (x : Nat) :
    termPairSetVars (functionEquationPairs hfg ss ts) x ↔
      termFV (Term.func f ss) x ∨ termFV (Term.func g ts) x := by
-- BEGIN PROOF
  subst g
  constructor
  · rintro ⟨p, hp, hVars⟩
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    subst p
    rcases hVars with hVars | hVars
    · exact Or.inl ⟨i, hVars⟩
    · exact Or.inr ⟨i, hVars⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨(ss i, ts i), List.mem_ofFn.mpr ⟨i, rfl⟩, Or.inl hi⟩
    · exact ⟨(ss i, ts i), List.mem_ofFn.mpr ⟨i, rfl⟩, Or.inr hi⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Delete preserves exactly the solutions of the remaining system. -/
theorem isPairwiseUnifier_delete_iff {L : Language}
    (t : Term L) (pairs : List (Term L × Term L))
    (sigma : Nat → Term L) :
    IsPairwiseUnifier sigma ((t, t) :: pairs) ↔
      IsPairwiseUnifier sigma pairs := by
-- BEGIN PROOF
  rw [isPairwiseUnifier_cons_iff]
  exact and_iff_right rfl

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Orienting an equation with a right-hand variable preserves its solutions. -/
theorem isPairwiseUnifier_orient_iff {L : Language}
    (x : Nat) (t : Term L) (pairs : List (Term L × Term L))
    (sigma : Nat → Term L) :
    IsPairwiseUnifier sigma ((t, Term.var x) :: pairs) ↔
      IsPairwiseUnifier sigma ((Term.var x, t) :: pairs) := by
-- BEGIN PROOF
  rw [isPairwiseUnifier_cons_iff, isPairwiseUnifier_cons_iff]
  constructor
  · rintro ⟨hEq, hrest⟩
    exact ⟨hEq.symm, hrest⟩
  · rintro ⟨hEq, hrest⟩
    exact ⟨hEq.symm, hrest⟩

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Decomposing equal function symbols position-wise preserves exactly the
    solutions of the original equation and tail system. -/
theorem isPairwiseUnifier_decompose_iff {L : Language}
    {f g : L.funSymbols} (hfg : f = g)
    (ss : Fin (L.funArity f) → Term L)
    (ts : Fin (L.funArity g) → Term L)
    (pairs : List (Term L × Term L))
    (sigma : Nat → Term L) :
    IsPairwiseUnifier sigma
        (functionEquationPairs hfg ss ts ++ pairs) ↔
      IsPairwiseUnifier sigma
        ((Term.func f ss, Term.func g ts) :: pairs) := by
-- BEGIN PROOF
  rw [isPairwiseUnifier_append_iff, isPairwiseUnifier_cons_iff,
    isPairwiseUnifier_functionEquationPairs_iff]

-- retained: used by LCS.FOResolution.Unification.Part2
/-- Elimination gives the exact solution factorization used by Robinson's
    algorithm: solutions of `x = t :: E` are precisely substitutions
    factoring through `[t/x]` from a solution of `[t/x](E)`. -/
theorem isPairwiseUnifier_eliminate_iff {L : Language}
    (x : Nat) (t : Term L) (pairs : List (Term L × Term L))
    (hNot : ¬ termFV t x) (sigma : Nat → Term L) :
    IsPairwiseUnifier sigma ((Term.var x, t) :: pairs) ↔
      ∃ theta : Nat → Term L,
        IsPairwiseUnifier theta
          (substEquationSystem (elementarySubst x t) pairs) ∧
        ∀ y, sigma y =
          SubstitutionCore.substCompose theta (elementarySubst x t) y := by
-- BEGIN PROOF
  constructor
  · intro hUnif
    obtain ⟨hHead, hRest⟩ :=
      (isPairwiseUnifier_cons_iff sigma (Term.var x, t) pairs).mp hUnif
    refine ⟨sigma, ?_, elementarySubst_factor_of_var_eq x t sigma hHead⟩
    rw [isPairwiseUnifier_substEquationSystem_iff]
    have hFactor := elementarySubst_factor_of_var_eq x t sigma hHead
    have hSigma : sigma =
        SubstitutionCore.substCompose sigma (elementarySubst x t) :=
      funext hFactor
    rwa [← hSigma]
  · rintro ⟨theta, hNext, hFactor⟩
    have hSigma : sigma =
        SubstitutionCore.substCompose theta (elementarySubst x t) :=
      funext hFactor
    apply (isPairwiseUnifier_cons_iff sigma
      (Term.var x, t) pairs).mpr
    constructor
    · rw [hSigma]
      calc
        termSubstAll (Term.var x)
            (SubstitutionCore.substCompose theta (elementarySubst x t)) =
            termSubstAll t theta := by
              simp only [termSubstAll, SubstitutionCore.substCompose, elementarySubst,
                if_pos]
        _ = termSubstAll
              (termSubstAll t (elementarySubst x t)) theta := by
              rw [termSubstAll_elementary_of_not_fv x t t hNot]
        _ = termSubstAll t
              (SubstitutionCore.substCompose theta (elementarySubst x t)) :=
              SubstitutionCore.termSubstAll_compose t (elementarySubst x t) theta
    · rw [hSigma]
      exact (isPairwiseUnifier_substEquationSystem_iff
        pairs (elementarySubst x t) theta).mp hNext

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

end LCS.FOResolution.Unification
end
