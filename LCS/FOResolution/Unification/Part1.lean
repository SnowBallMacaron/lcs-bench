import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import Attach
import LCS.FOResolution.Unification.Part1.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

/-- Definition 8.4.1: The homomorphic extension sigma-hat applied to a
    term, the unique extension of sigma on variables to all terms. -/
@[blueprint "chap8__definition_8_4_1" (main := true)]
def termSubstAll {L : Language} : Term L → (Nat → Term L) → Term L
  | .var x, sigma => sigma x
  | .const c, _ => .const c
  | .func f ts, sigma => .func f (fun i => termSubstAll (ts i) sigma)

end LCS.FOResolution.Unification
end

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables
namespace SubstitutionCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The support D(sigma) of an arbitrary variable map:
    D(sigma) = {x | sigma(x) != var x}. -/
def substSupport {L : Language} (sigma : Nat → Term L) : Set Nat :=
  fun x => sigma x ≠ Term.var x

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- For an arbitrary variable map, I(sigma) is the union
    of FV(sigma(x)) for all x in D(sigma). -/
def substIntroduced {L : Language} (sigma : Nat → Term L) : Set Nat :=
  fun y => ∃ x, substSupport sigma x ∧ termFV (sigma x) y

/-- Ordinary functional composition of arbitrary variable maps: apply theta
    first, then sigma homomorphically. The finite source-facing operation below
    reverses these arguments to implement the book's left-first convention. -/
@[blueprint "chap8__definition_8_4_1"]
def substCompose {L : Language}
    (sigma : Nat → Term L) (theta : Nat → Term L) : Nat → Term L :=
  fun x => termSubstAll (theta x) sigma

end SubstitutionCore
end LCS.FOResolution.Unification
end

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A variable map with an explicit finite list containing its support.
    The list may include fixed variables; actual support is defined by inequality.
    Outside the list the map is the identity, as required by finite substitutions. -/
@[blueprint "chap8__definition_8_4_1"]
structure FiniteSubstitution (L : Language) where
  support : List Nat
  map : Nat → Term L
  outsideSupport : ∀ x, x ∉ support → map x = Term.var x

-- ATTACH-BLOCKER: unsupported untagged instance
instance {L : Language} : CoeFun (FiniteSubstitution L) (fun _ => Nat → Term L) :=
  ⟨FiniteSubstitution.map⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The finite identity substitution, with empty support witness. -/
@[blueprint "chap8__definition_8_4_1"]
def FiniteSubstitution.identity {L : Language} : FiniteSubstitution L where
  support := []
  map := Term.var
  outsideSupport := by intros; rfl

/-- Definition 8.4.1: D(sigma) is the actual support of a finite substitution,
    not necessarily the whole finite list witnessing its support. -/
@[blueprint "chap8__definition_8_4_1"]
def substSupport {L : Language} (sigma : FiniteSubstitution L) : Set Nat :=
  SubstitutionCore.substSupport sigma.map

/-- Definition 8.4.1: I(sigma) is the union of FV(sigma(x)) over x in D(sigma).
    Variables at fixed points of the map do not contribute. -/
@[blueprint "chap8__definition_8_4_1"]
def substIntroduced {L : Language} (sigma : FiniteSubstitution L) : Set Nat :=
  SubstitutionCore.substIntroduced sigma.map

/-- Definition 8.4.1: Source composition is left-first: sigma circ theta
    maps x to theta-hat(sigma(x)). The concatenated support witnesses ensure
    finite support; cancellations may make the actual support smaller. -/
@[blueprint "chap8__definition_8_4_1"]
def substCompose {L : Language}
    (sigma theta : FiniteSubstitution L) : FiniteSubstitution L where
  support := sigma.support ++ theta.support
  map := SubstitutionCore.substCompose theta.map sigma.map
  outsideSupport := by
    intro x hx
    have hs : x ∉ sigma.support := fun h => hx (List.mem_append_left _ h)
    have ht : x ∉ theta.support := fun h => hx (List.mem_append_right _ h)
    change termSubstAll (sigma.map x) theta.map = Term.var x
    rw [sigma.outsideSupport x hs]
    exact theta.outsideSupport x ht

-- ===================================================================
-- Definition 8.4.2: Unifier, most general unifier, term set variables,
-- and most common instance
-- ===================================================================

/-- Definition 8.4.2 (companion): Collect all variable indices occurring in a list of
terms S. The set of variables is the union of termFV(t) for all t in S. -/
@[blueprint "chap8__definition_8_4_2"]
def termSetVars {L : Language} (ts : List (Term L)) : Set Nat :=
  fun x => ∃ t, t ∈ ts ∧ termFV t x

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A general variable map sigma unifies a possibly empty finite term set S
    iff sigma-hat(t_1) = ... = sigma-hat(t_n) for all t_i in S. -/
@[blueprint "chap8__definition_8_4_2"]
def IsUnifierCore {L : Language} (sigma : Nat → Term L) (ts : List (Term L)) :
    Prop :=
  ∀ t1 t2, t1 ∈ ts → t2 ∈ ts →
    termSubstAll t1 sigma = termSubstAll t2 sigma

-- retained: used by LCS.FOResolution.Method.Completeness.Substitutions
/-- General-map MGU predicate, including empty input:
    sigma unifies S and every other unifier factors through sigma. -/
def IsMGUCore {L : Language} (sigma : Nat → Term L) (ts : List (Term L)) :
    Prop :=
  IsUnifierCore sigma ts ∧
  (SubstitutionCore.substSupport sigma ⊆ termSetVars ts) ∧
  (∀ sigma', IsUnifierCore sigma' ts →
    ∃ theta : Nat → Term L,
      ∀ x, sigma' x = SubstitutionCore.substCompose theta sigma x)

/-- Definition 8.4.2: a finite substitution unifies a nonempty finite term
    set exactly when all its input terms have the same substitution image. -/
@[blueprint "chap8__definition_8_4_2"]
def IsUnifier {L : Language} (sigma : FiniteSubstitution L) (ts : List (Term L)) :
    Prop :=
  ts ≠ [] ∧ IsUnifierCore sigma.map ts

/-- Definition 8.4.2: an MGU is a finite unifier of a nonempty finite term set,
    with actual support contained in the input variables. Every finite unifier
    factors through it by a finite substitution, globally on all variables,
    using the source's left-first composition. -/
@[blueprint "chap8__definition_8_4_2" (main := true)]
def IsMGU {L : Language} (sigma : FiniteSubstitution L) (ts : List (Term L)) :
    Prop :=
  IsUnifier sigma ts ∧
  (substSupport sigma ⊆ termSetVars ts) ∧
  (∀ sigma' : FiniteSubstitution L, IsUnifier sigma' ts →
    ∃ theta : FiniteSubstitution L, ∀ x, sigma' x = substCompose sigma theta x)

/-- Lemma 8.4.2 (companion): a finite MGU in the relaxed-support sense is
    a unifier of a nonempty finite term set through which every finite unifier
    factors globally. This removes only the requirement that its actual support
    be contained in the input variables; the ordinary IsMGU retains that clause. -/
@[blueprint "chap8__lemma_8_4_2"]
def IsMGURelaxed {L : Language} (sigma : FiniteSubstitution L)
    (ts : List (Term L)) : Prop :=
  IsUnifier sigma ts ∧
  (∀ sigma' : FiniteSubstitution L, IsUnifier sigma' ts →
    ∃ theta : FiniteSubstitution L, ∀ x, sigma' x = substCompose sigma theta x)

/-- Definition 8.4.2: the most common instance is the image of the first
    input under an MGU. Its MGU witness supplies nonemptiness; the defining
    computation selects an actual input term rather than an optional value. -/
@[blueprint "chap8__definition_8_4_2"]
def mostCommonInstance {L : Language} (sigma : FiniteSubstitution L)
    (ts : List (Term L)) (h : IsMGU sigma ts) : Term L :=
  termSubstAll (ts.head h.1.1) sigma

/-- Definition 8.4.2 (companion): every input image agrees with the most
    common instance determined by the MGU. -/
@[blueprint "chap8__definition_8_4_2"]
theorem mostCommonInstance_eq {L : Language} (sigma : FiniteSubstitution L)
    (ts : List (Term L)) (h : IsMGU sigma ts) (t : Term L) (ht : t ∈ ts) :
    mostCommonInstance sigma ts h = termSubstAll t sigma 

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Substitutions, LCS.FOResolution.Method.GroundExtension, LCS.FOResolution.Method.ResolutionTrees, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.FOResolution.Unification.Part2, LCS.SLD.FirstOrder.HornClauses, LCS.SLD.FirstOrder.Soundness
/-- Pairwise unification: a substitution `sigma` is a pairwise unifier of a
    list of term pairs `pairs` iff for every pair `(t1, t2) ∈ pairs`,
    `sigma-hat(t1) = sigma-hat(t2)`. This is the textbook unification problem
    formulated as a system of equations — each pair is its own equation,
    rather than collapsing all terms into a single "all equal" flat list.
    Used by SLD-resolution where the per-argument-position unification
    `termSubstAll (args_H i) sigma = args_A i` is naturally a pairwise
    problem, not a flat-list problem. -/
def IsPairwiseUnifier {L : Language} (sigma : Nat → Term L)
    (pairs : List (Term L × Term L)) : Prop :=
  ∀ p ∈ pairs, termSubstAll p.1 sigma = termSubstAll p.2 sigma

-- retained: used by LCS.FOResolution.Unification.Part2
/-- The variables occurring on either side of a finite system of term
    equations. This is the pairwise analogue of `termSetVars`. -/
def termPairSetVars {L : Language}
    (pairs : List (Term L × Term L)) : Set Nat :=
  fun x => ∃ p, p ∈ pairs ∧ (termFV p.1 x ∨ termFV p.2 x)

-- retained: used by LCS.FOResolution.Method.GroundExtension, LCS.FOResolution.Method.ResolutionTrees, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.FOResolution.Unification.Part2, LCS.SLD.FirstOrder.HornClauses, LCS.SLD.LogicProgramming.Correctness.RefutationExamples
/-- Pairwise most-general unifier: `sigma` is an MGU for a list of term pairs
    `pairs` iff `sigma` pairwise-unifies `pairs`, its support is contained in
    the variables of the equation system, and every other pairwise unifier
    factors through `sigma`. Pairwise analogue of `IsMGUCore`. -/
def IsPairwiseMGU {L : Language} (sigma : Nat → Term L)
    (pairs : List (Term L × Term L)) : Prop :=
  IsPairwiseUnifier sigma pairs ∧
  (SubstitutionCore.substSupport sigma ⊆ termPairSetVars pairs) ∧
  (∀ sigma', IsPairwiseUnifier sigma' pairs →
    ∃ theta : Nat → Term L,
      ∀ x, sigma' x = SubstitutionCore.substCompose theta sigma x)

-- ===================================================================
-- Concrete equation-system foundation for Robinson unification
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The identity substitution on first-order terms. -/
def identitySubst {L : Language} : Nat → Term L :=
  fun x => Term.var x

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Applying the identity substitution leaves a term unchanged. -/
theorem termSubstAll_identity {L : Language} (t : Term L) :
    termSubstAll t identitySubst = t := by
-- BEGIN PROOF
  induction t with
  | var x => rfl
  | const c => rfl
  | func f args ih =>
    simp only [termSubstAll]
    congr 1
    funext i
    exact ih i

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Simultaneous substitution composition: applying `sigma` and then `theta`
    equals applying `SubstitutionCore.substCompose theta sigma` once. -/
theorem SubstitutionCore.termSubstAll_compose {L : Language}
    (t : Term L) (sigma theta : Nat → Term L) :
    termSubstAll (termSubstAll t sigma) theta =
    termSubstAll t (SubstitutionCore.substCompose theta sigma) := by
-- BEGIN PROOF
  induction t with
  | var x => rfl
  | const c => rfl
  | func f args ih =>
    simp only [termSubstAll]
    congr 1
    funext i
    exact ih i

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Substitution composition is associative. -/
theorem SubstitutionCore.substCompose_assoc {L : Language}
    (rho theta sigma : Nat → Term L) :
    SubstitutionCore.substCompose rho (SubstitutionCore.substCompose theta sigma) =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose rho theta) sigma := by
-- BEGIN PROOF
  funext x
  unfold SubstitutionCore.substCompose
  exact SubstitutionCore.termSubstAll_compose (sigma x) theta rho

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The identity substitution is a left identity for composition. -/
theorem SubstitutionCore.substCompose_identity_left {L : Language}
    (sigma : Nat → Term L) :
    SubstitutionCore.substCompose identitySubst sigma = sigma := by
-- BEGIN PROOF
  funext x
  exact termSubstAll_identity (sigma x)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The identity substitution is a right identity for composition. -/
theorem SubstitutionCore.substCompose_identity_right {L : Language}
    (sigma : Nat → Term L) :
    SubstitutionCore.substCompose sigma identitySubst = sigma := by
-- BEGIN PROOF
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Composition can only change a variable already changed by one of its two
    component substitutions. -/
theorem SubstitutionCore.substSupport_compose_subset {L : Language}
    (theta sigma : Nat → Term L) :
    SubstitutionCore.substSupport (SubstitutionCore.substCompose theta sigma) ⊆
      SubstitutionCore.substSupport theta ∪ SubstitutionCore.substSupport sigma := by
-- BEGIN PROOF
  intro x hx
  by_cases hSigma : SubstitutionCore.substSupport sigma x
  · exact Or.inr hSigma
  · apply Or.inl
    unfold SubstitutionCore.substSupport
    intro hTheta
    apply hx
    unfold SubstitutionCore.substCompose
    have hSigmaEq : sigma x = Term.var x :=
      Classical.byContradiction fun h => hSigma h
    rw [hSigmaEq]
    exact hTheta

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Two finite substitutions with the same support witness and pointwise map
    are equal; the outside-support proof carries no extra data. -/
theorem FiniteSubstitution.ext {L : Language} {sigma theta : FiniteSubstitution L}
    (hSupport : sigma.support = theta.support) (hMap : ∀ x, sigma x = theta x) :
    sigma = theta := by
  cases sigma with
  | mk ss sm sh =>
    cases theta with
    | mk ts tm th =>
      cases hSupport
      have hm : sm = tm := funext hMap
      cases hm
      rfl

/-- Definition 8.4.1 (companion): the homomorphic extension of left-first
    finite composition applies sigma and then theta. -/
@[blueprint "chap8__definition_8_4_1"]
theorem termSubstAll_compose {L : Language}
    (t : Term L) (sigma theta : FiniteSubstitution L) :
    termSubstAll (termSubstAll t sigma) theta =
      termSubstAll t (substCompose sigma theta) 

/-- Definition 8.4.1 (companion): left-first finite composition is associative,
    including its concatenated finite support witnesses. -/
@[blueprint "chap8__definition_8_4_1"]
theorem substCompose_assoc {L : Language}
    (sigma theta rho : FiniteSubstitution L) :
    substCompose (substCompose sigma theta) rho =
      substCompose sigma (substCompose theta rho) 

/-- Definition 8.4.1 (companion): the finite identity is a left identity. -/
@[blueprint "chap8__definition_8_4_1"]
theorem substCompose_identity_left {L : Language} (sigma : FiniteSubstitution L) :
    substCompose FiniteSubstitution.identity sigma = sigma 

/-- Definition 8.4.1 (companion): the finite identity is a right identity. -/
@[blueprint "chap8__definition_8_4_1"]
theorem substCompose_identity_right {L : Language} (sigma : FiniteSubstitution L) :
    substCompose sigma FiniteSubstitution.identity = sigma 

/-- Definition 8.4.1 (companion): actual support of finite composition is
    contained in the union of the actual supports of its two arguments. -/
@[blueprint "chap8__definition_8_4_1"]
theorem substSupport_compose_subset {L : Language}
    (sigma theta : FiniteSubstitution L) :
    substSupport (substCompose sigma theta) ⊆ substSupport sigma ∪ substSupport theta 

-- retained: used by LCS.FOResolution.Unification.Part3
/-- Free variables after simultaneous substitution are exactly the variables
    appearing in the image of an original free variable. -/
theorem termFV_termSubstAll {L : Language}
    (t : Term L) (sigma : Nat → Term L) (y : Nat) :
    termFV (termSubstAll t sigma) y ↔
      ∃ x, termFV t x ∧ termFV (sigma x) y := by
-- BEGIN PROOF
  induction t with
  | var x =>
      simp only [termSubstAll, termFV, Set.singleton]
      constructor
      · intro hy
        exact ⟨x, rfl, hy⟩
      · rintro ⟨z, hz, hy⟩
        subst z
        exact hy
  | const c =>
      simp only [termSubstAll, termFV, Set.empty]
      exact ⟨nofun, fun ⟨_, h, _⟩ => h.elim⟩
  | func f args ih =>
      simp only [termSubstAll, termFV, Set.iUnion]
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨x, hx, hy⟩ := (ih i).mp hi
        exact ⟨x, ⟨i, hx⟩, hy⟩
      · rintro ⟨x, ⟨i, hx⟩, hy⟩
        exact ⟨i, (ih i).mpr ⟨x, hx, hy⟩⟩

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

-- retained: used by LCS.FOResolution.Unification.Part3
/-- Simultaneous substitutions agreeing on all free variables of a term give
    the same substituted term. -/
theorem termSubstAll_ext_on_fv {L : Language}
    (t : Term L) (sigma theta : Nat → Term L)
    (h : ∀ x, termFV t x → sigma x = theta x) :
    termSubstAll t sigma = termSubstAll t theta := by
-- BEGIN PROOF
  induction t with
  | var x =>
      exact h x rfl
  | const c =>
      rfl
  | func f args ih =>
      simp only [termSubstAll]
      congr 1
      funext i
      exact ih i (fun x hx => h x ⟨i, hx⟩)

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

end LCS.FOResolution.Unification
end

