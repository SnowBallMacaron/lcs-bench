import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import Attach
import LCS.FOResolution.Unification.Substitutions.ProofsStamp

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

namespace SubstitutionCore

/-- The support D(sigma) of an arbitrary variable map:
    D(sigma) = {x | sigma(x) != var x}. -/
def substSupport {L : Language} (sigma : Nat → Term L) : Set Nat :=
  fun x => sigma x ≠ Term.var x

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

/-- A variable map with an explicit finite list containing its support.
    The list may include fixed variables; actual support is defined by inequality.
    Outside the list the map is the identity, as required by finite substitutions. -/
@[blueprint "chap8__definition_8_4_1"]
structure FiniteSubstitution (L : Language) where
  support : List Nat
  map : Nat → Term L
  outsideSupport : ∀ x, x ∉ support → map x = Term.var x

instance {L : Language} : CoeFun (FiniteSubstitution L) (fun _ => Nat → Term L) :=
  ⟨FiniteSubstitution.map⟩

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
-- Concrete equation-system foundation for Robinson unification
-- ===================================================================

/-- The identity substitution on first-order terms. -/
def identitySubst {L : Language} : Nat → Term L :=
  fun x => Term.var x

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

/-- Substitution composition is associative. -/
theorem SubstitutionCore.substCompose_assoc {L : Language}
    (rho theta sigma : Nat → Term L) :
    SubstitutionCore.substCompose rho (SubstitutionCore.substCompose theta sigma) =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose rho theta) sigma := by
-- BEGIN PROOF
  funext x
  unfold SubstitutionCore.substCompose
  exact SubstitutionCore.termSubstAll_compose (sigma x) theta rho

/-- The identity substitution is a right identity for composition. -/
theorem SubstitutionCore.substCompose_identity_right {L : Language}
    (sigma : Nat → Term L) :
    SubstitutionCore.substCompose sigma identitySubst = sigma := by
-- BEGIN PROOF
  rfl

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

end LCS.FOResolution.Unification
end
