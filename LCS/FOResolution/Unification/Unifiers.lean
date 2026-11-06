import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import Attach
import LCS.FOResolution.Unification.Unifiers.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

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

end LCS.FOResolution.Unification
end
