import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers
import Attach
import LCS.FOResolution.Unification.MGUUniqueness.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Lemma 8.4.2: Essential uniqueness of most general unifiers
-- ===================================================================

/-- Lemma 8.4.2 (companion): A substitution rho is a variable-to-variable
    map (renaming) on a domain set A if for every x in A, rho(x) is a
    variable. -/
@[blueprint "chap8__lemma_8_4_2"]
def IsVarRenaming {L : Language} (rho : Nat → Term L)
    (A : Set Nat) : Prop :=
  ∀ x, A x → ∃ y, rho x = Term.var y

/-- Lemma 8.4.2 (companion): a variable map is a bijective renaming from
    A to B when it maps A into B and admits an inverse mapping B into A,
    with both round trips equal to the identity on the respective sets.
    The maps outside A and B are irrelevant to this restricted bijection. -/
@[blueprint "chap8__lemma_8_4_2"]
def IsBijectiveRenaming {L : Language} (rho : Nat → Term L)
    (A B : Set Nat) : Prop :=
  IsVarRenaming rho A ∧
  (∀ x, A x → ∃ y, B y ∧ rho x = Term.var y) ∧
  ∃ rho_inv : Nat → Term L,
    IsVarRenaming rho_inv B ∧
    (∀ y, B y → ∃ x, A x ∧ rho_inv y = Term.var x) ∧
    (∀ x, A x → termSubstAll (rho x) rho_inv = Term.var x) ∧
    (∀ y, B y → termSubstAll (rho_inv y) rho = Term.var y)

-- In the source's left-first convention, theta = sigma ∘ rho means
-- theta(x) = rho-hat(sigma(x)), represented for general maps below by
-- SubstitutionCore.substCompose rho sigma. The printed support equality is
-- subject to the support-inclusion erratum (SQ18); it is not a consequence
-- of choosing the opposite composition order.

-- Helper: termSubstAll (var x) sigma = sigma x
-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
theorem termSubstAll_var {L : Language} (x : Nat) (sigma : Nat → Term L) :
    termSubstAll (Term.var x) sigma = sigma x := by
-- BEGIN PROOF
  rfl

-- Helper: if termSubstAll t sigma = var x, then t must be a variable

-- Helper: if a compose roundtrip holds (termSubstAll (termSubstAll t rho) rho' = t),
-- then for every y in FV(t), rho y is a variable with a round-trip via rho'.

/-- Lemma 8.4.2 (companion): two finite relaxed-support MGUs admit one
    finite renaming rho such that
    theta = sigma circ rho in the source's left-first convention. The same
    rho bijects the stated introduced/support-difference sets, has support
    contained in its source set (the SQ18 erratum), and is variable-valued
    on its support. Exact support equality is not asserted. -/
@[blueprint "chap8__lemma_8_4_2"]
theorem mgu_unique_up_to_renaming_relaxed {L : Language}
    (S : List (Term L)) (sigma theta : FiniteSubstitution L)
    (h_sigma : IsMGURelaxed sigma S) (h_theta : IsMGURelaxed theta S) :
    ∃ rho : FiniteSubstitution L,
      (∀ x, theta x = substCompose sigma rho x) ∧
      IsBijectiveRenaming rho
        (substIntroduced sigma ∪ (substSupport theta \ substSupport sigma))
        (substIntroduced theta ∪ (substSupport sigma \ substSupport theta)) ∧
      (substSupport rho ⊆
        substIntroduced sigma ∪ (substSupport theta \ substSupport sigma)) ∧
      IsVarRenaming rho (substSupport rho) 

/-- Lemma 8.4.2: two finite MGUs admit one finite renaming rho such that
    theta = sigma circ rho in the source's left-first convention. The same
    rho bijects the stated introduced/support-difference sets, has support
    contained in its source set (the SQ18 erratum), and is variable-valued
    on its support. Exact support equality is not asserted. -/
@[blueprint "chap8__lemma_8_4_2" (main := true)]
theorem mgu_unique_up_to_renaming {L : Language}
    (S : List (Term L)) (sigma theta : FiniteSubstitution L)
    (h_sigma : IsMGU sigma S) (h_theta : IsMGU theta S) :
    ∃ rho : FiniteSubstitution L,
      (∀ x, theta x = substCompose sigma rho x) ∧
      IsBijectiveRenaming rho
        (substIntroduced sigma ∪ (substSupport theta \ substSupport sigma))
        (substIntroduced theta ∪ (substSupport sigma \ substSupport theta)) ∧
      (substSupport rho ⊆
        substIntroduced sigma ∪ (substSupport theta \ substSupport sigma)) ∧
      IsVarRenaming rho (substSupport rho) 

end LCS.FOResolution.Unification
end
