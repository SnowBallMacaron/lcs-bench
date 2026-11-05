import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Part1
import LCS.FOResolution.Unification.Part2
import Attach
import LCS.FOResolution.Unification.Part3.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

/-- Example 8.4.1(i) (companion): the displayed finite substitution is an
    MGU of the two stored terms, including input-bounded support and global
    factorization of every finite unifier. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_isMGU_i :
    IsMGU unifEx_finite_mgu_i [unifEx_t1_i, unifEx_t2_i] 

/-- Example 8.4.1(i) (companion): the MGU-guarded common-instance operation
    returns the stored common image. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_mostCommonInstance_i :
    mostCommonInstance unifEx_finite_mgu_i [unifEx_t1_i, unifEx_t2_i]
      unifEx_isMGU_i = unifEx_mci_i 

/-- Example 8.4.1: t_1 = f(x, g(y)) from subcase (ii), the first term in
the symbol clash pair. Variables: x = 0, y = 1. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t1_ii : Term unificationExampleLanguage :=
  Term.func UnifExFunc.f
    (unifVec2 (Term.var 0)
      (Term.func UnifExFunc.g (unifVec1 (Term.var 1))))

/-- Example 8.4.1: t_2 = f(g(u), h(z)) from subcase (ii); symbol clash
    demonstrates non-unifiability because g != h. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t2_ii : Term unificationExampleLanguage :=
  Term.func UnifExFunc.f
    (unifVec2
      (Term.func UnifExFunc.g (unifVec1 (Term.var 3)))
      (Term.func UnifExFunc.h (unifVec1 (Term.var 2))))

/-- Example 8.4.1(ii) (companion): any alleged unifier of the binary
    pair would identify the fixed, distinct unary function symbols g and h. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_symbol_clash_ii
    (sigma : FiniteSubstitution unificationExampleLanguage)
    (h : IsUnifier sigma [unifEx_t1_ii, unifEx_t2_ii]) :
    UnifExFunc.g = UnifExFunc.h 

/-- Example 8.4.1(ii) (companion): the binary symbol-clash pair has no
    finite unifier. Substitution changes variables, not the fixed symbols. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_not_unifiable_ii :
    ¬ ∃ sigma : FiniteSubstitution unificationExampleLanguage,
      IsUnifier sigma [unifEx_t1_ii, unifEx_t2_ii] 

-- For part (iii) we need a ternary f. We model this with a separate
-- language that gives f arity 3.

/-- Example 8.4.1 (companion): Function symbols for the ternary example:
f3 (arity 3), g (arity 1). -/
@[blueprint "chap8__example_8_4_1"]
inductive UnifExFunc3 : Type where
  | f3 : UnifExFunc3
  | g : UnifExFunc3

/-- Example 8.4.1 (companion): A language variant where f has arity 3 and
g has arity 1, used for the occurs-check example (iii). -/
@[blueprint "chap8__example_8_4_1"]
def unificationExampleLanguage3 : Language where
  funSymbols := UnifExFunc3
  funArity := fun
    | .f3 => 3
    | .g => 1
  constSymbols := Empty
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := false

/-- Example 8.4.1 (companion): build a Fin 3 -> alpha function from
three values. -/
@[blueprint "chap8__example_8_4_1"]
def unifVec3 (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- Example 8.4.1: t_1 = f(x, g(x), x) from subcase (iii), the first term
demonstrating occurs-check failure. Variable: x = 0. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t1_iii : Term unificationExampleLanguage3 :=
  Term.func UnifExFunc3.f3
    (unifVec3 (Term.var 0)
      (Term.func UnifExFunc3.g (unifVec1 (Term.var 0)))
      (Term.var 0))

/-- Example 8.4.1: t_2 = f(g(u), g(g(z)), z) from subcase (iii); unification
    requires z = g(z), impossible for finite trees. -/
@[blueprint "chap8__example_8_4_1" (main := true)]
def unifEx_t2_iii : Term unificationExampleLanguage3 :=
  Term.func UnifExFunc3.f3
    (unifVec3
      (Term.func UnifExFunc3.g (unifVec1 (Term.var 3)))
      (Term.func UnifExFunc3.g
        (unifVec1 (Term.func UnifExFunc3.g (unifVec1 (Term.var 2)))))
      (Term.var 2))

/-- Example 8.4.1(iii) (companion): the same alleged finite unifier
    satisfies all five equations x=g(u), x=z, g(x)=g(g(z)), x=g(z), z=g(z)
    after substitution. Here x=0, z=2 and u=3 in the ternary language. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_equations_iii
    (sigma : FiniteSubstitution unificationExampleLanguage3)
    (h : IsUnifier sigma [unifEx_t1_iii, unifEx_t2_iii]) :
    sigma 0 = termSubstAll (Term.func UnifExFunc3.g (unifVec1 (Term.var 3))) sigma ∧
    sigma 0 = sigma 2 ∧
    termSubstAll (Term.func UnifExFunc3.g (unifVec1 (Term.var 0))) sigma =
      termSubstAll (Term.func UnifExFunc3.g
        (unifVec1 (Term.func UnifExFunc3.g (unifVec1 (Term.var 2))))) sigma ∧
    sigma 0 = termSubstAll (Term.func UnifExFunc3.g (unifVec1 (Term.var 2))) sigma ∧
    sigma 2 = termSubstAll (Term.func UnifExFunc3.g (unifVec1 (Term.var 2))) sigma 

/-- Example 8.4.1(iii) (companion): the ternary pair has no finite unifier,
    since its last forced equation makes a finite term equal to its proper
    unary extension. -/
@[blueprint "chap8__example_8_4_1"]
theorem unifEx_not_unifiable_iii :
    ¬ ∃ sigma : FiniteSubstitution unificationExampleLanguage3,
      IsUnifier sigma [unifEx_t1_iii, unifEx_t2_iii] 

-- ===================================================================
-- Lemma 8.4.1: Reduction of multi-tree unification to pairwise
-- ===================================================================

/-- Lemma 8.4.1: A substitution sigma unifies {t_1, ..., t_m} iff sigma
    unifies the pair {#(t_1,...,t_m), #(t_1,...,t_1)} for a fresh #. -/
@[blueprint "chap8__lemma_8_4_1" (main := true)]
theorem unifier_iff_auxiliary_unifier {L : Language}
    (ts : List (Term L)) (sigma : Nat → Term L)
    (L' : Language)
    (embed : L.funSymbols → L'.funSymbols)
    (sharp : L'.funSymbols)
    (h_arity_embed : ∀ f, L'.funArity (embed f) = L.funArity f)
    (h_arity_sharp : L'.funArity sharp = ts.length)
    (liftTerm : Term L → Term L')
    (h_lift_var : ∀ x, liftTerm (Term.var x) = Term.var x)
    (h_lift_const : ∀ c, liftTerm (Term.const c) =
      liftTerm (Term.const c))
    (h_lift_func : ∀ (f : L.funSymbols) (args : Fin (L.funArity f) → Term L),
      liftTerm (Term.func f args) =
        Term.func (embed f)
          (fun i => liftTerm (args (i.cast (h_arity_embed f)))))
    (h_lift_subst : ∀ t, liftTerm (termSubstAll t sigma) =
      termSubstAll (liftTerm t) (fun x => liftTerm (sigma x)))
    (h_lift_injective : ∀ a b, liftTerm a = liftTerm b → a = b) :
    IsUnifierCore sigma ts ↔
      IsUnifierCore (fun x => liftTerm (sigma x))
        [Term.func sharp (fun i =>
          liftTerm (ts.get (i.cast h_arity_sharp))),
         Term.func sharp (fun _ =>
          match ts with
          | [] => Term.var 0
          | t :: _ => liftTerm t)] 

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

