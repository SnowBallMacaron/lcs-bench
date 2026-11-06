import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers
import LCS.FOResolution.Unification.RobinsonStep
import LCS.FOResolution.Unification.RobinsonSolve
import Attach
import LCS.FOResolution.Unification.Examples.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

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

inductive RobinsonRegressionConst : Type where
  | left
  | right

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

end LCS.FOResolution.Unification
end
