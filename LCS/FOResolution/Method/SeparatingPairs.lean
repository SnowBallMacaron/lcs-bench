import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import Attach
import LCS.FOResolution.Method.SeparatingPairs.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

-- ===================================================================
-- Definition 8.5.1: Separating pair of substitutions
-- ===================================================================

/-- Definition 8.5.1 (companion): The set of free variables occurring in
    a clause: the union of the variable sets of all literals in the
    clause. -/
@[blueprint "chap8__definition_8_5_1"]
def clauseFV {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq) : Set Nat :=
  fun m => ∃ lit, lit ∈ c ∧ FOLiteral.vars hNoEq lit m

/-- Definition 8.5.1 (companion): Predicate that a substitution maps
    every variable in a given set to a variable (not a compound term). -/
@[blueprint "chap8__definition_8_5_1"]
def substIsVarOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Prop :=
  ∀ x, S x → ∃ y, sigma x = Term.var y

/-- Definition 8.5.1 (companion): Predicate that a substitution is
    injective on a given set of variables. -/
@[blueprint "chap8__definition_8_5_1"]
def substInjectiveOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Prop :=
  ∀ x y, S x → S y → sigma x = sigma y → x = y

/-- Definition 8.5.1 (companion): The range of a substitution restricted
    to a given set: the set of variable indices that appear as images. -/
@[blueprint "chap8__definition_8_5_1"]
def substRangeOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Set Nat :=
  fun n => ∃ x, S x ∧ sigma x = Term.var n

/-- Definition 8.5.1: Predicate that all literals in the list are
    positive (unnegated atomic formulae). -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetPositive {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  ∀ lit, lit ∈ lits → ∃ B, lit = FOLiteralCore.pos B

/-- Definition 8.5.1: Predicate that all literals in the list are
    negative (negations of atomic formulae). -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetNegative {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  ∀ lit, lit ∈ lits → ∃ B, lit = FOLiteralCore.neg B

/-- Definition 8.5.1: An equality-free literal set has the same sign
    when all its literals are positive or all are negative. The empty
    set satisfies both alternatives; admission of a resolution step
    separately requires nonempty pivot sets. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetSameSign {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  LitSetPositive (hNoEq := by first | exact hNoEq | done) lits ∨ LitSetNegative (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: The conjugate of a list of literals: map
    FOLiteral.conjugate over each element. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetConjugate {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : List (FOLiteral L hNoEq) :=
  lits.map (FOLiteral.conjugate hNoEq)

/-- Internal total extension of literal-set absolute value retained for
    compatibility; the canonical Definition 8.5.1 boundary is
    `LitSetAbsSameSign`. -/
@[blueprint "chap8__example_8_5_1"]
def LitSetAbs {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : List (FOLiteral L hNoEq) :=
  match lits with
  | [] => []
  | (FOLiteralCore.pos _) :: _ => lits
  | (FOLiteralCore.neg _) :: _ => LitSetConjugate (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: The absolute value |S| of a same-sign literal set,
    implemented by the internal total extension `LitSetAbs`. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetAbsSameSign {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) (_hSame : LitSetSameSign (hNoEq := by first | exact hNoEq | done) lits) :
    List (FOLiteral L hNoEq) :=
  LitSetAbs (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: A separating pair (rho, rho') for equality-free
    clauses A and A' maps each clause's variables injectively to variables,
    giving a bijection onto its local image. These two local images are
    disjoint. Each substitution fixes every variable outside its clause's
    free-variable set, so its moved support is contained in that set.
    Variables inside the set may also be fixed, as in Example 8.5.1;
    identity witnesses are allowed when the two clause-variable sets
    are already disjoint. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def IsSeparatingPair {L : Language} (hNoEq : L.withoutEquality)
    (rho rho' : Nat → Term L)
    (A A' : FOClause L hNoEq) : Prop :=
  substIsVarOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A) ∧
  substIsVarOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A') ∧
  substInjectiveOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A) ∧
  substInjectiveOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A') ∧
  Set.inter (substRangeOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A))
            (substRangeOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A')) = Set.empty ∧
  (∀ x, ¬ clauseFV (hNoEq := by first | exact hNoEq | done) A x → rho x = Term.var x) ∧
  (∀ x, ¬ clauseFV (hNoEq := by first | exact hNoEq | done) A' x → rho' x = Term.var x)

end LCS.FOResolution.Method
end
