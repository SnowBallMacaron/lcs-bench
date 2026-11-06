import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.SeparatingPairs
import LCS.FOResolution.Method.Resolvents
import Attach
import LCS.FOResolution.Method.ResolventExample.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- Example 8.5.1: Clause A = {neg P(z, a), neg P(z, x), neg P(x, z)}
    with z = var 0, x = var 4. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResClause_A : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P (Term.var 0) exSkolemConst_a),
    FOLiteralCore.neg (exPred_P (Term.var 0) (Term.var 4)),
    FOLiteralCore.neg (exPred_P (Term.var 4) (Term.var 0)) ]

/-- Example 8.5.1: Clause B = {P(z, f(z)), P(z, a)} with z = var 0. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResClause_B : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) (exSkolemFunc_f 0)),
    FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): A' = {neg P(z, a), neg P(z, x)}, the
    subset of A for the first resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_A'_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.neg (exPred_P (Term.var 0) exSkolemConst_a),
    FOLiteralCore.neg (exPred_P (Term.var 0) (Term.var 4)) ]

/-- Example 8.5.1 (companion): B' = {P(z, a)}, the subset of B for the
    first resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_B'_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): rho = (z_1/z), renaming z (var 0) to z_1
    (var 1). All other variables map to themselves. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho_first : Nat → Term exClauseFormLang
  | 0 => Term.var 1  -- z -> z_1
  | n => Term.var n

/-- Example 8.5.1 (companion): rho' = (z_2/z), renaming z (var 0) to
    z_2 (var 2). All other variables map to themselves. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho'_first : Nat → Term exClauseFormLang
  | 0 => Term.var 2  -- z -> z_2
  | n => Term.var n

/-- Example 8.5.1 (companion): sigma = (z_1/z_2, a/x), the MGU for the
    first resolvent. Maps z_2 (var 2) to z_1 (var 1), x (var 4) to a. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_sigma_first : Nat → Term exClauseFormLang
  | 2 => Term.var 1        -- z_2 -> z_1
  | 4 => exSkolemConst_a   -- x -> a
  | n => Term.var n

/-- Example 8.5.1: C = {neg P(a, z_1), P(z_1, f(z_1))}, the first
    resolvent of A and B. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exRes_C_first : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exSkolemConst_a (Term.var 1)),
    FOLiteralCore.pos (exPred_P (Term.var 1) (exSkolemFunc_f 1)) ]

/-- Example 8.5.1 (companion): A' = A = {neg P(z, a), neg P(z, x),
    neg P(x, z)}, the full clause A selected for the second resolvent
    computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_A'_second : List (FOLiteral exClauseFormLang rfl) :=
  exResClause_A

/-- Example 8.5.1 (companion): B' = {P(z, a)}, the subset of B for the
    second resolvent computation (same as the first computation). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_B'_second : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): rho for the second resolvent, same as
    first: (z_1/z), renaming z (var 0) to z_1 (var 1). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho_second : Nat → Term exClauseFormLang
  | 0 => Term.var 1
  | n => Term.var n

/-- Example 8.5.1 (companion): rho' for the second resolvent, same as
    first: (z_2/z), renaming z (var 0) to z_2 (var 2). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho'_second : Nat → Term exClauseFormLang
  | 0 => Term.var 2
  | n => Term.var n

/-- Example 8.5.1 (companion): sigma = (a/z_1, a/z_2, a/x), the MGU for
    the second resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_sigma_second : Nat → Term exClauseFormLang
  | 1 => exSkolemConst_a   -- z_1 -> a
  | 2 => exSkolemConst_a   -- z_2 -> a
  | 4 => exSkolemConst_a   -- x -> a
  | n => Term.var n

/-- Example 8.5.1: C = {P(a, f(a))}, the second resolvent of A and B
    obtained by taking A' = A. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exRes_C_second : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exSkolemConst_a
      (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]

/-- Example 8.5.1: The worked example demonstrating two distinct
    resolvents of A and B with different literal subsets and MGUs. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResolventExample : FOClause exClauseFormLang rfl × FOClause exClauseFormLang rfl :=
  (exRes_C_first, exRes_C_second)

-- ===================================================================
-- Example 8.5.1: Worked resolvent example
-- ===================================================================

/-- Example 8.5.1: The displayed positive literal set for the first pivot choice. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_normalized_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a),
    FOLiteralCore.pos (exPred_P (Term.var 1) (Term.var 4)),
    FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]

/-- Example 8.5.1: Renaming, C-side conjugation, and absolute value give the displayed first set. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_normalize_first :
    LitSetAbs (L := exClauseFormLang) rfl
      (substLits (L := exClauseFormLang) rfl exRes_rho_first exRes_A'_first ++
        substLits (L := exClauseFormLang) rfl exRes_rho'_first (LitSetConjugate (L := exClauseFormLang) rfl exRes_B'_first)) =
      exRes_normalized_first

/-- Example 8.5.1: The first unifier's common image P(z₁, a). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_common_first : FOLiteral exClauseFormLang rfl :=
  FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a)

/-- Example 8.5.1: The first substitution unifies the displayed literals, has input-bounded finite support, and every finite-support unifier factors through it on all variables by a finite-support substitution. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_first_mgu :
    (∀ lit, lit ∈ exRes_normalized_first →
      substLit (L := exClauseFormLang) rfl exRes_sigma_first lit = exRes_common_first) ∧
    (∀ x, exRes_sigma_first x ≠ Term.var x →
      clauseFV (L := exClauseFormLang) rfl exRes_normalized_first x) ∧
    (∃ support : List Nat, ∀ x, x ∉ support →
      exRes_sigma_first x = Term.var x) ∧
    (∀ tau : Nat → Term exClauseFormLang,
      (∃ support : List Nat, ∀ x, x ∉ support → tau x = Term.var x) →
      (∀ lit, lit ∈ exRes_normalized_first → ∀ lit', lit' ∈ exRes_normalized_first →
        substLit (L := exClauseFormLang) rfl tau lit = substLit (L := exClauseFormLang) rfl tau lit') →
      ∃ theta : Nat → Term exClauseFormLang,
        (∃ support : List Nat, ∀ x, x ∉ support → theta x = Term.var x) ∧
        ∀ x, tau x = termSubstAll (exRes_sigma_first x) theta)

/-- Example 8.5.1: The stored first output is a resolvent via precisely the displayed pivots, separating maps and MGU. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_first_isResolventVia :
    @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _) exRes_C_first exResClause_A exResClause_B
      exRes_A'_first exRes_B'_first
      exRes_rho_first exRes_rho'_first exRes_sigma_first

/-- Example 8.5.1: The displayed positive literal set for the second pivot choice. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_normalized_second : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 1) exSkolemConst_a),
    FOLiteralCore.pos (exPred_P (Term.var 1) (Term.var 4)),
    FOLiteralCore.pos (exPred_P (Term.var 4) (Term.var 1)),
    FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]

/-- Example 8.5.1: Renaming, C-side conjugation, and absolute value give the displayed second set. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_normalize_second :
    LitSetAbs (L := exClauseFormLang) rfl
      (substLits (L := exClauseFormLang) rfl exRes_rho_second exRes_A'_second ++
        substLits (L := exClauseFormLang) rfl exRes_rho'_second (LitSetConjugate (L := exClauseFormLang) rfl exRes_B'_second)) =
      exRes_normalized_second

/-- Example 8.5.1: The second unifier's common image P(a, a). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_common_second : FOLiteral exClauseFormLang rfl :=
  FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a)

/-- Example 8.5.1: The second substitution unifies the displayed literals, has input-bounded finite support, and every finite-support unifier factors through it on all variables by a finite-support substitution. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_sigma_second_mgu :
    (∀ lit, lit ∈ exRes_normalized_second →
      substLit (L := exClauseFormLang) rfl exRes_sigma_second lit = exRes_common_second) ∧
    (∀ x, exRes_sigma_second x ≠ Term.var x →
      clauseFV (L := exClauseFormLang) rfl exRes_normalized_second x) ∧
    (∃ support : List Nat, ∀ x, x ∉ support →
      exRes_sigma_second x = Term.var x) ∧
    (∀ tau : Nat → Term exClauseFormLang,
      (∃ support : List Nat, ∀ x, x ∉ support → tau x = Term.var x) →
      (∀ lit, lit ∈ exRes_normalized_second → ∀ lit', lit' ∈ exRes_normalized_second →
        substLit (L := exClauseFormLang) rfl tau lit = substLit (L := exClauseFormLang) rfl tau lit') →
      ∃ theta : Nat → Term exClauseFormLang,
        (∃ support : List Nat, ∀ x, x ∉ support → theta x = Term.var x) ∧
        ∀ x, tau x = termSubstAll (exRes_sigma_second x) theta)

/-- Example 8.5.1: The stored second output is a resolvent via precisely the displayed pivots, separating maps and MGU. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exRes_second_isResolventVia :
    @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _) exRes_C_second exResClause_A exResClause_B
      exRes_A'_second exRes_B'_second
      exRes_rho_second exRes_rho'_second exRes_sigma_second

/-- Example 8.5.1: The two stored outputs are extensionally distinct resolvents of the same parents. -/
@[attach_debt, blueprint "chap8__example_8_5_1"]
theorem exResolventExample_spec :
    @IsResolvent exClauseFormLang rfl (Classical.typeDecidableEq _) exResolventExample.1 exResClause_A exResClause_B ∧
    @IsResolvent exClauseFormLang rfl (Classical.typeDecidableEq _) exResolventExample.2 exResClause_A exResClause_B ∧
    ¬ (∀ lit, lit ∈ exResolventExample.1 ↔ lit ∈ exResolventExample.2)

end LCS.FOResolution.Method
end
