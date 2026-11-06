import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Graph
import LCS.Herbrand.PrimRecursive
import LCS.FirstOrder.Equality.Search.Procedure
import LCS.CutElim.LKe.Equivalence
import LCS.FOResolution.GroundResolution.GroundClauses
import LCS.FOResolution.GroundResolution.ResolutionTrees
import Attach
import LCS.FOResolution.GroundResolution.Example.ProofsStamp

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN

-- ===================================================================
-- Example 8.3.1: Ground clauses G1-G4
-- ===================================================================

/-- Example 8.3.1 (companion): The ground term f(a), obtained by applying the
    Skolem function f to the Skolem constant a. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundTerm_fa : Term exClauseFormLang :=
  Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)

/-- Example 8.3.1: G1 = {not P(a,a)}, the ground clause obtained
    from C1 by substituting a for x and z1. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G1 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G2 = {P(a,f(a)), P(a,a)}, the ground clause
    obtained from C2 by substituting a for z2. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G2 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exSkolemConst_a exGroundTerm_fa),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G3 = {P(f(a),a), P(a,a)}, the ground clause
    obtained from C3 by substituting a for z3. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G3 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G4 = {not P(f(a),a), not P(a,f(a))}, the ground
    clause obtained from C1 by substituting f(a) for z1 and a for x. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G4 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.neg (exPred_P exSkolemConst_a exGroundTerm_fa) ]

-- ===================================================================
-- Example 8.3.1: Resolution steps
-- ===================================================================

/-- Example 8.3.1: Resolution step 1 -- G2 resolves with G1 on
    P(a,a), yielding the unit clause {P(a,f(a))}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step1 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exGroundClause_G2)
    (.axiom_ exGroundClause_G1)
    (FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a))

/-- Example 8.3.1: Resolution step 2 -- G1 resolves with G3 on
    P(a,a), yielding the unit clause {P(f(a),a)}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step2 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exGroundClause_G3)
    (.axiom_ exGroundClause_G1)
    (FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a))

/-- Example 8.3.1: Resolution step 3 -- {P(f(a),a)} resolves with
    G4 on P(f(a),a), yielding {not P(a,f(a))}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step3 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exGroundResolution_step2
    (.axiom_ exGroundClause_G4)
    (FOLiteralCore.pos
      (exPred_P (exGroundTerm_fa) exSkolemConst_a))

/-- Example 8.3.1: Resolution step 4 -- {P(a,f(a))} resolves with
    {not P(a,f(a))} on P(a,f(a)), yielding the empty clause. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step4 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exGroundResolution_step1
    exGroundResolution_step3
    (FOLiteralCore.pos
      (exPred_P exSkolemConst_a (exGroundTerm_fa)))

-- ===================================================================
-- Example 8.3.1: Complete refutation
-- ===================================================================

/-- Example 8.3.1: The complete resolution tree deriving the empty
    clause from G1-G4 through four resolution steps. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_refutation :
    FOResolutionTree exClauseFormLang rfl :=
  exGroundResolution_step4

open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical

-- ===================================================================
-- Example 8.3.1: Refutation root is empty clause
-- ===================================================================

-- Helper lemmas for concrete term discrimination

-- Step labels for the intermediate resolution steps

/-- Example 8.3.1 (companion): The root label of exGroundResolution_refutation is
    the empty clause, confirming the refutation is valid. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundResolution_refutation_label_empty :
    FOResolutionTree.labelSpec (hNoEq := by rfl) exGroundResolution_refutation []

open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FOResolution.Unification

/-- Example 8.3.1: (a/z1, a/x), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G1 (n : Nat) : Term exClauseFormLang :=
  if n = 1 ∨ n = 4 then exSkolemConst_a else .var n

/-- Example 8.3.1: (a/z2), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G2 (n : Nat) : Term exClauseFormLang :=
  if n = 2 then exSkolemConst_a else .var n

/-- Example 8.3.1: (a/z3), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G3 (n : Nat) : Term exClauseFormLang :=
  if n = 3 then exSkolemConst_a else .var n

/-- Example 8.3.1: (f(a)/z1, a/x), fixing every other variable. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundSubst_G4 (n : Nat) : Term exClauseFormLang :=
  if n = 1 then exGroundTerm_fa
  else if n = 4 then exSkolemConst_a else .var n

/-- Apply a simultaneous substitution to an example literal, preserving
    its sign and extending the variable map homomorphically to terms. -/
@[blueprint "chap8__example_8_3_1"]
def exLiteralSubst (sigma : Nat → Term exClauseFormLang) :
    FOLiteral exClauseFormLang rfl → FOLiteral exClauseFormLang rfl
  | .pos A => .pos (A.mapTerms (fun t => termSubstAll t sigma))
  | .neg A => .neg (A.mapTerms (fun t => termSubstAll t sigma))

/-- G1 is the literal-set image of C1 under (a/z1,a/x).
    Its three negative literals collapse to the single literal not P(a,a). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G1_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C1.map (exLiteralSubst exGroundSubst_G1) ↔
      lit ∈ exGroundClause_G1

/-- G2 is the literal-set image of C2 under (a/z2). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G2_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C2.map (exLiteralSubst exGroundSubst_G2) ↔
      lit ∈ exGroundClause_G2

/-- G3 is the literal-set image of C3 under (a/z3). -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G3_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C3.map (exLiteralSubst exGroundSubst_G3) ↔
      lit ∈ exGroundClause_G3

/-- G4 is the literal-set image of C1 under (f(a)/z1,a/x).
    The first two substituted literals coincide. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundClause_G4_image (lit : FOLiteral exClauseFormLang rfl) :
    lit ∈ exClause_C1.map (exLiteralSubst exGroundSubst_G4) ↔
      lit ∈ exGroundClause_G4

end LCS.FOResolution.GroundResolution
end
