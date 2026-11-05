import LCS.Item
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import Attach
import LCS.FirstOrder.SyntaxN.Substitution.ProofsStamp

/-! # FirstOrder.SyntaxN.Substitution
    Substitution and free-for predicate for FormulaN (§5.3.8+).
    Self-contained on FormulaN. Uses termSubst from Basic.lean.
-/

namespace LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- FormulaN substitution
-- ===================================================================

/-- Definition 5.2.6: Substitute term t for free
occurrences of variable x in a normalized formula A. -/
@[blueprint "chap5__definition_5_2_6"]
def formulaSubstN {L : Language} :
    FormulaN L → Term L → Nat → FormulaN L
  | .predN P ts, t, x => .predN P (fun i => termSubst (ts i) t x)
  | .eq_ hL t1 t2, t, x => .eq_ hL (termSubst t1 t x) (termSubst t2 t x)
  | .neg A, t, x => .neg (formulaSubstN A t x)
  | .conj A B, t, x => .conj (formulaSubstN A t x) (formulaSubstN B t x)
  | .disj A B, t, x => .disj (formulaSubstN A t x) (formulaSubstN B t x)
  | .impl A B, t, x => .impl (formulaSubstN A t x) (formulaSubstN B t x)
  | .all y A, t, x =>
    if x != y then .all y (formulaSubstN A t x) else .all y A
  | .ex y A, t, x =>
    if x != y then .ex y (formulaSubstN A t x) else .ex y A

-- ===================================================================
-- Free-for predicate
-- ===================================================================

/-- Definition 5.2.7: Term t is free for variable
x in a normalized formula A if substituting t for x does not cause
variable capture. -/
@[blueprint "chap5__definition_5_2_7"]
def isFreeForN {L : Language} :
    Term L → Nat → FormulaN L → Prop
  | _, _, .predN _ _ => True
  | _, _, .eq_ _ _ _ => True
  | t, x, .neg A => isFreeForN t x A
  | t, x, .conj A B => isFreeForN t x A ∧ isFreeForN t x B
  | t, x, .disj A B => isFreeForN t x A ∧ isFreeForN t x B
  | t, x, .impl A B => isFreeForN t x A ∧ isFreeForN t x B
  | t, x, .all y A =>
    x = y ∨ (¬ Membership.mem (termFV t) y ∧ isFreeForN t x A)
  | t, x, .ex y A =>
    x = y ∨ (¬ Membership.mem (termFV t) y ∧ isFreeForN t x A)



-- retained: used by LCS.CutElim.Interpolation, LCS.CutElim.Interpolation.Equality, LCS.Herbrand.HerbrandTheorem, LCS.Herbrand.SharpenedHauptsatz
/-- Substituting var x for x in a FormulaN is the identity. -/
theorem formulaSubstN_var_self {L : Language} (A : FormulaN L) (x : Nat) :
    formulaSubstN A (Term.var x) x = A := by
-- BEGIN PROOF
  induction A with
  | predN _ ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i; exact termSubst_var_self (ts i) x
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, termSubst_var_self]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.conj.injEq]; exact ⟨ihA, ihB⟩
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.disj.injEq]; exact ⟨ihA, ihB⟩
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.impl.injEq]; exact ⟨ihA, ihB⟩
  | neg A ih =>
    simp only [formulaSubstN, FormulaN.neg.injEq]; exact ih
  | all y A ih =>
    simp only [formulaSubstN]; split
    · exact congrArg (FormulaN.all y) ih
    · rfl
  | ex y A ih =>
    simp only [formulaSubstN]; split
    · exact congrArg (FormulaN.ex y) ih
    · rfl

end LCS.FirstOrder.SyntaxN.Substitution
