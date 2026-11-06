import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.AdditionExample
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.HashLanguage
import Attach
import LCS.SLD.FirstOrder.HornEncoding.ProofsStamp

/-! # Encoding the Horn clause set for the SHG theorem

Section 9.4.2 (proof of Theorem 9.4.1): lowering hash-language syntax back to the base language with the fresh constant sent to a globally fresh variable; the encoded Horn clause set is a rectified NNF sentence, so the Skolem-Herbrand-Gödel theorem applies (in the hash language when the base language has no constant) and yields a compound instance. -/

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ===================================================================
-- Safe hash lowering algebra for the §9.4 ground transcript adapter
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding
/-- Lower hash-language terms to `L`: preserve base symbols and send the
    fresh constant to the caller-selected variable `k`. -/
def hashLowerTerm {L : Language} (k : Nat) :
    Term (HashLanguage L) → Term L
  | .var x => .var x
  | .const (.inl c) => .const c
  | .const (.inr _) => .var k
  | .func (Sum.inl f) args =>
      .func f (fun i => hashLowerTerm k (args i))
  | .func (Sum.inr _) _ => .var k

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Lower a hash-language substitution while keeping the hash variable
    rigid.  The override at `k` is load-bearing: a hash head is not
    affected by source substitution, so its lowered representative must
    likewise remain `.var k`. -/
def hashLowerSubst {L : Language} (k : Nat)
    (σ : Nat → Term (HashLanguage L)) : Nat → Term L :=
  fun x => if x = k then .var k else hashLowerTerm k (σ x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite raw-variable enumeration for one source Horn clause. -/
def hashSourceClauseVarsList {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) : List Nat :=
  (c.toFOClause.map (fun lit => formulaVarsList (FOLiteralCore.formula lit))).flatten

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The finite variable list of a source Horn problem.  It is computed
    solely from the concrete syntax of `D ++ goals`; no infinite set or
    ambient-language enumeration is involved. -/
def hashSourceProblemVarsList {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) : List Nat :=
  ((D ++ goals).map (hashSourceClauseVarsList (hNoEq := by all_goals exact hNoEq))).flatten.eraseDups

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A globally fresh even variable for the finite source Horn problem.
    It is twice one more than the maximum enumerated source variable. -/
def hashFreshEvenVar {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) : Nat :=
  2 * (((hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals).foldl Nat.max 0 + 1)

end LCS.SLD.FirstOrder
end
