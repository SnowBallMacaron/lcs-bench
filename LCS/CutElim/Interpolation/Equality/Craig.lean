import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.KeyLemma
import Attach
import LCS.CutElim.Interpolation.Equality.Craig.ProofsStamp

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Theorem 6.5.2 (required structure): IsLKeImplicationInterpolant
-- ===================================================================

/-- Theorem 6.5.2 (required): A formula C is an interpolant of an
implication A implies B in the LKe setting if: (1) A implies C is
LKe-provable (i.e., [A] -> [C] is LKe-provable), (2) C implies B
is LKe-provable (i.e., [C] -> [B] is LKe-provable), and (3) all
predicate symbols except equality, constant symbols, and free
variables in C occur in both A and B. -/
@[blueprint "chap6__theorem_6_5_2"]
structure IsLKeImplicationInterpolant {L : Language}
    (A B C : FormulaN L) : Prop where
  /-- A implies C is LKe-provable -/
  left_provable :
    lkeProvable { antecedent := [A], succedent := [C] }
  /-- C implies B is LKe-provable -/
  right_provable :
    lkeProvable { antecedent := [C], succedent := [B] }
  /-- All non-equality predicate symbols in C occur in both
      A and B -/
  pred_common_except_eq :
    formulaNonEqPredSymbols C ⊆
      formulaNonEqPredSymbols A ∩ formulaNonEqPredSymbols B
  /-- All constant symbols in C occur in both A and B -/
  const_common :
    formulaConstSymbolsN C ⊆
      formulaConstSymbolsN A ∩ formulaConstSymbolsN B
  /-- All free variables in C occur in both A and B -/
  fv_common :
    formulaFVN C ⊆ formulaFVN A ∩ formulaFVN B

-- ===================================================================
-- Theorem 6.5.2 (companion def): craig_interpolation_equality_partition
-- ===================================================================



-- ===================================================================
-- Theorem 6.5.2: public textbook statement and witness
-- ===================================================================

/-- Theorem 6.5.2 (Craig's interpolation theorem, with equality):
if `A ⊃ B` is LKe-provable, there is an interpolant `C` whose
non-equality predicate symbols, constants, and free variables occur
in both `A` and `B`. -/
@[attach_debt, blueprint "chap6__theorem_6_5_2" (main := true)]
theorem craig_interpolation_equality {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (A B : FormulaN L)
    (hProv : lkeProvable
      { antecedent := [A], succedent := [B] }) :
    ∃ C : FormulaN L, IsLKeImplicationInterpolant A B C 

-- ===================================================================
-- Theorem 6.3.1 (companion): lkeProvableN_of_sequentValidN
-- ===================================================================

end LCS.CutElim.Interpolation.Equality
end
