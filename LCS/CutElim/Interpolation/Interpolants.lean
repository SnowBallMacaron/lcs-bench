import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Symbols
import Attach
import LCS.CutElim.Interpolation.Interpolants.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
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
open LCS.FirstOrder.Gentzen.Hintikka

/-- The designated falsum constant ⊥ for LK⊥ and LKₑ,⊥, encoded as a
nullary predicate symbol applied to the empty term vector. -/
@[blueprint "chap6__lemma_6_5_4"]
def botFormula {L : Language} (botP : L.predSymbols) (hArity : L.predArity botP = 0) : FormulaN L :=
  FormulaN.predN botP (hArity ▸ Fin.elim0)

-- ===================================================================
-- Theorem 6.5.1 (required structure): IsImplicationInterpolant
-- ===================================================================

/-- Theorem 6.5.1 (required): A formula C is an interpolant of an
implication A implies B if: (1) A implies C is LK-provable
(i.e., [A] -> [C] is provable), (2) C implies B is LK-provable
(i.e., [C] -> [B] is provable), and (3) all predicate symbols,
constant symbols, and free variables in C occur in both A and B. -/
@[blueprint "chap6__theorem_6_5_1"]
structure IsImplicationInterpolant {L : Language}
    (A B C : FormulaN L) : Prop where
  /-- A implies C is LK-provable -/
  left_provable :
    folkProvable { antecedent := [A], succedent := [C] }
  /-- C implies B is LK-provable -/
  right_provable :
    folkProvable { antecedent := [C], succedent := [B] }
  /-- All predicate symbols in C occur in both A and B -/
  pred_common :
    formulaPredSymbolsN C ⊆
      formulaPredSymbolsN A ∩ formulaPredSymbolsN B
  /-- All constant symbols in C occur in both A and B -/
  const_common :
    formulaConstSymbolsN C ⊆
      formulaConstSymbolsN A ∩ formulaConstSymbolsN B
  /-- All free variables in C occur in both A and B -/
  fv_common :
    formulaFVN C ⊆ formulaFVN A ∩ formulaFVN B

end LCS.CutElim.Interpolation
end
