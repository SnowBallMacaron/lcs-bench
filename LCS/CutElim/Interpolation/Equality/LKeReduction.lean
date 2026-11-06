import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.Instantiation
import LCS.CutElim.Interpolation.Equality.RootSupport
import Attach
import LCS.CutElim.Interpolation.Equality.LKeReduction.ProofsStamp

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
-- Helper: if A is universally valid, then lkeProvable ([] -> [A])
-- ===================================================================

theorem lkeProvable_of_universally_valid {L : Language}
    (A : FormulaN L)
    (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
    lkeProvable { antecedent := [], succedent := [A] } := by
-- BEGIN PROOF
  apply lkeProvable_of_sequentValid
  intro M s _; exact ⟨A, List.Mem.head _, hvalid M s⟩

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): lke_to_lk_with_se
-- ===================================================================

/-- Lemma 6.5.3 (companion): Forward direction: if S is
LKe-provable, then (closedEqualityAxioms S ++ Gamma) -> Delta
is LK-provable (folkProvable). The textbook states the right side
as "LK-provable": the closed equality axioms S_e are universally
valid, so S_e, Gamma -> Delta is provable in LK (without equality
axioms) by instantiating the closed axioms. -/
theorem lke_to_folk_with_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : lkeProvable S) :
    folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent } := by
  -- REPAIR(T6-47): proof pending
  sorry

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): lke_with_se_to_lke
-- ===================================================================





-- ===================================================================
-- Lemma 6.5.3: lke_provable_iff_lke_with_se
-- ===================================================================

/-- Lemma 6.5.3: A sequent S = Gamma -> Delta is LKe-provable
iff S_e, Gamma -> Delta is LK-provable (folkProvable). The
forward direction adds the universally valid closed equality
axioms to the antecedent and produces an LK proof. The backward
direction wraps the LK proof in LKe and strips the S_e prefix
using lkeProvable_remove_valid_prefix. -/
@[blueprint "chap6__lemma_6_5_3" (main := true)]
theorem lke_provable_iff_lke_with_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) :
    lkeProvable S ↔
    folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent } 

end LCS.CutElim.Interpolation.Equality
end
