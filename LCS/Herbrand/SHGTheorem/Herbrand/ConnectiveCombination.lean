import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SequentEncodings

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Helper: G2nnf identity tree for quantifier-free NNF formulas
-- ===================================================================

/-- NNF evidence for singleton premise and conclusion formulae. -/
theorem allNNF_singletons {L : Language}
    [DecidableEq (FormulaN L)] {A B : FormulaN L}
    (hA : A.isNNF) (hB : B.isNNF) : AllNNF (({A} : LCS.Finset (FormulaN L)), {B}) := by
  constructor <;> intro F h
  · have he := (LCS.Finset.mem_singleton F A).mp h
    subst F; exact hA
  · have he := (LCS.Finset.mem_singleton F B).mp h
    subst F; exact hB

end LCS.Herbrand.SHGTheorem.Herbrand
end
