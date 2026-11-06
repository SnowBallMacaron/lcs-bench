import LCS.Herbrand.HerbrandTheorem.Main.Theorem

namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

proof_of herbrandTheorem_LK := ⟨herbrandTheorem_forward_LK hL Gamma hAllPrenex hAllSentences hAllRectified hDistinct,
   herbrandTheorem_converse_LK hL Gamma hAllPrenex hAllSentences hAllRectified hDistinct⟩

proof_of herbrandTheorem_LKe := by
  -- REPAIR(T7-59): proof pending
  sorry

end LCS.Herbrand.HerbrandTheorem.Main
