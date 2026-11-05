import LCS.CutElim.Interpolation.KeyLemma
import LCS.CutElim.Interpolation.KeyLemma.Cases

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

proof_of interpolation_key_lemma := by
  -- Rename bound variables apart, apply lkBot_cut_elimination under the
  -- end-sequent convention, use the cut-free construction, and transfer
  -- the two interpolant sequents back by cuts.
  -- REPAIR(T6-44): proof pending
  sorry


end LCS.CutElim.Interpolation

end
