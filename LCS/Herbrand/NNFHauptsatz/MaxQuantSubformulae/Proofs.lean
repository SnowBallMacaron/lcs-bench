import LCS.Herbrand.NNFHauptsatz.MaxQuantSubformulae

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

proof_of qfExResult := by
  -- BEGIN PROOF
    unfold maxQuantSubformulae maxQuantSubformulaeCore qfExFormula
    rfl

proof_of qfExNonMaximal := by
  -- BEGIN PROOF
    unfold maxQuantSubformulae maxQuantSubformulaeCore qfExFormula LCS.Herbrand.NNFHauptsatz.sng
    intro h
    rcases h with (h | h) | h
    · exact nomatch h
    · rcases h with h | h
      · exact h
      · exact nomatch h
    · exact nomatch h
end LCS.Herbrand.NNFHauptsatz
end
