import LCS.Propositional.Infinite.ClosedSearchExample
open LCS.Propositional.Infinite.Search.Proofs

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedInit_eq_displayed := by
  dsimp only [exInfSearchClosedInit, exInfSearchClosedInitDisplayed, infSearchInit,
    exInfSearchClosedAntecedent, InfSeq.head]
  congr 1
  funext n
  cases n <;> rfl

proof_of exInfSearchClosedRound1_eq_displayed := by
  rfl

proof_of exInfSearchClosedRound2_eq_displayed := by
  rfl

proof_of exInfSearchClosedRound3_eq_displayed := by
  rfl

proof_of exInfSearchClosedRound4_eq_displayed := by
  rfl

open LCS.Propositional.Systems.G.Search

proof_of exInfSearchClosedRound4_closed := by
  have hall : exInfSearchClosedRound4.tree.leaves.all isAxiomBool = true := by decide
  intro leaf hmem
  exact (isAxiomBool_iff leaf).mp ((List.all_eq_true.mp hall) leaf hmem)

end LCS.Propositional.Infinite
end
