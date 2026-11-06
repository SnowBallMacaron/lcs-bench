import LCS.Herbrand.SharpenedHauptsatz.Theorem.MidsequentExample

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SyntaxN.Variables

proof_of midsequentExampleSatisfiesConditions := by
  -- BEGIN PROOF
    constructor
    · simp [midsequentExampleMidseq, isQuantifierFree, midseqExMkP, midseqExMkQ]
    · refine ⟨List.replicate 19 0, midsequentExampleUpperTree, midsequentExampleNode, ?_, ?_⟩
      · simp [midsequentExampleUpperTree, AllRulesPropStructInessentialLK,
          FOLKStep1.isStructural, FOLKStep1.isLogical, FOLKStep1.isQuantifier,
          FOLKStep2.isStructural, FOLKStep2.isLogical, FOLKStep2.isQuantifier]
      · -- REPAIR(T7-126): proof pending
        sorry

proof_of midsequentExampleValidity := by
  -- BEGIN PROOF
    simp [sequentValid, universallyValidN, validInN, midsequentExampleSequent,
      midsequentExampleEquivFormula, formulaEvalN]

proof_of midsequentExampleCutFree := by
  -- BEGIN PROOF
    exact ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩

proof_of midsequentRenamedPure := by
  -- BEGIN PROOF
    -- REPAIR(T7-126): proof pending
    sorry

end LCS.Herbrand.SharpenedHauptsatz.Theorem
