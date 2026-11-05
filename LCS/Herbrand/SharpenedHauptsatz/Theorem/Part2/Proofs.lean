import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part2

section

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

proof_of permutationExampleFinalMeasures := by
  -- BEGIN PROOF
    exact ⟨rfl, rfl⟩


helper /-- Example 7.3.3 (companion): The two recorded local exchanges compute the
exact printed next stages, and their source fragments use the same frontiers
once each in the original order. The first exchange adds two weakenings. -/
theorem permutationExampleExchangeResults :
    permutationFirstBefore.inputOrder = [0,1] ∧
    permutationSecondBefore.inputOrder = [0,1] ∧
    permutationFirstExchange.result = permutationExampleIntermediateTree ∧
    permutationSecondExchange.result = permutedExampleTree ∧
    numWeakeningRulesLK permutationExampleIntermediateTree =
      numWeakeningRulesLK permutationExampleTree + 2 := by
-- BEGIN PROOF
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

proof_of permutationExampleMeasureM := by
  -- BEGIN PROOF
    rfl


proof_of permutationExampleMeasureN := by
  -- BEGIN PROOF
    rfl


end LCS.Herbrand.SharpenedHauptsatz.Theorem

end

section

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

helper /-- Example 7.3.4 (companion): The renamed midsequent is connected to the
fresh representative at the same actual node address as in the raw diagram. -/
theorem midsequentRenamedNode :
    lkSubtreeAt midsequentRenamedTree (List.replicate 19 0) =
      some ⟨midsequentRenamedMidseq, midsequentRenamedUpperTree⟩ := by
-- BEGIN PROOF
  rfl

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


helper /-- Example 7.3.4 (companion): The common end sequent satisfies the
sequent-wide free/bound convention; all its displayed formulas are sentences. -/
theorem midsequentExampleEndClean : Hintikka.crossNoFreeBound midsequentExampleSequent := by
-- BEGIN PROOF
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  intro x ⟨A, hA, hx⟩
  simp only [midsequentExampleSequent, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl
  all_goals
    exfalso
    simp [formulaFVN, midseqExMkP, midseqExMkQ, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo] at hx
    omega

proof_of midsequentRenamedPure := by
  -- BEGIN PROOF
    -- REPAIR(T7-126): proof pending
    sorry


proof_of sharpenedHauptsatz_LK := by
  -- BEGIN PROOF
    -- REPAIR(T7-43): proof pending
    sorry


proof_of sharpenedHauptsatz_LKe := by
  -- BEGIN PROOF
    -- REPAIR(T7-43): proof pending
    sorry


end LCS.Herbrand.SharpenedHauptsatz.Theorem

end
