import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import LCS.SLD.Propositional.SLDDerivations
import LCS.SLD.Propositional.LinearizationExample
import Attach
import LCS.SLD.Propositional.RefutationExamples.ProofsStamp

/-! # Examples 9.3.2 and 9.3.3

Sections 9.3.1-9.3.2: the SLD-refutation obtained from the linearization of Example 9.3.1, and a Horn clause set with two goals each of which starts an SLD-refutation. -/

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

-- ========= Example 9.3.2: SLD-refutation example =========

/-- Example 9.3.2: The sequence from Example 9.3.1 is an SLD-refutation: an SLDDerivation
    with definiteClauses from Example 9.2.1, goals = [{neg 1, neg 2}], sequence = exLinearizationResult. -/
@[blueprint "chap9__example_9_3_2" (main := true)]
def exSLDRefutation : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals := [Clause.ofList [Literal.neg 1, Literal.neg 2]]
  sequence := exLinearizationResult
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [exLinearizationResult, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by simp [exLinearizationResult]
  initialIsGoal := by simp [exLinearizationResult]
  steps := fun i =>
    ([⟨1, Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩,
      ⟨4, Clause.ofList [Literal.pos 4]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [exLinearizationResult] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    unfold exLinearizationResult at hi ⊢
    have hi5 : i < 5 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

-- ========= Example 9.3.3: Multiple goal SLD-refutations =========

/-- Example 9.3.3: A set S of Horn clauses with two goals S = {{P}, {Q}, {neg S, R},
    {neg R, neg P}, {neg R, neg Q}, {S}} where P=0, Q=1, R=2, S=3. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalClauseSet : List Clause :=
  [Clause.ofList [Literal.pos 0],
   Clause.ofList [Literal.pos 1],
   Clause.ofList [Literal.neg 3, Literal.pos 2],
   Clause.ofList [Literal.neg 2, Literal.neg 0],
   Clause.ofList [Literal.neg 2, Literal.neg 1],
   Clause.ofList [Literal.pos 3]]

/-- Example 9.3.3: The SLD-refutation <{neg R, neg P}, {neg R}, {neg S}, square> resolving
    neg P against {P}, then neg R against {neg S, R}, then neg S against {S} to yield []. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalRefutation1 : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2, Literal.neg 1]]
  sequence :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2],
     Clause.ofList [Literal.neg 3],
     Clause.empty]
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by decide
  initialIsGoal := by simp
  steps := fun i =>
    ([⟨0, Clause.ofList [Literal.pos 0]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    have hi3 : i < 3 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

/-- Example 9.3.3: The SLD-refutation <{neg R, neg Q}, {neg R}, {neg S}, square> resolving
    neg Q against {Q}, then neg R against {neg S, R}, then neg S against {S} to yield []. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalRefutation2 : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2, Literal.neg 1]]
  sequence :=
    [Clause.ofList [Literal.neg 2, Literal.neg 1],
     Clause.ofList [Literal.neg 2],
     Clause.ofList [Literal.neg 3],
     Clause.empty]
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by decide
  initialIsGoal := by simp
  steps := fun i =>
    ([⟨1, Clause.ofList [Literal.pos 1]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    have hi3 : i < 3 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

-- ========= Example 9.3.3 (companion): clause set decomposition =========

/-- Example 9.3.3 (companion): Every definite clause used in the
    first SLD-refutation belongs to the clause set S. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation1_clauses_subset :
    ∀ C ∈ exMultiGoalRefutation1.definiteClauses, C ∈ exMultiGoalClauseSet 

-- ========= Example 9.3.2 (companion theorem): exSLDRefutation_isRefutation =========

/-- Example 9.3.2 (companion): Proof that the example SLD-derivation is
    indeed an SLD-refutation (last clause is empty). -/
@[blueprint "chap9__example_9_3_2"]
theorem exSLDRefutation_isRefutation : isSLDRefutation exSLDRefutation 

-- ========= Example 9.3.3 (companion theorems): refutation proofs =========

/-- Example 9.3.3 (companion): Proof that the first derivation is an
    SLD-refutation. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation1_isRefutation :
    isSLDRefutation exMultiGoalRefutation1 

/-- Example 9.3.3 (companion): Proof that the second derivation is an
    SLD-refutation. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation2_isRefutation :
    isSLDRefutation exMultiGoalRefutation2 

end LCS.SLD.Propositional
end
