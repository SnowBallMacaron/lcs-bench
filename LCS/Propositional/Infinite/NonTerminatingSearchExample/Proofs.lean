import LCS.Propositional.Infinite.NonTerminatingSearchExample
open LCS.Propositional.Infinite.Search.Proofs

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Q is distinct from every Pᵢ in the chain. -/
theorem exInfChainVariables_disjoint (i : Nat) :
    (PropFormulaNormalized.var (i + 1)) ≠ .var 0 := by
  intro h
  have := PropFormulaNormalized.var.inj h
  omega

helper theorem exInfRightmostAddress_step (n : Nat) :
    exInfRightmostAddress (n + 1) = exInfRightmostAddress n ++ [n % 2] := by
  simp [exInfRightmostAddress, List.range_succ]

helper @[simp] theorem exInfRightmostLabel_even (n : Nat) :
    exInfRightmostLabel (2 * n) = exInfRightmostCheckpoint n := by
  have hd : 2 * n / 2 = n := by omega
  have hm : 2 * n % 2 = 0 := by omega
  simp [exInfRightmostLabel, hd, hm]

helper @[simp] theorem exInfRightmostLabel_odd (n : Nat) :
    exInfRightmostLabel (2 * n + 1) = exInfRightmostIntroduced n := by
  have hd : (2 * n + 1) / 2 = n := by omega
  have hm : (2 * n + 1) % 2 = 1 := by omega
  simp [exInfRightmostLabel, hd, hm]

helper theorem exInfRightmostAtoms_mem (n : Nat) (A : PropFormulaNormalized) :
    A ∈ exInfRightmostAtoms n ↔ ∃ i, i ≤ n ∧ A = .var (i + 1) := by
  induction n with
  | zero => simp [exInfRightmostAtoms]
  | succ n ih =>
    simp only [exInfRightmostAtoms, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, hA⟩)
      · exact ⟨n + 1, Nat.le_refl _, h⟩
      · exact ⟨i, by omega, hA⟩
    · rintro ⟨i, hi, hA⟩
      by_cases heq : i = n + 1
      · subst i; exact Or.inl hA
      · exact Or.inr ⟨i, by omega, hA⟩

helper theorem exInfRightmostAtoms_atomic (n : Nat) :
    (exInfRightmostAtoms n).all isAtomicBool = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [exInfRightmostAtoms, isAtomicBool] using ih

helper theorem exInfRightmostCheckpoint_open (n : Nat) : ¬ isAxiom (exInfRightmostCheckpoint n) := by
  rintro ⟨A, hA, hQ⟩
  simp only [exInfRightmostCheckpoint, List.mem_singleton] at hQ
  subst A
  obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem n _).mp hA
  exact exInfChainVariables_disjoint i hi.symm

helper theorem exInfRightmostIntroduced_open (n : Nat) : ¬ isAxiom (exInfRightmostIntroduced n) := by
  rintro ⟨A, hA, hQ⟩
  simp only [exInfRightmostIntroduced, List.mem_singleton] at hQ
  subst A
  simp only [exInfRightmostIntroduced, List.mem_append, List.mem_singleton] at hA
  rcases hA with hA | hA
  · obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem n _).mp hA
    exact exInfChainVariables_disjoint i hi.symm
  · cases hA

helper /-- A checkpoint's introduced implication keeps this leaf unfinished. -/
theorem exInfRightmostIntroduced_unfinished (st : InfSearchState) (n : Nat) :
    ¬ infIsFinishedLeaf st (exInfRightmostIntroduced n) := by
  rintro (ha | ⟨_, _, hatom⟩)
  · exact exInfRightmostIntroduced_open n ha
  · have hm : .impl (.var (n + 1)) (.var (n + 2)) ∈
        (exInfRightmostIntroduced n).antecedent ++ (exInfRightmostIntroduced n).succedent := by
      simp [exInfRightmostIntroduced]
    exact hatom _ hm

helper /-- Every Pᵢ and every chain implication occurs on the full actual-label sequence. -/
theorem exInfRightmost_antecedent_union (A : PropFormulaNormalized) :
    (∃ n, A ∈ (exInfRightmostLabel n).antecedent) ↔ exInfBranchPremises A := by
  constructor
  · rintro ⟨n, hA⟩
    unfold exInfRightmostLabel at hA
    split at hA
    · obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem (n / 2) A).mp hA
      exact Or.inl ⟨i, hi⟩
    · simp only [exInfRightmostIntroduced, List.mem_append, List.mem_singleton] at hA
      rcases hA with hA | hA
      · obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem (n / 2) A).mp hA
        exact Or.inl ⟨i, hi⟩
      · exact Or.inr ⟨n / 2, hA⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨2 * i, ?_⟩
      rw [exInfRightmostLabel_even]
      exact (exInfRightmostAtoms_mem i _).mpr ⟨i, Nat.le_refl _, rfl⟩
    · refine ⟨2 * i + 1, ?_⟩
      simp [exInfRightmostIntroduced]

helper theorem exInfRightmost_succedent_union (A : PropFormulaNormalized) :
    (∃ n, A ∈ (exInfRightmostLabel n).succedent) ↔ exInfBranchConclusions A := by
  have hlabel : ∀ n, (exInfRightmostLabel n).succedent = [.var 0] := by
    intro n
    unfold exInfRightmostLabel
    split <;> rfl
  simp [hlabel, exInfBranchConclusions]

helper /-- The actual replacement below the rightmost introduced leaf in the next round. -/
def exInfRightmostRound (n : Nat) : InfDeductionTree (exInfRightmostIntroduced n) :=
  appendToLeavesCore
    (InfDeductionTree.ofDeductionTree (expandLeaf .systematic (exInfRightmostIntroduced n)))
    (some (.impl (.var (n + 2)) (.var (n + 3)))) none

helper theorem exInfRightmostRound_checkpoint (n : Nat) :
    (exInfRightmostRound n).labelAt [1] = some (exInfRightmostCheckpoint (n + 1)) := by
  unfold exInfRightmostRound exInfRightmostIntroduced
  rw [Search.expandLeaf_finalImplication (exInfRightmostAtoms n) (n + 1) (n + 2) 0
    (exInfRightmostAtoms_atomic n) (exInfRightmostIntroduced_open n)]
  simp [Search.finalImplicationTree, appendToLeavesCore, InfDeductionTree.ofDeductionTree,
    InfDeductionTree.bindLeaves, InfDeductionTree.labelAt, exInfRightmostCheckpoint,
    exInfRightmostAtoms]

helper theorem exInfRightmostRound_leaf (n : Nat) :
    (exInfRightmostRound n).leafAt [1, 0] = some (exInfRightmostIntroduced (n + 1)) := by
  have hright : isAxiomBool (exInfRightmostCheckpoint (n + 1)) ≠ true :=
    fun h => exInfRightmostCheckpoint_open (n + 1) ((isAxiomBool_iff _).mp h)
  unfold exInfRightmostRound exInfRightmostIntroduced
  rw [Search.expandLeaf_finalImplication (exInfRightmostAtoms n) (n + 1) (n + 2) 0
    (exInfRightmostAtoms_atomic n) (exInfRightmostIntroduced_open n)]
  simp only [Search.finalImplicationTree, appendToLeavesCore,
    InfDeductionTree.ofDeductionTree_cast, InfDeductionTree.bindLeaves_cast,
    InfDeductionTree.leafAt_cast, InfDeductionTree.ofDeductionTree,
    InfDeductionTree.bindLeaves, InfDeductionTree.leafAt, List.append_nil, List.singleton_append]
  simp only [exInfRightmostCheckpoint, exInfRightmostAtoms] at hright
  simp [hright, InfDeductionTree.leafAt, extendSeq, exInfRightmostAtoms]

helper /-- Every checkpoint and introduced label occurs at the stated actual stage/address. -/
theorem exInfRightmost_stage_labels (n : Nat) :
    (infSearchSteps exInfSearchNonTerminating (n + 1)).tree.labelAt
      (exInfRightmostAddress (2 * n)) = some (exInfRightmostCheckpoint n) ∧
    (infSearchSteps exInfSearchNonTerminating (n + 1)).tree.leafAt
      (exInfRightmostAddress (2 * n + 1)) = some (exInfRightmostIntroduced n) := by
  induction n with
  | zero => constructor <;> decide
  | succ n ih =>
    let st := infSearchSteps exInfSearchNonTerminating (n + 1)
    let f : (s : Sequent) → InfDeductionTree s := fun s =>
      if infIsFinishedLeafBool st s then .leaf s
      else appendToLeavesCore (InfDeductionTree.ofDeductionTree (searchRound .systematic (.leaf s)))
        (InfSeq.head st.L) (InfSeq.head st.R)
    have hL : InfSeq.head st.L = some (.impl (.var (n + 2)) (.var (n + 3))) := by
      simpa [st, InfSeq.head, exInfSearchNonTerminating] using
        (infSearchSteps_remaining exInfSearchNonTerminating (n + 1) 0).1
    have hR : InfSeq.head st.R = none := by
      simpa [st, InfSeq.head, exInfSearchNonTerminating] using
        (infSearchSteps_remaining exInfSearchNonTerminating (n + 1) 0).2
    have hguard : infIsFinishedLeafBool st (exInfRightmostIntroduced n) ≠ true :=
      fun h => exInfRightmostIntroduced_unfinished st n ((infIsFinishedLeafBool_iff _ _).mp h)
    have hf : f (exInfRightmostIntroduced n) = exInfRightmostRound n := by
      simp [f, hguard, hL, hR, searchRound, mapLeaves, exInfRightmostRound]
    have hc := InfDeductionTree.labelAt_bindLeaves_below_leaf f st.tree
      (exInfRightmostAddress (2 * n + 1)) [1] ih.2
    have hl := InfDeductionTree.leafAt_bindLeaves_below_leaf f st.tree
      (exInfRightmostAddress (2 * n + 1)) [1, 0] ih.2
    rw [hf, exInfRightmostRound_checkpoint] at hc
    rw [hf, exInfRightmostRound_leaf] at hl
    have he : exInfRightmostAddress (2 * (n + 1)) =
        exInfRightmostAddress (2 * n + 1) ++ [1] := by
      have heq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      have hm : (2 * n + 1) % 2 = 1 := by omega
      rw [heq, exInfRightmostAddress_step, hm]
    have ho : exInfRightmostAddress (2 * (n + 1) + 1) =
        exInfRightmostAddress (2 * n + 1) ++ [1, 0] := by
      have hm : 2 * (n + 1) % 2 = 0 := by omega
      rw [exInfRightmostAddress_step, hm, he, List.append_assoc]
      rfl
    constructor
    · rw [he]; exact hc
    · rw [ho]; exact hl

helper /-- Every full rightmost-path label belongs to the actual search limit. -/
theorem exInfRightmost_labels_in_limit (n : Nat) :
    infSearchLimit exInfSearchNonTerminating (exInfRightmostAddress n) (exInfRightmostLabel n) := by
  by_cases he : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    obtain ⟨hc, _⟩ := exInfRightmost_stage_labels (n / 2)
    refine ⟨n / 2 + 1, ?_⟩
    simp only [exInfRightmostLabel, he, ↓reduceIte]
    rw [congrArg exInfRightmostAddress hn]
    exact hc
  · have hn : n = 2 * (n / 2) + 1 := by omega
    obtain ⟨_, hl⟩ := exInfRightmost_stage_labels (n / 2)
    have hc := InfDeductionTree.labelAt_of_leafAt _ _ hl
    refine ⟨n / 2 + 1, ?_⟩
    simp only [exInfRightmostLabel, he, ↓reduceIte]
    rw [congrArg exInfRightmostAddress hn]
    exact hc

proof_of exInfRightmost_is_infinite_path := by
  constructor
  · rfl
  · intro n
    refine ⟨?_, exInfRightmostLabel (n + 1), exInfRightmost_labels_in_limit (n + 1)⟩
    rw [exInfRightmostAddress_step]
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm
    · exact Or.inl (by rw [hm])
    · exact Or.inr (by rw [hm])

proof_of exInfRightmost_checkpoints := by
  simpa only [exInfRightmostLabel_even, exInfRightmostCheckpoint] using
    exInfRightmost_labels_in_limit (2 * n)

proof_of exInfHintikkaSet_actual_branch := by
  cases sf with
  | trueSign A => exact (exInfRightmost_antecedent_union A).symm
  | falseSign A => exact (exInfRightmost_succedent_union A).symm

proof_of exInfHintikkaSet_satisfied := by
  cases sf with
  | trueSign A =>
    rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [evalExtN, exInfFalsifyingValuation, hImplies]
  | falseSign A =>
    change A = .var 0 at h
    subst A
    rfl

proof_of exInfSearchNonTerminating_does_not_halt := by
  rintro ⟨k, hk⟩
  cases k with
  | zero =>
    have hf : infIsFinishedTreeBool (infSearchSteps exInfSearchNonTerminating 0) = false := by decide
    have ht := (infIsFinishedTreeBool_iff _).mpr hk
    rw [hf] at ht
    contradiction
  | succ n =>
    have hl := (exInfRightmost_stage_labels n).2
    have hm := InfDeductionTree.mem_leaves_of_leafAt _ _ hl
    exact exInfRightmostIntroduced_unfinished _ n (hk _ hm)

end LCS.Propositional.Infinite
end
