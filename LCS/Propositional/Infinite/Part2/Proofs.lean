import LCS.Propositional.Infinite.Part2

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedRound1_eq_displayed := by
  rfl

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedRound2_eq_displayed := by
  rfl

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedRound3_eq_displayed := by
  rfl

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedRound4_eq_displayed := by
  rfl

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exInfSearchClosedRound4_computation_eq_displayed := by
  rw [exInfSearchClosedRound4, exInfSearchClosedInit_eq_displayed,
    exInfSearchClosedRound1_eq_displayed, exInfSearchClosedRound2_eq_displayed,
    exInfSearchClosedRound3_eq_displayed, exInfSearchClosedRound4_eq_displayed]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
namespace InfDeductionTree

helper def conclusion {s : Sequent} (_ : InfDeductionTree s) : Sequent := s

end InfDeductionTree
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
namespace InfDeductionTree

helper @[simp] theorem leaves_ofDeductionTree {s : Sequent} (t : DeductionTree s) :
    (ofDeductionTree t).leaves = t.leaves := by
  induction t with
  | leaf => rfl
  | onePremise _ _ ih => exact ih
  | twoPremise _ _ _ ih₁ ih₂ => simp [ofDeductionTree, leaves, DeductionTree.leaves, ih₁, ih₂]

end InfDeductionTree
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Emptiness is decidable for the finite/infinite sequences used in the source. -/
theorem noHoles_empty_iff (s : Nat → Option PropFormulaNormalized) (h : NoHoles s) :
    (∀ n, s n = none) ↔ s 0 = none := by
  constructor
  · intro hempty; exact hempty 0
  · intro hzero n
    induction n with
    | zero => exact hzero
    | succ n ih => exact h n ih

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem isAxiomBool_iff (s : Sequent) : isAxiomBool s = true ↔ isAxiom s := by
  simp only [isAxiomBool, List.any_eq_true, beq_iff_eq, isAxiom]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩; exact ⟨A, hA, hB⟩
  · rintro ⟨A, hA, hB⟩; exact ⟨A, hA, A, hB, rfl⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infIsFinishedLeafBool_iff (state : InfSearchState) (s : Sequent) :
    infIsFinishedLeafBool state s = true ↔ infIsFinishedLeaf state s := by
  simp only [infIsFinishedLeafBool, infIsFinishedLeaf, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true, isAxiomBool_iff,
    isAtomicBool_iff]
  rw [noHoles_empty_iff state.L state.L_noHoles,
    noHoles_empty_iff state.R state.R_noHoles]
  simp only [and_assoc]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infIsFinishedTreeBool_iff (state : InfSearchState) :
    infIsFinishedTreeBool state = true ↔ infIsFinishedTree state := by
  simp [infIsFinishedTreeBool, infIsFinishedTree, List.all_eq_true,
    infIsFinishedLeafBool_iff]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every finite stage retains the initial root. -/
theorem infSearchSteps_root (seq : InfSequent) (k : Nat) :
    (infSearchSteps seq k).rootSeq = (infSearchInit seq).rootSeq := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- No round changes or removes an old label. -/
theorem infExpand_labelAt_preserves (st : InfSearchState) (p : List Nat)
    (label : Sequent) (h : st.tree.labelAt p = some label) :
    (infExpand st).tree.labelAt p = some label :=
  InfDeductionTree.labelAt_bindLeaves_preserves _ _ p label h

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Closed leaves remain closed leaves at all later rounds. -/
theorem infExpand_closed_leaf (st : InfSearchState) (leaf : Sequent)
    (hmem : leaf ∈ st.tree.leaves) (hclosed : isAxiom leaf) :
    leaf ∈ (infExpand st).tree.leaves := by
  apply InfDeductionTree.mem_leaves_bindLeaves_of_fixed _ _ leaf hmem
  have hfin : infIsFinishedLeafBool st leaf = true :=
    (infIsFinishedLeafBool_iff st leaf).mpr (Or.inl hclosed)
  simp [hfin]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The total stage presentation stops changing the tree once it is finished. -/
theorem infExpand_tree_of_finished (st : InfSearchState) (h : infIsFinishedTree st) :
    (infExpand st).tree = st.tree := by
  apply InfDeductionTree.bindLeaves_eq_self
  intro leaf hmem
  simp [(infIsFinishedLeafBool_iff st leaf).mpr (h leaf hmem)]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The remaining sequences are exactly the original tails after k+1 heads.
Thus every input index is scheduled, with no left/right priority starvation. -/
theorem infSearchSteps_remaining (seq : InfSequent) (k n : Nat) :
    (infSearchSteps seq k).L n = seq.antecedent (n + k + 1) ∧
    (infSearchSteps seq k).R n = seq.succedent (n + k + 1) := by
  induction k generalizing n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simpa only [infSearchSteps, infExpand, InfSeq.tail, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Finite stages form an increasing family of labeled address trees. -/
theorem infSearchSteps_labelAt_mono (seq : InfSequent) (k n : Nat)
    (p : List Nat) (label : Sequent)
    (h : (infSearchSteps seq k).tree.labelAt p = some label) :
    (infSearchSteps seq (k + n)).tree.labelAt p = some label := by
  induction n with
  | zero => exact h
  | succ n ih => exact infExpand_labelAt_preserves _ p label ih

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The limit assigns a unique label to every address in its domain. -/
theorem infSearchLimit_unique (seq : InfSequent) (p : List Nat) (s t : Sequent)
    (hs : infSearchLimit seq p s) (ht : infSearchLimit seq p t) : s = t := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  have hi' := infSearchSteps_labelAt_mono seq i j p s hi
  have hj' := infSearchSteps_labelAt_mono seq j i p t hj
  rw [Nat.add_comm j i] at hj'
  rw [hi'] at hj'
  exact Option.some.inj hj'

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Immediate edges in the limit are actual logical or introduction steps. -/
theorem infSearchLimit_branchStep (seq : InfSequent) (p : List Nat) (i : Nat)
    {s c : Sequent} (hs : infSearchLimit seq p s)
    (hc : infSearchLimit seq (p ++ [i]) c) : Nonempty (InfBranchStep s c) := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨n, hn⟩ := hc
  have hk' := infSearchSteps_labelAt_mono seq k n p s hk
  have hn' := infSearchSteps_labelAt_mono seq n k (p ++ [i]) c hn
  rw [Nat.add_comm n k] at hn'
  exact InfDeductionTree.branchStep_of_labels _ p i hk' hn'

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Later stages extend the complete edge structure of each earlier stage. -/
theorem infSearchSteps_extension (seq : InfSequent) (k n : Nat) :
    InfDeductionTree.Extension (infSearchSteps seq k).tree
      (infSearchSteps seq (k + n)).tree := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (InfDeductionTree.extension_bindLeaves _ _)

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Infinite paths advance by exactly one binary-tree address component. -/
theorem infSearchPath_step (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) (n : Nat) :
    ∃ i, i < 2 ∧ address (n + 1) = address n ++ [i] := by
  rcases (hp.2 n).1 with h | h
  · exact ⟨0, by decide, h⟩
  · exact ⟨1, by decide, h⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infSearchPath_length (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) (n : Nat) :
    (address n).length = n := by
  induction n with
  | zero => rw [hp.1]; rfl
  | succ n ih =>
    obtain ⟨i, _, hi⟩ := infSearchPath_step seq address hp n
    simp [hi, ih]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infSearchPath_take (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) (n m : Nat) (hnm : n ≤ m) :
    (address m).take n = address n := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp [hp.1, infSearchTreeDomain]
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      exact List.take_of_length_le (by simp [infSearchPath_length seq address hp])
    · have hnm' : n ≤ m := by omega
      obtain ⟨i, _, hi⟩ := infSearchPath_step seq address hp m
      rw [hi, List.take_append]
      simp [infSearchPath_length seq address hp m, Nat.sub_eq_zero_of_le hnm', ih hnm']

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- A stage's leaf crossing cannot precede one of its existing path nodes. -/
theorem infSearchPath_node_before_leaf (seq : InfSequent)
    (address : Nat → List Nat) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (k i n : Nat) (label leaf : Sequent)
    (hi : (infSearchSteps seq k).tree.labelAt (address i) = some label)
    (hn : (infSearchSteps seq k).tree.leafAt (address n) = some leaf) : i ≤ n := by
  by_cases hle : i ≤ n
  · exact hle
  have hni : n ≤ i := by omega
  have hsplit : address i = address n ++ (address i).drop n := by
    calc
      address i = (address i).take n ++ (address i).drop n := (List.take_append_drop _ _).symm
      _ = address n ++ (address i).drop n := by rw [infSearchPath_take seq address hp n i hni]
  have hempty := InfDeductionTree.leafAt_descendant_eq
    (infSearchSteps seq k).tree (address n) ((address i).drop n) hn (hsplit ▸ hi)
  rw [hempty, List.append_nil] at hsplit
  have hlength := congrArg List.length hsplit
  rw [infSearchPath_length seq address hp i, infSearchPath_length seq address hp n] at hlength
  omega

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every infinite limit path crosses a leaf of every finite stage. -/
theorem infSearchPath_crosses_stage_leaf (seq : InfSequent)
    (address : Nat → List Nat) (labels : Nat → Sequent)
    (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (labels n)) (k : Nat) :
    ∃ n, (infSearchSteps seq k).tree.leafAt (address n) = some (labels n) := by
  let depth := (infSearchSteps seq k).tree.height + 1
  obtain ⟨m, hm⟩ := hl depth
  have hm' := infSearchSteps_labelAt_mono seq m k (address depth) (labels depth) hm
  rw [Nat.add_comm m k] at hm'
  rcases (infSearchSteps_extension seq k m).node_or_leaf_prefix
    (address depth) (labels depth) hm' with hold | ⟨q, suffix, leaf, hq, hleaf⟩
  · have hbound := InfDeductionTree.labelAt_length_le_height _ _ hold
    rw [infSearchPath_length seq address hp depth] at hbound
    omega
  · have hlen : q.length ≤ depth := by
      have := congrArg List.length hq
      rw [infSearchPath_length seq address hp depth, List.length_append] at this
      omega
    have haddr : address q.length = q := by
      rw [← infSearchPath_take seq address hp q.length depth hlen, hq]
      simp
    have hlabel : leaf = labels q.length := by
      apply infSearchLimit_unique seq (address q.length)
      · exact ⟨k, by rw [haddr]; exact InfDeductionTree.labelAt_of_leafAt _ _ hleaf⟩
      · exact hl q.length
    exact ⟨q.length, by rw [haddr, ← hlabel]; exact hleaf⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem appendToLeavesCore_allInnerOpen {s} (t : InfDeductionTree s)
    (h : t.AllInnerOpen) (a b) : (appendToLeavesCore t a b).AllInnerOpen := by
  apply InfDeductionTree.allInnerOpen_bindLeaves _ _ _ h
  intro leaf
  split
  · trivial
  · next hn =>
    exact ⟨fun ha => hn ((isAxiomBool_iff leaf).mpr ha), trivial⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infExpand_allInnerOpen (st : InfSearchState) (h : st.tree.AllInnerOpen) :
    (infExpand st).tree.AllInnerOpen := by
  apply InfDeductionTree.allInnerOpen_bindLeaves _ _ _ h
  intro s
  split
  · trivial
  · apply appendToLeavesCore_allInnerOpen
    apply InfDeductionTree.allInnerOpen_ofDeductionTree
    exact Search.allInnerOpen_expandLeaf s

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infSearchSteps_allInnerOpen (seq : InfSequent) (k : Nat) :
    (infSearchSteps seq k).tree.AllInnerOpen := by
  induction k with
  | zero => trivial
  | succ k ih => exact infExpand_allInnerOpen _ ih

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- A closed leaf retains its address and remains terminal after every round. -/
theorem infExpand_closed_leafAt (st : InfSearchState) (p : List Nat) (label : Sequent)
    (hp : st.tree.leafAt p = some label) (ha : isAxiom label) :
    (infExpand st).tree.leafAt p = some label := by
  apply InfDeductionTree.leafAt_bindLeaves_of_fixed _ _ p hp
  simp [(infIsFinishedLeafBool_iff st label).mpr (Or.inl ha)]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infSearchSteps_closed_leafAt (seq : InfSequent) (k n : Nat)
    (p : List Nat) (label : Sequent)
    (hp : (infSearchSteps seq k).tree.leafAt p = some label) (ha : isAxiom label) :
    (infSearchSteps seq (k + n)).tree.leafAt p = some label := by
  induction n with
  | zero => exact hp
  | succ n ih => exact infExpand_closed_leafAt _ p label ih ha

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- An axiom in the actual limit tree has no child. -/
theorem infSearchLimit_axiom_terminal (seq : InfSequent) (p : List Nat)
    (label : Sequent) (hp : infSearchLimit seq p label) (ha : isAxiom label)
    (i : Nat) : ¬ ∃ child, infSearchLimit seq (p ++ [i]) child := by
  obtain ⟨k, hk⟩ := hp
  have hleaf := InfDeductionTree.leafAt_of_axiom _
    (infSearchSteps_allInnerOpen seq k) p hk ha
  rintro ⟨child, m, hm⟩
  have hleaf' := infSearchSteps_closed_leafAt seq k m p label hleaf ha
  have hm' := infSearchSteps_labelAt_mono seq m k (p ++ [i]) child hm
  rw [Nat.add_comm m k] at hm'
  have hnone := InfDeductionTree.labelAt_child_of_leafAt _ p i hleaf'
  rw [hnone] at hm'
  contradiction

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every label on an infinite path of the actual search limit is nonaxiomatic. -/
theorem infSearchPath_nonaxiom (seq : InfSequent) (address : Nat → List Nat)
    (labels : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (labels n)) :
    ∀ n, ¬ isAxiom (labels n) := by
  intro n ha
  obtain ⟨i, _, hi⟩ := infSearchPath_step seq address hp n
  apply infSearchLimit_axiom_terminal seq (address n) (labels n) (hl n) ha i
  exact ⟨labels (n + 1), hi ▸ hl (n + 1)⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfSearchClosedProofTreeSeq_valid := by
  -- BEGIN PROOF
    intro v hAnt
    -- Extract hypotheses from antecedent
    have h0 : v 1 = BoolVal.T := by
      have := hAnt _ (List.Mem.head _); simp [evalExtN] at this; exact this
    have h01 : hImplies (v 1) (v 2) = BoolVal.T := by
      have := hAnt _ (List.Mem.tail _ (List.Mem.head _)); simp [evalExtN] at this; exact this
    have h12 : hImplies (v 2) (v 3) = BoolVal.T := by
      have := hAnt _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      simp [evalExtN] at this; exact this
    have h23 : hImplies (v 3) (v 4) = BoolVal.T := by
      have := hAnt _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      simp [evalExtN] at this; exact this
    -- Chain modus ponens: P0=T, P0=>P1=T => P1=T, etc.
    have h1 : v 2 = BoolVal.T := by
      rw [h0] at h01; simp [hImplies] at h01
      cases h : v 2 <;> simp_all [hImplies]
    have h2 : v 3 = BoolVal.T := by
      rw [h1] at h12; simp [hImplies] at h12
      cases h : v 3 <;> simp_all [hImplies]
    have h3 : v 4 = BoolVal.T := by
      rw [h2] at h23; simp [hImplies] at h23
      cases h : v 4 <;> simp_all [hImplies]
    -- P3 is in the succedent
    exact ⟨.var 4, List.Mem.tail _ (List.Mem.head _), by simp [evalExtN, h3]⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfSearchClosedProofTree_nonempty := ⟨exInfSearchClosedProofTree⟩

end LCS.Propositional.Infinite
end

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfFalsifyingValuation_falsifies := by
  constructor
  · intro n A h
    cases n with
    | zero =>
      simp [exInfSearchNonTerminating] at h
      subst A
      rfl
    | succ n =>
      simp [exInfSearchNonTerminating] at h
      subst A
      simp [evalExtN, exInfFalsifyingValuation, hImplies]
  · intro n B h
    cases n with
    | zero =>
      simp [exInfSearchNonTerminating] at h
      subst B
      rfl
    | succ n => simp [exInfSearchNonTerminating] at h

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The atomic initial label is not finished while the input has a tail. -/
theorem exInfSearchClosedInit_unfinished :
    infIsFinishedTreeBool exInfSearchClosedInit = false := by decide

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The first round extends below the original root. -/
theorem exInfSearchClosed_first_round_child :
    (infSearchSteps exInfSearchClosedAntecedent 1).tree.labelAt [0] =
      some (Sequent.mk [.var 1, .impl (.var 1) (.var 2)] [.var 0, .var 4]) := by
  decide

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- None of the first four stages is prematurely reported as finished. -/
theorem exInfSearchClosed_before_round4 :
    (List.range 4).all (fun k =>
      !infIsFinishedTreeBool (infSearchSteps exInfSearchClosedAntecedent k)) = true := by
  decide

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfSearchClosedRound4_closed := by
  have hall : exInfSearchClosedRound4.tree.leaves.all isAxiomBool = true := by decide
  intro leaf hmem
  exact (isAxiomBool_iff leaf).mp ((List.all_eq_true.mp hall) leaf hmem)

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmostAddress_step (n : Nat) :
    exInfRightmostAddress (n + 1) = exInfRightmostAddress n ++ [n % 2] := by
  simp [exInfRightmostAddress, List.range_succ]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper @[simp] theorem exInfRightmostLabel_even (n : Nat) :
    exInfRightmostLabel (2 * n) = exInfRightmostCheckpoint n := by
  have hd : 2 * n / 2 = n := by omega
  have hm : 2 * n % 2 = 0 := by omega
  simp [exInfRightmostLabel, hd, hm]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper @[simp] theorem exInfRightmostLabel_odd (n : Nat) :
    exInfRightmostLabel (2 * n + 1) = exInfRightmostIntroduced n := by
  have hd : (2 * n + 1) / 2 = n := by omega
  have hm : (2 * n + 1) % 2 = 1 := by omega
  simp [exInfRightmostLabel, hd, hm]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmostAtoms_atomic (n : Nat) :
    (exInfRightmostAtoms n).all isAtomicBool = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [exInfRightmostAtoms, isAtomicBool] using ih

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmostCheckpoint_open (n : Nat) : ¬ isAxiom (exInfRightmostCheckpoint n) := by
  rintro ⟨A, hA, hQ⟩
  simp only [exInfRightmostCheckpoint, List.mem_singleton] at hQ
  subst A
  obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem n _).mp hA
  exact exInfChainVariables_disjoint i hi.symm

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmostIntroduced_open (n : Nat) : ¬ isAxiom (exInfRightmostIntroduced n) := by
  rintro ⟨A, hA, hQ⟩
  simp only [exInfRightmostIntroduced, List.mem_singleton] at hQ
  subst A
  simp only [exInfRightmostIntroduced, List.mem_append, List.mem_singleton] at hA
  rcases hA with hA | hA
  · obtain ⟨i, _, hi⟩ := (exInfRightmostAtoms_mem n _).mp hA
    exact exInfChainVariables_disjoint i hi.symm
  · cases hA

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- A checkpoint's introduced implication keeps this leaf unfinished. -/
theorem exInfRightmostIntroduced_unfinished (st : InfSearchState) (n : Nat) :
    ¬ infIsFinishedLeaf st (exInfRightmostIntroduced n) := by
  rintro (ha | ⟨_, _, hatom⟩)
  · exact exInfRightmostIntroduced_open n ha
  · have hm : .impl (.var (n + 1)) (.var (n + 2)) ∈
        (exInfRightmostIntroduced n).antecedent ++ (exInfRightmostIntroduced n).succedent := by
      simp [exInfRightmostIntroduced]
    exact hatom _ hm

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmost_succedent_union (A : PropFormulaNormalized) :
    (∃ n, A ∈ (exInfRightmostLabel n).succedent) ↔ exInfBranchConclusions A := by
  have hlabel : ∀ n, (exInfRightmostLabel n).succedent = [.var 0] := by
    intro n
    unfold exInfRightmostLabel
    split <;> rfl
  simp [hlabel, exInfBranchConclusions]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- The actual replacement below the rightmost introduced leaf in the next round. -/
def exInfRightmostRound (n : Nat) : InfDeductionTree (exInfRightmostIntroduced n) :=
  appendToLeavesCore
    (InfDeductionTree.ofDeductionTree (expandLeaf .systematic (exInfRightmostIntroduced n)))
    (some (.impl (.var (n + 2)) (.var (n + 3)))) none

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem exInfRightmostRound_checkpoint (n : Nat) :
    (exInfRightmostRound n).labelAt [1] = some (exInfRightmostCheckpoint (n + 1)) := by
  unfold exInfRightmostRound exInfRightmostIntroduced
  rw [Search.expandLeaf_finalImplication (exInfRightmostAtoms n) (n + 1) (n + 2) 0
    (exInfRightmostAtoms_atomic n) (exInfRightmostIntroduced_open n)]
  simp [Search.finalImplicationTree, appendToLeavesCore, InfDeductionTree.ofDeductionTree,
    InfDeductionTree.bindLeaves, InfDeductionTree.labelAt, exInfRightmostCheckpoint,
    exInfRightmostAtoms]

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfRightmost_checkpoints := by
  simpa only [exInfRightmostLabel_even, exInfRightmostCheckpoint] using
    exInfRightmost_labels_in_limit (2 * n)

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfHintikkaSet_actual_branch := by
  cases sf with
  | trueSign A => exact (exInfRightmost_antecedent_union A).symm
  | falseSign A => exact (exInfRightmost_succedent_union A).symm

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of exInfHintikkaSet_satisfied := by
  cases sf with
  | trueSign A =>
    rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [evalExtN, exInfFalsifyingValuation, hImplies]
  | falseSign A =>
    change A = .var 0 at h
    subst A
    rfl

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of infSeqProvable_implies_valid := by
  -- BEGIN PROOF
    -- Extract the finite witnessing sequent and its provability
    obtain ⟨Gamma_fin, Delta_fin, hGamma, hDelta, hProv⟩ := h
    -- By soundness of G' (Lemma 3.4.3), the finite sequent is valid
    have hValid := soundness_G (Sequent.mk Gamma_fin Delta_fin) hProv
    -- Lift finite validity to the infinite sequent
    intro v hAnt
    -- v satisfies all antecedent formulae of the infinite sequent
    -- In particular, v satisfies the finite subset Gamma_fin
    have hFinAnt : ∀ A ∈ Gamma_fin, evalExtN v A = BoolVal.T := by
      intro A hA
      obtain ⟨n, hn⟩ := hGamma A hA
      exact hAnt n A hn
    -- By validity of the finite sequent, some B in Delta_fin is true
    obtain ⟨B, hBmem, hBtrue⟩ := hValid v hFinAnt
    -- This B is also in the infinite succedent
    obtain ⟨m, hm⟩ := hDelta B hBmem
    exact ⟨m, B, hm, hBtrue⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
namespace TreeDomain

helper /-- Every descendant of a child of p is a descendant of p -/
theorem descendants_of_child (T : TreeDomain) (p c : T.Node)
    (hch : T.children p c) (n : T.Node) (hn : T.descendants c n) :
    T.descendants p n := by
-- BEGIN PROOF
  obtain ⟨hnode, hreach⟩ := hn
  exact ⟨hnode, Reachable.step p c n hch hreach⟩

end TreeDomain
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of konig_lemma := by
  -- BEGIN PROOF
    -- First, show root has infinite descendants
    have hroot_inf : ¬ Set.Finite (T.descendants T.root) := by
      intro hfin
      apply h_infinite
      apply Set.Finite.subset hfin
      intro n hn
      exact ⟨hn, h_allReachable n hn⟩
    -- Build a choice function: given a node with infinite descendants,
    -- pick a child with infinite descendants
    have choose_child : ∀ p, T.isNode p → ¬ Set.Finite (T.descendants p) →
        ∃ c, T.children p c ∧ ¬ Set.Finite (T.descendants c) := by
      intro p hp hinf
      exact T.exists_child_infinite_desc p hp hinf (fun n hn => h_tree p n hn.1 hn.2)
    -- Use Classical.choose to make a definite selection function
    let chosenChild : (p : T.Node) → T.isNode p → ¬ Set.Finite (T.descendants p) → T.Node :=
      fun p hp hinf => Classical.choose (choose_child p hp hinf)
    have chosenChild_spec : ∀ p hp hinf,
        T.children p (chosenChild p hp hinf) ∧
        ¬ Set.Finite (T.descendants (chosenChild p hp hinf)) :=
      fun p hp hinf => Classical.choose_spec (choose_child p hp hinf)
    have chosenChild_isNode : ∀ p hp hinf,
        T.isNode (chosenChild p hp hinf) :=
      fun p hp hinf =>
        T.childrenAreNodes p _ hp (chosenChild_spec p hp hinf).1
    -- Bundle type for the recursion
    -- Use Nat.rec to iterate: seq n = (node_n, isNode_n, infDesc_n)
    let stepB : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } →
                { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      fun ⟨p, hp, hinf⟩ =>
        ⟨chosenChild p hp hinf, chosenChild_isNode p hp hinf, (chosenChild_spec p hp hinf).2⟩
    let init : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      ⟨T.root, T.rootIsNode, hroot_inf⟩
    -- iterB n = stepB^n(init)
    let iterB : Nat → { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      fun n => Nat.rec init (fun _ prev => stepB prev) n
    -- The children relation: stepB produces a child of the input
    have hch_step : ∀ b : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) },
        T.children b.1 (stepB b).1 := by
      intro ⟨p, hp, hinf⟩
      exact (chosenChild_spec p hp hinf).1
    -- Extract path and prove infinite path property
    exact ⟨fun n => (iterB n).1, rfl, fun n => hch_step (iterB n)⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Once a fixed label is finished, advancing empty tails preserves that fact. -/
theorem infIsFinishedLeaf_after_expand (st : InfSearchState) (label : Sequent)
    (h : infIsFinishedLeaf st label) : infIsFinishedLeaf (infExpand st) label := by
  rcases h with ha | ⟨hL, hR, hatom⟩
  · exact Or.inl ha
  · exact Or.inr ⟨fun n => hL (n + 1), fun n => hR (n + 1), hatom⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every surviving open leaf lies strictly below its expansion root. -/
theorem appendToLeavesCore_open_leaf_depth {s label : Sequent} (t : InfDeductionTree s)
    (a b) (p : List Nat) (hp : (appendToLeavesCore t a b).leafAt p = some label)
    (ho : ¬ isAxiom label) : 0 < p.length := by
  obtain ⟨q, suffix, leaf, rfl, _, hf⟩ :=
    InfDeductionTree.leafAt_bindLeaves_decompose _ t p hp
  by_cases ha : isAxiomBool leaf = true
  · simp only [ha, ↓reduceIte] at hf
    cases suffix with
    | nil =>
      simp only [InfDeductionTree.leafAt, Option.some.injEq] at hf
      subst label
      exact False.elim (ho ((isAxiomBool_iff leaf).mp ha))
    | cons => simp [InfDeductionTree.leafAt] at hf
  · simp only [ha] at hf
    cases suffix with
    | nil => simp [InfDeductionTree.leafAt] at hf
    | cons i suffix => simp only [List.length_append, List.length_cons]; omega

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every still-unfinished leaf has gained at least one edge in every round. -/
theorem infSearchSteps_unfinished_depth (seq : InfSequent) (k : Nat)
    (p : List Nat) (label : Sequent)
    (hp : (infSearchSteps seq k).tree.leafAt p = some label)
    (hu : ¬ infIsFinishedLeaf (infSearchSteps seq k) label) : k ≤ p.length := by
  induction k generalizing p label with
  | zero => omega
  | succ k ih =>
    obtain ⟨q, suffix, leaf, rfl, hq, hf⟩ :=
      InfDeductionTree.leafAt_bindLeaves_decompose _ (infSearchSteps seq k).tree p hp
    by_cases hfin : infIsFinishedLeafBool (infSearchSteps seq k) leaf = true
    · simp only [hfin, ↓reduceIte] at hf
      cases suffix with
      | nil =>
        simp only [InfDeductionTree.leafAt, Option.some.injEq] at hf
        subst label
        exact False.elim (hu (infIsFinishedLeaf_after_expand _ _
          ((infIsFinishedLeafBool_iff _ _).mp hfin)))
      | cons => simp [InfDeductionTree.leafAt] at hf
    · have huOld : ¬ infIsFinishedLeaf (infSearchSteps seq k) leaf :=
        fun h => hfin ((infIsFinishedLeafBool_iff _ _).mpr h)
      have hdepth := ih q leaf hq huOld
      simp only [hfin] at hf
      have hmore := appendToLeavesCore_open_leaf_depth _ _ _ suffix hf
        (fun ha => hu (Or.inl ha))
      simp only [List.length_append]
      omega

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Nontermination gives actual limit nodes at unbounded depths. -/
theorem infSearch_unbounded_of_not_halts (seq : InfSequent) (h : ¬ infSearchHalts seq) :
    ∀ k, ∃ p, (infSearchTreeDomain seq).isNode p ∧ k ≤ p.length := by
  classical
  intro k
  have hex : ∃ leaf, leaf ∈ (infSearchSteps seq k).tree.leaves ∧
      ¬ infIsFinishedLeaf (infSearchSteps seq k) leaf := by
    apply Classical.byContradiction
    intro hn
    apply h
    refine ⟨k, ?_⟩
    intro leaf hmem
    by_cases hf : infIsFinishedLeaf (infSearchSteps seq k) leaf
    · exact hf
    · exact False.elim (hn ⟨leaf, hmem, hf⟩)
  obtain ⟨leaf, hmem, hnot⟩ := hex
  obtain ⟨p, hp⟩ := InfDeductionTree.leafAt_of_mem_leaves _ hmem
  exact ⟨p, ⟨leaf, k, InfDeductionTree.labelAt_of_leafAt _ _ hp⟩,
    infSearchSteps_unfinished_depth seq k p leaf hp hnot⟩

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper theorem infSearch_infinite_of_not_halts (seq : InfSequent) (h : ¬ infSearchHalts seq) :
    ¬ Set.Finite (infSearchTreeDomain seq).isNode := by
  rintro ⟨nodes, hnodes⟩
  let bound := (nodes.map List.length).foldl max 0
  obtain ⟨p, hp, hdepth⟩ := infSearch_unbounded_of_not_halts seq h (bound + 1)
  have hmem : p ∈ nodes := (hnodes p).mp hp
  have hbound := Search.Proofs.le_foldl_max_of_mem
    (List.mem_map.mpr ⟨p, hmem, rfl⟩ : p.length ∈ nodes.map List.length)
  omega

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

helper /-- Every node of the addressed search limit is reachable from its root. -/
theorem infSearchTreeDomain_reachable (seq : InfSequent) (p : List Nat)
    (hp : (infSearchTreeDomain seq).isNode p) :
    Reachable (infSearchTreeDomain seq) [] p := by
  have hrev : ∀ q : List Nat, (infSearchTreeDomain seq).isNode q.reverse →
      Reachable (infSearchTreeDomain seq) [] q.reverse := by
    intro q
    induction q with
    | nil => intro _; exact .refl _
    | cons i q ih =>
      simp only [List.reverse_cons]
      intro hn
      obtain ⟨label, k, hk⟩ := hn
      obtain ⟨⟨parent, hparent⟩, hi⟩ := InfDeductionTree.labelAt_parent _ q.reverse i hk
      have hroot := ih ⟨parent, k, hparent⟩
      apply hroot.trans
      apply Reachable.step _ (q.reverse ++ [i]) _
      · refine ⟨?_, label, k, hk⟩
        rcases hi with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact .refl _
  simpa using hrev p.reverse (by simpa using hp)

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of infSearch_infinitePath_of_not_halts := by
  apply konig_lemma (infSearchTreeDomain seq) (infSearch_infinite_of_not_halts seq h)
  · exact fun p hp => infSearchTreeDomain_reachable seq p hp
  · intro p n _ hr
    cases hr with
    | refl => exact Or.inl rfl
    | step p c n hc hn => exact Or.inr ⟨c, hc, hn⟩

end LCS.Propositional.Infinite
end
