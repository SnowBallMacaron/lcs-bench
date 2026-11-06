import LCS.Propositional.Infinite.Search

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

helper theorem isAxiomBool_iff (s : Sequent) : isAxiomBool s = true ↔ isAxiom s := by
  simp only [isAxiomBool, List.any_eq_true, beq_iff_eq, isAxiom]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩; exact ⟨A, hA, hB⟩
  · rintro ⟨A, hA, hB⟩; exact ⟨A, hA, A, hB, rfl⟩

helper theorem infIsFinishedLeafBool_iff (state : InfSearchState) (s : Sequent) :
    infIsFinishedLeafBool state s = true ↔ infIsFinishedLeaf state s := by
  simp only [infIsFinishedLeafBool, infIsFinishedLeaf, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true, isAxiomBool_iff,
    isAtomicBool_iff]
  rw [noHoles_empty_iff state.L state.L_noHoles,
    noHoles_empty_iff state.R state.R_noHoles]
  simp only [and_assoc]

helper theorem infIsFinishedTreeBool_iff (state : InfSearchState) :
    infIsFinishedTreeBool state = true ↔ infIsFinishedTree state := by
  simp [infIsFinishedTreeBool, infIsFinishedTree, List.all_eq_true,
    infIsFinishedLeafBool_iff]

helper /-- No round changes or removes an old label. -/
theorem infExpand_labelAt_preserves (st : InfSearchState) (p : List Nat)
    (label : Sequent) (h : st.tree.labelAt p = some label) :
    (infExpand st).tree.labelAt p = some label :=
  InfDeductionTree.labelAt_bindLeaves_preserves _ _ p label h

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

helper /-- Finite stages form an increasing family of labeled address trees. -/
theorem infSearchSteps_labelAt_mono (seq : InfSequent) (k n : Nat)
    (p : List Nat) (label : Sequent)
    (h : (infSearchSteps seq k).tree.labelAt p = some label) :
    (infSearchSteps seq (k + n)).tree.labelAt p = some label := by
  induction n with
  | zero => exact h
  | succ n ih => exact infExpand_labelAt_preserves _ p label ih

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

helper /-- Later stages extend the complete edge structure of each earlier stage. -/
theorem infSearchSteps_extension (seq : InfSequent) (k n : Nat) :
    InfDeductionTree.Extension (infSearchSteps seq k).tree
      (infSearchSteps seq (k + n)).tree := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (InfDeductionTree.extension_bindLeaves _ _)

helper /-- Infinite paths advance by exactly one binary-tree address component. -/
theorem infSearchPath_step (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) (n : Nat) :
    ∃ i, i < 2 ∧ address (n + 1) = address n ++ [i] := by
  rcases (hp.2 n).1 with h | h
  · exact ⟨0, by decide, h⟩
  · exact ⟨1, by decide, h⟩

helper theorem infSearchPath_length (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) (n : Nat) :
    (address n).length = n := by
  induction n with
  | zero => rw [hp.1]; rfl
  | succ n ih =>
    obtain ⟨i, _, hi⟩ := infSearchPath_step seq address hp n
    simp [hi, ih]

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

helper theorem appendToLeavesCore_allInnerOpen {s} (t : InfDeductionTree s)
    (h : t.AllInnerOpen) (a b) : (appendToLeavesCore t a b).AllInnerOpen := by
  apply InfDeductionTree.allInnerOpen_bindLeaves _ _ _ h
  intro leaf
  split
  · trivial
  · next hn =>
    exact ⟨fun ha => hn ((isAxiomBool_iff leaf).mpr ha), trivial⟩

helper theorem infExpand_allInnerOpen (st : InfSearchState) (h : st.tree.AllInnerOpen) :
    (infExpand st).tree.AllInnerOpen := by
  apply InfDeductionTree.allInnerOpen_bindLeaves _ _ _ h
  intro s
  split
  · trivial
  · apply appendToLeavesCore_allInnerOpen
    apply InfDeductionTree.allInnerOpen_ofDeductionTree
    exact Search.allInnerOpen_expandLeaf s

helper theorem infSearchSteps_allInnerOpen (seq : InfSequent) (k : Nat) :
    (infSearchSteps seq k).tree.AllInnerOpen := by
  induction k with
  | zero => trivial
  | succ k ih => exact infExpand_allInnerOpen _ ih

helper /-- A closed leaf retains its address and remains terminal after every round. -/
theorem infExpand_closed_leafAt (st : InfSearchState) (p : List Nat) (label : Sequent)
    (hp : st.tree.leafAt p = some label) (ha : isAxiom label) :
    (infExpand st).tree.leafAt p = some label := by
  apply InfDeductionTree.leafAt_bindLeaves_of_fixed _ _ p hp
  simp [(infIsFinishedLeafBool_iff st label).mpr (Or.inl ha)]

helper theorem infSearchSteps_closed_leafAt (seq : InfSequent) (k n : Nat)
    (p : List Nat) (label : Sequent)
    (hp : (infSearchSteps seq k).tree.leafAt p = some label) (ha : isAxiom label) :
    (infSearchSteps seq (k + n)).tree.leafAt p = some label := by
  induction n with
  | zero => exact hp
  | succ n ih => exact infExpand_closed_leafAt _ p label ih ha

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

helper /-- Every label on an infinite path of the actual search limit is nonaxiomatic. -/
theorem infSearchPath_nonaxiom (seq : InfSequent) (address : Nat → List Nat)
    (labels : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (labels n)) :
    ∀ n, ¬ isAxiom (labels n) := by
  intro n ha
  obtain ⟨i, _, hi⟩ := infSearchPath_step seq address hp n
  apply infSearchLimit_axiom_terminal seq (address n) (labels n) (hl n) ha i
  exact ⟨labels (n + 1), hi ▸ hl (n + 1)⟩

helper /-- Once a fixed label is finished, advancing empty tails preserves that fact. -/
theorem infIsFinishedLeaf_after_expand (st : InfSearchState) (label : Sequent)
    (h : infIsFinishedLeaf st label) : infIsFinishedLeaf (infExpand st) label := by
  rcases h with ha | ⟨hL, hR, hatom⟩
  · exact Or.inl ha
  · exact Or.inr ⟨fun n => hL (n + 1), fun n => hR (n + 1), hatom⟩

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

helper theorem infSearch_infinite_of_not_halts (seq : InfSequent) (h : ¬ infSearchHalts seq) :
    ¬ Set.Finite (infSearchTreeDomain seq).isNode := by
  rintro ⟨nodes, hnodes⟩
  let bound := (nodes.map List.length).foldl max 0
  obtain ⟨p, hp, hdepth⟩ := infSearch_unbounded_of_not_halts seq h (bound + 1)
  have hmem : p ∈ nodes := (hnodes p).mp hp
  have hbound := Search.Procedure.Proofs.le_foldl_max_of_mem
    (List.mem_map.mpr ⟨p, hmem, rfl⟩ : p.length ∈ nodes.map List.length)
  omega

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

proof_of infSearch_infinitePath_of_not_halts := by
  apply konig_lemma (infSearchTreeDomain seq) (infSearch_infinite_of_not_halts seq h)
  · exact fun p hp => infSearchTreeDomain_reachable seq p hp
  · intro p n _ hr
    cases hr with
    | refl => exact Or.inl rfl
    | step p c n hc hn => exact Or.inr ⟨c, hc, hn⟩

end LCS.Propositional.Infinite
end
