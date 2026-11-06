import LCS.Resolution.Method.FiniteGraph

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace FiniteGraph

helper theorem FiniteGraph.next_exists_iff {g : FiniteGraph} {i p : Nat} :
    (g.next i p).isSome = true ↔
      p < 2 ∧ (g.next i 0).isSome = true := by
  cases hn : g.node i with
  | none => simp [next, hn]
  | some n =>
    cases hr : n.inference with
    | none => simp [next, hn, hr]
    | some r =>
      by_cases h0 : p = 0
      · simp [next, hn, hr, h0]
      · by_cases h1 : p = 1
        · simp [next, hn, hr, h1]
        · simp [next, hn, hr, h0, h1]; omega

helper theorem FiniteGraph.followFrom_index_lt {g : FiniteGraph} (hg : g.WellFormed)
    {i j : Nat} {a : LCS.TreeAddr} (hi : i < g.table.length)
    (h : g.followFrom i a = some j) : j < g.table.length := by
  have := followFrom_length_bound hg h
  omega

proof_of follow_index_lt := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  followFrom_index_lt hg hg.1 h


proof_of domain_prefix_closed := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    change (g.follow (a ++ b)).isSome = true at h
    rw [follow_append] at h
    cases ha : g.follow a with
    | none => simp [ha] at h
    | some i => show (g.follow a).isSome = true; simp [ha]


proof_of child_domain_iff := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    change (g.follow (a ++ [p])).isSome = true ↔
      p < 2 ∧ (g.follow (a ++ [0])).isSome = true
    simp only [follow_append, followFrom]
    cases ha : g.follow a with
    | none => simp
    | some i => simpa using (next_exists_iff (g := g) (i := i) (p := p))


proof_of domain_finite := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    apply Classical.byContradiction
    intro h
    have hfb : g.treeDomain.FinitelyBranching := by
      intro a _
      exact ⟨2, fun i hi hm => by
        have := (g.child_domain_iff a i).mp hm |>.1
        omega⟩
    obtain ⟨a, ha, hlen⟩ :=
      g.treeDomain.not_finite_is_infinite hfb h (g.root + 1)
    change (g.follow a).isSome = true at ha
    cases hf : g.follow a with
    | none => simp [hf] at ha
    | some i =>
      have hb := followFrom_length_bound hg hf
      omega


proof_of addressRel_equiv := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩


proof_of addressRel_follow_eq := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    unfold addressRel addressKey at h
    cases ha : g.follow a <;> cases hb : g.follow b <;> simp_all


helper theorem FiniteGraph.addressRel_prefix_eq {g : FiniteGraph} (hg : g.WellFormed)
    {a b : LCS.TreeAddr} (h : g.addressRel a b)
    (hp : List.isPrefixOf a b = true) : a = b := by
  obtain ⟨suffix, rfl⟩ := List.isPrefixOf_iff_prefix.mp hp
  cases ha : g.follow a with
  | none =>
    have hb := addressRel_follow_eq h
    have hb0 : g.follow (a ++ suffix) = none := hb.symm.trans ha
    simpa [addressRel, addressKey, ha, hb0] using h
  | some i =>
    have hb := addressRel_follow_eq h
    rw [ha, follow_append, ha] at hb
    have hs : g.followFrom i suffix = some i := by simpa using hb.symm
    have hlen := followFrom_length_bound hg hs
    have hz : suffix.length = 0 := by omega
    have he := List.length_eq_zero_iff.mp hz
    simp [he]

proof_of addressRel_independent := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    exact ⟨fun hp => hne (addressRel_prefix_eq hg h hp),
      fun hp => hne (addressRel_prefix_eq hg h.symm hp).symm⟩


proof_of follow_vertexAt := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  (Option.some_get ha).symm


helper theorem FiniteGraph.vertexAt_eq {g : FiniteGraph} {a : LCS.TreeAddr} {i : Nat}
    (ha : a ∈ g.domain) (h : g.follow a = some i) : g.vertexAt a ha = i :=
  Option.get_of_eq_some ha h

helper theorem FiniteGraph.labeledTree_label_eq {g : FiniteGraph} (hg : g.WellFormed)
    {a : LCS.TreeAddr} (ha : a ∈ g.domain) {i : Nat} {n : Node}
    (hf : g.follow a = some i) (hn : g.node i = some n) :
    (g.labeledTree hg).label a ha = n.clause := by
  have hv := vertexAt_eq ha hf
  have hlabel := g.node_vertexAt hg a ha
  rw [hv] at hlabel
  simpa [label, hn] using hlabel.symm

proof_of labelAtOpt_labeledTree := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    classical
    by_cases ha : a ∈ g.domain
    · rw [labelAtOpt_of_mem _ _ ha, g.follow_vertexAt a ha]
      exact (g.node_vertexAt hg a ha).symm
    · have hf : g.follow a = none := by
        cases h : g.follow a with
        | none => rfl
        | some i => exact False.elim (ha (by show (g.follow a).isSome = true; simp [h]))
      simp only [labelAtOpt, labeledTree, treeDomain]
      simp [ha, hf]


proof_of addressRel_children := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    change (g.follow (a ++ [p])).isSome = true ↔
      (g.follow (b ++ [p])).isSome = true
    rw [follow_append, follow_append, addressRel_follow_eq h]


proof_of addressRel_childRel := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    have hf : g.follow (a ++ [p]) = g.follow (b ++ [p]) := by
      rw [follow_append, follow_append, addressRel_follow_eq h]
    change (g.follow (a ++ [p])).isSome = true at ha
    unfold addressRel addressKey
    cases hfa : g.follow (a ++ [p]) with
    | none => simp [hfa] at ha
    | some i => rw [← hf, hfa]

helper theorem FiniteGraph.exists_mem_leafIds (g : FiniteGraph) (hwf : g.WellFormed) :
    ∃ j, j ∈ g.leafIds := by
  have hn : g.node g.root = some (g.table[g.root]'hwf.1) :=
    List.getElem?_eq_some_iff.mpr ⟨hwf.1, rfl⟩
  obtain ⟨a, j, ha, hj, hlen⟩ := exists_leaf_path g hwf g.root _ hn
  refine ⟨j, List.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact (mem_vertexIds_iff g j).mpr ⟨a, ha, by have := hwf.1; omega⟩
  · simp [hj]

helper theorem FiniteGraph.nodeCount_eq_stepCount_add_leafCount (g : FiniteGraph) :
    g.nodeCount = g.stepCount + g.leafIds.length := by
  change g.vertexIds.length =
    (g.vertexIds.filter g.isInternal).length +
    (g.vertexIds.filter fun i => !g.isInternal i).length
  have h := List.length_eq_countP_add_countP g.isInternal (l := g.vertexIds)
  simpa [List.countP_eq_length_filter] using h

helper theorem FiniteGraph.stepCount_add_one_le_nodeCount (g : FiniteGraph) (hwf : g.WellFormed) :
    g.stepCount + 1 ≤ g.nodeCount := by
  obtain ⟨j, hj⟩ := exists_mem_leafIds g hwf
  have hpos : 0 < g.leafIds.length := List.length_pos_iff_exists_mem.mpr ⟨j, hj⟩
  have hcount := nodeCount_eq_stepCount_add_leafCount g
  omega

helper /-- Each vertex other than the root occurs in a premise position of a reachable step. -/
theorem FiniteGraph.vertexIds_covered_by_steps (g : FiniteGraph) (j : Nat)
    (hj : j ∈ g.vertexIds) :
    j = g.root ∨ ∃ i, i ∈ g.stepIds ∧
      (g.next i 0 = some j ∨ g.next i 1 = some j) := by
  obtain ⟨a, ha, hlen⟩ := (mem_vertexIds_iff g j).mp hj
  by_cases hempty : a = []
  · subst a
    exact Or.inl (Option.some.inj ha).symm
  · let pathPrefix := a.dropLast
    let p := a.getLast hempty
    have heq : pathPrefix ++ [p] = a := List.dropLast_concat_getLast hempty
    have hlookup : g.followFrom g.root (pathPrefix ++ [p]) = some j := by
      simpa only [heq, follow] using ha
    rw [followFrom_append] at hlookup
    cases hi : g.followFrom g.root pathPrefix with
    | none => simp [hi] at hlookup
    | some i =>
      have hnext : g.next i p = some j := by
        simpa [hi, followFrom] using hlookup
      have hipathPrefix : i ∈ g.vertexIds :=
        (mem_vertexIds_iff g i).mpr ⟨pathPrefix, hi, by
          have heqlen := congrArg List.length heq
          simp only [List.length_append, List.length_singleton] at heqlen
          omega⟩
      obtain ⟨n, r, hn, hr, _⟩ := next_spec hnext
      have hiStep : i ∈ g.stepIds :=
        List.mem_filter.mpr ⟨hipathPrefix, by simp [isInternal, hn, hr]⟩
      refine Or.inr ⟨i, hiStep, ?_⟩
      have hp : p = 0 ∨ p = 1 := by
        have := next_position_lt hnext
        omega
      rcases hp with hp | hp
      · exact Or.inl (by simpa only [hp] using hnext)
      · exact Or.inr (by simpa only [hp] using hnext)

helper theorem FiniteGraph.nodup_length_le_of_subset {α : Type} [DecidableEq α]
    {xs ys : List α} (hNodup : xs.Nodup)
    (hSubset : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    have hParts := List.nodup_cons.mp hNodup
    have hHead : head ∈ ys := hSubset head List.mem_cons_self
    have hTailSubset : ∀ x, x ∈ tail → x ∈ ys.erase head := by
      intro x hx
      apply (List.mem_erase_of_ne ?_).mpr
        (hSubset x (List.mem_cons.mpr (Or.inr hx)))
      intro hEq
      subst x
      exact hParts.1 hx
    have hTailLe := ih hParts.2 hTailSubset
    have hLength := (List.perm_cons_erase hHead).length_eq
    simp only [List.length_cons] at hLength ⊢
    omega

helper theorem FiniteGraph.nodeCount_le_two_stepCount_add_one (g : FiniteGraph) :
    g.nodeCount ≤ 2 * g.stepCount + 1 := by
  let slots := g.stepIds.flatMap fun i => [g.next i 0, g.next i 1]
  have hcoverage : ∀ x, x ∈ g.vertexIds.map some → x ∈ some g.root :: slots := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rcases vertexIds_covered_by_steps g j hj with rfl | ⟨i, hi, hnext⟩
    · exact List.mem_cons_self
    · apply List.mem_cons.mpr; right
      apply List.mem_flatMap.mpr
      refine ⟨i, hi, ?_⟩
      rcases hnext with h | h <;> simp [h]
  have hnodup : (g.vertexIds.map some).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact (vertexIds_nodup g).imp (fun hne heq => hne (Option.some.inj heq))
  have hle := nodup_length_le_of_subset hnodup hcoverage
  have hslots : slots.length = 2 * g.stepIds.length := by
    dsimp [slots]
    generalize g.stepIds = ids
    induction ids with
    | nil => simp
    | cons i rest ih => simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at *; omega
  simpa only [List.length_map, List.length_cons, hslots, nodeCount, stepCount] using hle

helper theorem FiniteGraph.isInternal_iff_child {g : FiniteGraph} {a : LCS.TreeAddr} {i : Nat}
    (hf : g.follow a = some i) :
    g.isInternal i = true ↔ (a ++ [0]) ∈ g.domain := by
  change _ ↔ (g.follow (a ++ [0])).isSome = true
  rw [follow_append, hf]
  cases hn : g.node i with
  | none => simp [isInternal, hn, followFrom, next]
  | some n =>
    cases hr : n.inference <;> simp [isInternal, hn, hr, followFrom, next]

proof_of resolution_labels := open LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph in
  by
    let i := g.vertexAt a ha
    have hf : g.follow a = some i := g.follow_vertexAt a ha
    have hi := follow_index_lt hg hf
    let n := g.table[i]'hi
    have hn : g.node i = some n := List.getElem?_eq_getElem hi
    have hint := (isInternal_iff_child hf).mpr h0
    cases hr : n.inference with
    | none => simp [isInternal, hn, hr] at hint
    | some r =>
      obtain ⟨na, nb, hna, hnb, hp, hcp, heq⟩ :=
        hg.2.2 i (follow_mem_vertexIds hg hf) n hn r hr
      have hf0 : g.follow (a ++ [0]) = some r.left := by
        simp [follow_append, hf, followFrom, next, hn, hr]
      have hf1 : g.follow (a ++ [1]) = some r.right := by
        simp [follow_append, hf, followFrom, next, hn, hr]
      rw [labeledTree_label_eq hg ha hf hn,
        labeledTree_label_eq hg h0 hf0 hna, labeledTree_label_eq hg h1 hf1 hnb]
      exact ⟨r.pivot, hp, hcp, heq⟩


helper theorem FiniteGraph.toResolutionDAG_rootLabel (g : FiniteGraph) (hg : g.WellFormed) :
    some (g.toResolutionDAG hg).rootLabel = g.rootLabel := by
  exact (g.node_vertexAt hg [] rfl).symm

helper theorem FiniteGraph.toResolutionDAG_leavesFrom (g : FiniteGraph) (hg : g.WellFormed)
    (S : ClauseSequent) : (g.toResolutionDAG hg).leavesFrom S ↔ g.LeavesFrom S := by
  constructor
  · intro h i hi
    obtain ⟨hreach, hinternal⟩ := List.mem_filter.mp hi
    have hint : g.isInternal i = false := by simpa using hinternal
    obtain ⟨a, hf, _⟩ := (mem_vertexIds_iff g i).mp hreach
    have ha : a ∈ g.domain := by show (g.follow a).isSome = true; simp [hf]
    have hleaf : ¬ (a ++ [0]) ∈ g.domain := by
      intro hc
      have := (isInternal_iff_child hf).mpr hc
      simp [hint] at this
    refine ⟨(g.labeledTree hg).label a ha, ?_, h a ha hleaf⟩
    have hv := vertexAt_eq ha hf
    simpa [hv] using g.node_vertexAt hg a ha
  · intro h a ha hleaf
    let i := g.vertexAt a ha
    have hf : g.follow a = some i := g.follow_vertexAt a ha
    have hint : g.isInternal i = false := by
      cases hb : g.isInternal i with
      | false => rfl
      | true => exact False.elim (hleaf ((isInternal_iff_child hf).mp hb))
    have hi : i ∈ g.leafIds := List.mem_filter.mpr
      ⟨follow_mem_vertexIds hg hf, by simp [hint]⟩
    obtain ⟨C, hC, hmem⟩ := h i hi
    have heq := (g.node_vertexAt hg a ha).symm.trans hC
    exact (Option.some.inj heq) ▸ hmem

helper theorem FiniteGraph.toResolutionDAG_isRefutationFor (g : FiniteGraph) (hg : g.WellFormed)
    (S : ClauseSequent) :
    (g.toResolutionDAG hg).isRefutationFor S ↔ g.IsRefutationFor S := by
  rw [ResolutionDAG.isRefutationFor, toResolutionDAG_leavesFrom]
  constructor
  · rintro ⟨hleaves, hroot⟩
    exact ⟨hg, hleaves, (toResolutionDAG_rootLabel g hg).symm.trans (congrArg some hroot)⟩
  · rintro ⟨_, hleaves, hroot⟩
    exact ⟨hleaves, Option.some.inj ((toResolutionDAG_rootLabel g hg).trans hroot)⟩

open LCS.Resolution.GCNF

helper /-- The vertex map used for recipient vertices during a graft. -/
def FiniteGraph.graftRedirect (donor : FiniteGraph) (replace : Nat → Bool) (i : Nat) : Nat :=
  if replace i then donor.root else donor.table.length + i

helper /-- Import a recipient row by redirecting its two incoming references. -/
def FiniteGraph.graftNode (donor : FiniteGraph) (replace : Nat → Bool) (n : Node) : Node :=
  { n with inference := n.inference.map fun r =>
    { r with left := graftRedirect donor replace r.left, right := graftRedirect donor replace r.right } }

helper /-- A selected vertex is an input vertex bearing the donor's conclusion. -/
def FiniteGraph.GraftCompatible (donor recipient : FiniteGraph) (replace : Nat → Bool) : Prop :=
  ∀ i n, recipient.node i = some n → replace i = true →
    n.inference = none ∧ donor.rootLabel = some n.clause

helper @[simp] theorem FiniteGraph.graft_table_length (donor recipient : FiniteGraph)
    (replace : Nat → Bool) :
    (graft donor recipient replace).table.length =
      donor.table.length + recipient.table.length := by
  simp [graft]

helper @[simp] theorem FiniteGraph.graft_node_donor {donor recipient : FiniteGraph}
    (replace : Nat → Bool) {i : Nat} (hi : i < donor.table.length) :
    (graft donor recipient replace).node i = donor.node i := by
  simp [node, graft, List.getElem?_append, hi]

helper @[simp] theorem FiniteGraph.graft_node_recipient (donor recipient : FiniteGraph)
    (replace : Nat → Bool) (i : Nat) :
    (graft donor recipient replace).node (donor.table.length + i) =
      (recipient.node i).map (graftNode donor replace) := by
  have h : ¬ donor.table.length + i < donor.table.length := by omega
  simp only [node, graft, List.getElem?_append, h, ↓reduceIte, List.getElem?_map, Nat.add_sub_cancel_left]
  rfl

helper theorem FiniteGraph.graft_node_redirect {donor recipient : FiniteGraph}
    (hd : donor.AllRowsWellFormed) (replace : Nat → Bool)
    (hc : GraftCompatible donor recipient replace) {i : Nat} {n : Node}
    (hn : recipient.node i = some n) :
    ∃ m, (graft donor recipient replace).node (graftRedirect donor replace i) = some m ∧
      m.clause = n.clause := by
  cases hi : replace i with
  | false =>
    refine ⟨graftNode donor replace n, ?_, rfl⟩
    simp [graftRedirect, hi, graft_node_recipient, hn]
  | true =>
    have hl := (hc i n hn hi).2
    unfold rootLabel label at hl
    cases hm : donor.node donor.root with
    | none => simp [hm] at hl
    | some m =>
      refine ⟨m, ?_, ?_⟩
      · simp [graftRedirect, hi, graft_node_donor replace hd.1, hm]
      · simpa [hm] using hl

helper theorem FiniteGraph.graftRedirect_lt {donor : FiniteGraph} (hd : donor.AllRowsWellFormed)
    (replace : Nat → Bool) {i j : Nat} (hij : i < j) :
    graftRedirect donor replace i < donor.table.length + j := by
  unfold graftRedirect
  split <;> have := hd.1 <;> omega

helper theorem FiniteGraph.graft_allRowsWellFormed {donor recipient : FiniteGraph}
    (hd : donor.AllRowsWellFormed) (hr : recipient.AllRowsWellFormed)
    (replace : Nat → Bool) (hc : GraftCompatible donor recipient replace) :
    (graft donor recipient replace).AllRowsWellFormed := by
  refine ⟨?_, ?_⟩
  · change graftRedirect donor replace recipient.root < _
    rw [graft_table_length]
    exact graftRedirect_lt hd replace hr.1
  · intro i n hn r hnr
    by_cases hi : i < donor.table.length
    · rw [graft_node_donor replace hi] at hn
      obtain ⟨hl, hright, a, b, ha, hb, hp, hpc, heq⟩ := hd.2 i n hn r hnr
      refine ⟨hl, hright, a, b, ?_, ?_, hp, hpc, heq⟩
      · rw [graft_node_donor replace (node_index_lt ha)]; exact ha
      · rw [graft_node_donor replace (node_index_lt hb)]; exact hb
    · have hi' : i = donor.table.length + (i - donor.table.length) := by omega
      rw [hi', graft_node_recipient] at hn
      cases ho : recipient.node (i - donor.table.length) with
      | none => simp [ho] at hn
      | some m =>
        have hn' : graftNode donor replace m = n := by simpa [ho] using hn
        subst n
        cases hm : m.inference with
        | none => simp [graftNode, hm] at hnr
        | some s =>
          have hsr : { s with left := graftRedirect donor replace s.left, right := graftRedirect donor replace s.right } = r := by
            simpa [graftNode, hm] using hnr
          subst r
          obtain ⟨hl, hright, a, b, ha, hb, hp, hpc, heq⟩ :=
            hr.2 (i - donor.table.length) m ho s hm
          obtain ⟨a', ha', hae⟩ := graft_node_redirect hd replace hc ha
          obtain ⟨b', hb', hbe⟩ := graft_node_redirect hd replace hc hb
          refine ⟨?_, ?_, a', b', ha', hb', ?_, ?_, ?_⟩
          · rw [hi']; exact graftRedirect_lt hd replace hl
          · rw [hi']; exact graftRedirect_lt hd replace hright
          · simpa [hae] using hp
          · simpa [hbe] using hpc
          · simpa [graftNode, hae, hbe] using heq

helper theorem FiniteGraph.graft_rootLabel {donor recipient : FiniteGraph}
    (hd : donor.AllRowsWellFormed) (hr : recipient.AllRowsWellFormed)
    (replace : Nat → Bool) (hc : GraftCompatible donor recipient replace) :
    (graft donor recipient replace).rootLabel = recipient.rootLabel := by
  cases hn : recipient.node recipient.root with
  | none =>
    have hn' : recipient.table[recipient.root]? = none := hn
    have := List.getElem?_eq_none_iff.mp hn'
    have := hr.1
    omega
  | some n =>
    obtain ⟨m, hm, hme⟩ := graft_node_redirect hd replace hc hn
    change ((graft donor recipient replace).node
      (graftRedirect donor replace recipient.root)).map Node.clause =
      (recipient.node recipient.root).map Node.clause
    simp [hm, hn, hme]

helper @[simp] theorem FiniteGraph.graft_next_donor {donor recipient : FiniteGraph}
    (replace : Nat → Bool) {i : Nat} (hi : i < donor.table.length) (p : Nat) :
    (graft donor recipient replace).next i p = donor.next i p := by
  simp only [next, graft_node_donor replace hi]

helper @[simp] theorem FiniteGraph.graft_next_recipient (donor recipient : FiniteGraph)
    (replace : Nat → Bool) (i p : Nat) :
    (graft donor recipient replace).next (donor.table.length + i) p =
      (recipient.next i p).map (graftRedirect donor replace) := by
  unfold next
  rw [graft_node_recipient]
  cases hn : recipient.node i with
  | none => rfl
  | some n =>
    cases hr : n.inference with
    | none => simp [graftNode, hr]
    | some r =>
      by_cases hp : p = 0
      · simp [graftNode, hr, hp]
      · by_cases hp1 : p = 1 <;> simp [graftNode, hr, hp, hp1]

helper /-- Every surviving graft vertex comes from the donor or an unselected
recipient vertex. The assertion uses rooted graph membership, not table size. -/
theorem FiniteGraph.graft_vertexIds_subset {donor recipient : FiniteGraph}
    (hd : donor.AllRowsWellFormed) (hr : recipient.AllRowsWellFormed)
    (replace : Nat → Bool)
    {j : Nat} (hj : j ∈ (graft donor recipient replace).vertexIds) :
    j ∈ donor.vertexIds ∨
      ∃ i, i ∈ recipient.vertexIds ∧ replace i = false ∧
        j = donor.table.length + i := by
  let P : Nat → Prop := fun j => j ∈ donor.vertexIds ∨
    ∃ i, i ∈ recipient.vertexIds ∧ replace i = false ∧ j = donor.table.length + i
  have hredirect : ∀ i, i ∈ recipient.vertexIds → P (graftRedirect donor replace i) := by
    intro i hi
    cases hs : replace i with
    | false => exact Or.inr ⟨i, hi, hs, by simp [graftRedirect, hs]⟩
    | true => exact Or.inl (by simpa [graftRedirect, hs] using root_mem_vertexIds donor hd.wellFormed)
  have hstep : ∀ i p j, P i → (graft donor recipient replace).next i p = some j → P j := by
    intro i p j hi hn
    rcases hi with hi | ⟨k, hk, hreplace, rfl⟩
    · rw [graft_next_donor replace (vertexIds_index_lt hd.wellFormed hi)] at hn
      exact Or.inl (next_mem_vertexIds hd.wellFormed hi hn)
    · rw [graft_next_recipient] at hn
      cases hn' : recipient.next k p with
      | none => simp [hn'] at hn
      | some l =>
        have he : graftRedirect donor replace l = j := by simpa [hn'] using hn
        subst j
        exact hredirect l (next_mem_vertexIds hr.wellFormed hk hn')
  obtain ⟨a, ha, _⟩ := (mem_vertexIds_iff _ j).mp hj
  exact followFrom_closed hstep
    (hredirect recipient.root (root_mem_vertexIds recipient hr.wellFormed)) ha

helper @[simp] theorem FiniteGraph.graft_isInternal_donor {donor recipient : FiniteGraph}
    (replace : Nat → Bool) {i : Nat} (hi : i < donor.table.length) :
    (graft donor recipient replace).isInternal i = donor.isInternal i := by
  simp only [isInternal, graft_node_donor replace hi]

helper @[simp] theorem FiniteGraph.graft_isInternal_recipient (donor recipient : FiniteGraph)
    (replace : Nat → Bool) (i : Nat) :
    (graft donor recipient replace).isInternal (donor.table.length + i) =
      recipient.isInternal i := by
  simp only [isInternal, graft_node_recipient]
  cases hn : recipient.node i with
  | none => rfl
  | some n => cases hr : n.inference <;> simp [graftNode, hr]

helper /-- Leaves of the graft come from donor leaves or unreplaced recipient leaves. -/
theorem FiniteGraph.graft_leavesFrom {donor recipient : FiniteGraph} {S : ClauseSequent}
    (hd : donor.AllRowsWellFormed) (hr : recipient.AllRowsWellFormed)
    (replace : Nat → Bool)
    (hld : donor.LeavesFrom S)
    (hlr : ∀ i, i ∈ recipient.leafIds → replace i = false →
      ∃ C, recipient.label i = some C ∧ C ∈ S) :
    (graft donor recipient replace).LeavesFrom S := by
  intro j hj
  obtain ⟨hjv, hjl⟩ := List.mem_filter.mp hj
  have hjfalse : (graft donor recipient replace).isInternal j = false := by simpa using hjl
  rcases graft_vertexIds_subset hd hr replace hjv with hdv | ⟨i, hiv, hi, rfl⟩
  · have hbound := vertexIds_index_lt hd.wellFormed hdv
    rw [graft_isInternal_donor replace hbound] at hjfalse
    obtain ⟨C, hl, hC⟩ := hld j (List.mem_filter.mpr ⟨hdv, by simp [hjfalse]⟩)
    refine ⟨C, ?_, hC⟩
    simpa only [label, graft_node_donor replace hbound] using hl
  · rw [graft_isInternal_recipient] at hjfalse
    obtain ⟨C, hl, hC⟩ := hlr i (List.mem_filter.mpr ⟨hiv, by simp [hjfalse]⟩) hi
    refine ⟨C, ?_, hC⟩
    unfold label at hl ⊢
    rw [graft_node_recipient]
    cases hn : recipient.node i with
    | none => simp [hn] at hl
    | some n => simpa [graftNode, hn] using hl

helper theorem FiniteGraph.graft_stepCount_le {donor recipient : FiniteGraph}
    (hd : donor.AllRowsWellFormed) (hr : recipient.AllRowsWellFormed)
    (replace : Nat → Bool) :
    (graft donor recipient replace).stepCount ≤ donor.stepCount + recipient.stepCount := by
  have hsub : ∀ j, j ∈ (graft donor recipient replace).stepIds →
      j ∈ donor.stepIds ++ recipient.stepIds.map (donor.table.length + ·) := by
    intro j hj
    obtain ⟨hjv, hjint⟩ := List.mem_filter.mp hj
    rcases graft_vertexIds_subset hd hr replace hjv with hdv | ⟨i, hiv, hi, rfl⟩
    · rw [graft_isInternal_donor replace (vertexIds_index_lt hd.wellFormed hdv)] at hjint
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨hdv, hjint⟩)
    · rw [graft_isInternal_recipient] at hjint
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hiv, hjint⟩, rfl⟩)
  have hle := nodup_length_le_of_subset (stepIds_nodup _) hsub
  simpa only [List.length_append, List.length_map, stepCount] using hle

end FiniteGraph

end LCS.Resolution.Method
