import LCS.Resolution.Method
import Attach
import LCS.Resolution.Method.FiniteGraph.ProofsStamp

/-! # Finite resolution graphs

The entries of a node table are vertices, rather than occurrences in an unfolded
tree. Premises precede their conclusion in the table. A selected root determines
the represented graph: entries unreachable from it do not contribute vertices
or resolution steps. Keeping those entries allows pruning to preserve vertex
identity. Equal clause labels never identify vertices implicitly.
-/

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace FiniteGraph

/-- The ordered premises and the actual pivot of a resolution step. -/
@[blueprint "chap4__definition_4_3_3"]
structure Inference where
  pivot : Literal
  left : Nat
  right : Nat
  deriving DecidableEq

/-- One stable vertex identifier is its position in the table. -/
@[blueprint "chap4__definition_4_3_3"]
structure Node where
  clause : Clause
  inference : Option Inference
  deriving DecidableEq

end FiniteGraph

/-- An executable representation of a finite, possibly shared, resolution DAG. -/
@[blueprint "chap4__definition_4_3_3"]
structure FiniteGraph where
  table : List FiniteGraph.Node
  root : Nat
  deriving DecidableEq

namespace FiniteGraph

@[blueprint "chap4__definition_4_3_3"]
def node (g : FiniteGraph) (i : Nat) : Option Node := g.table[i]?

@[blueprint "chap4__definition_4_3_3"]
def label (g : FiniteGraph) (i : Nat) : Option Clause :=
  (g.node i).map Node.clause

@[blueprint "chap4__definition_4_3_3"]
def rootLabel (g : FiniteGraph) : Option Clause := g.label g.root

/-- Premise IDs precede their conclusion, including in stored rows outside the
selected rooted graph. -/
@[blueprint "chap4__definition_4_3_3"]
def Topological (g : FiniteGraph) : Prop :=
  ∀ i n, g.node i = some n → ∀ r, n.inference = some r →
    r.left < i ∧ r.right < i

/-- Follow one ordered successor position. Other positions are absent. -/
@[blueprint "chap4__definition_4_3_3"]
def next (g : FiniteGraph) (i position : Nat) : Option Nat := do
  let n ← g.node i
  let r ← n.inference
  if position = 0 then some r.left
  else if position = 1 then some r.right else none

@[blueprint "chap4__definition_4_3_3"]
def followFrom (g : FiniteGraph) (i : Nat) : LCS.TreeAddr → Option Nat
  | [] => some i
  | p :: rest => (g.next i p).bind fun j => g.followFrom j rest

@[blueprint "chap4__definition_4_3_3"]
def follow (g : FiniteGraph) (a : LCS.TreeAddr) : Option Nat :=
  g.followFrom g.root a





theorem followFrom_append (g : FiniteGraph) (i : Nat)
    (a b : LCS.TreeAddr) :
    g.followFrom i (a ++ b) =
      (g.followFrom i a).bind (fun j => g.followFrom j b) := by
  induction a generalizing i with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.cons_append, followFrom]
    cases h : g.next i p <;> simp [ih]

/-- Reachability explores premise IDs and removes repetitions by ID. -/
@[blueprint "chap4__definition_4_3_3"]
def reachableFrom (g : FiniteGraph) : Nat → Nat → List Nat
  | 0, _ => []
  | depth + 1, i =>
    i :: ((match g.next i 0 with
      | none => []
      | some j => g.reachableFrom depth j) ++
      (match g.next i 1 with
      | none => []
      | some j => g.reachableFrom depth j))

@[blueprint "chap4__definition_4_3_3"]
def vertexIds (g : FiniteGraph) : List Nat :=
  (g.reachableFrom g.table.length g.root).eraseDups

@[blueprint "chap4__definition_4_3_3"]
def isInternal (g : FiniteGraph) (i : Nat) : Bool :=
  ((g.node i).bind Node.inference).isSome

@[blueprint "chap4__definition_4_3_3"]
def stepIds (g : FiniteGraph) : List Nat := g.vertexIds.filter g.isInternal

@[blueprint "chap4__definition_4_3_3"]
def leafIds (g : FiniteGraph) : List Nat :=
  g.vertexIds.filter fun i => !g.isInternal i

@[blueprint "chap4__lemma_4_3_3"]
def nodeCount (g : FiniteGraph) : Nat := g.vertexIds.length

@[blueprint "chap4__theorem_4_3_1"]
def stepCount (g : FiniteGraph) : Nat := g.stepIds.length

/-- Resolution validity is required on the represented, reachable graph.
Unused stored rows do not become part of a selected premise subgraph. -/
@[blueprint "chap4__definition_4_3_3"]
def WellFormed (g : FiniteGraph) : Prop :=
  g.root < g.table.length ∧ g.Topological ∧
  ∀ i, i ∈ g.vertexIds → ∀ n, g.node i = some n →
    ∀ r, n.inference = some r →
    ∃ a b, g.node r.left = some a ∧ g.node r.right = some b ∧
      r.pivot ∈ a.clause ∧ r.pivot.conjugate ∈ b.clause ∧
      n.clause = GCNF.Clause.union
        (GCNF.Clause.remove a.clause r.pivot)
        (GCNF.Clause.remove b.clause r.pivot.conjugate)

/-- The stronger invariant used when replaying every row of a table. -/
def AllRowsWellFormed (g : FiniteGraph) : Prop :=
  g.root < g.table.length ∧
  ∀ i n, g.node i = some n → ∀ r, n.inference = some r →
    r.left < i ∧ r.right < i ∧
    ∃ a b, g.node r.left = some a ∧ g.node r.right = some b ∧
      r.pivot ∈ a.clause ∧ r.pivot.conjugate ∈ b.clause ∧
      n.clause = GCNF.Clause.union
        (GCNF.Clause.remove a.clause r.pivot)
        (GCNF.Clause.remove b.clause r.pivot.conjugate)

theorem AllRowsWellFormed.wellFormed {g : FiniteGraph}
    (h : g.AllRowsWellFormed) : g.WellFormed :=
  ⟨h.1, (fun i n hn r hr => ⟨(h.2 i n hn r hr).1, (h.2 i n hn r hr).2.1⟩),
    (fun i _ n hn r hr => (h.2 i n hn r hr).2.2)⟩

@[blueprint "chap4__definition_4_3_3"]
def LeavesFrom (g : FiniteGraph) (S : ClauseSequent) : Prop :=
  ∀ i, i ∈ g.leafIds → ∃ C, g.label i = some C ∧ C ∈ S

@[blueprint "chap4__definition_4_3_3"]
def IsRefutationFor (g : FiniteGraph) (S : ClauseSequent) : Prop :=
  g.WellFormed ∧ g.LeavesFrom S ∧ g.rootLabel = some GCNF.Clause.empty









/-- Change labels while retaining every vertex and successor identity. A caller
must separately establish the resolution equations of the resulting graph. -/
@[blueprint "chap4__definition_4_3_3"]
def mapLabels (g : FiniteGraph) (f : Nat → Clause → Clause) : FiniteGraph :=
  ⟨g.table.zipIdx |>.map (fun (n, i) => { n with clause := f i n.clause }), g.root⟩

/-- Turn one vertex into an input leaf. Its former descendants remain available
to other branches; only root-reachable entries belong to the pruned graph. -/
@[blueprint "chap4__definition_4_3_3"]
def prune (g : FiniteGraph) (i : Nat) : FiniteGraph :=
  ⟨g.table.zipIdx |>.map (fun (n, j) =>
    if i = j then { n with inference := none } else n), g.root⟩

/-- Select a premise subgraph without copying or merging any vertices. -/
@[blueprint "chap4__definition_4_3_3"]
def atRoot (g : FiniteGraph) (i : Nat) : FiniteGraph := { g with root := i }

/-- Replace designated recipient input IDs by the donor root. Donor IDs stay
fixed; other recipient IDs are shifted by the donor table size. The selector
is explicit: equal clause labels alone do not cause identification. -/
@[blueprint "chap4__theorem_4_3_1"]
def graft (donor recipient : FiniteGraph) (replace : Nat → Bool) : FiniteGraph :=
  let redirect := fun i => if replace i then donor.root else donor.table.length + i
  let imported := recipient.table.map fun n =>
    { n with inference := n.inference.map fun r =>
      { r with left := redirect r.left, right := redirect r.right } }
  ⟨donor.table ++ imported, redirect recipient.root⟩

theorem next_spec {g : FiniteGraph} {i p j : Nat} (h : g.next i p = some j) :
    ∃ n r, g.node i = some n ∧ n.inference = some r ∧
      ((p = 0 ∧ j = r.left) ∨ (p = 1 ∧ j = r.right)) := by
  cases hn : g.node i with
  | none => simp [next, hn] at h
  | some n =>
    cases hr : n.inference with
    | none => simp [next, hn, hr] at h
    | some r =>
      refine ⟨n, r, rfl, hr, ?_⟩
      by_cases hp : p = 0
      · simp [next, hn, hr, hp] at h
        exact Or.inl ⟨hp, h.symm⟩
      · by_cases hp1 : p = 1
        · simp [next, hn, hr, hp1] at h
          exact Or.inr ⟨hp1, h.symm⟩
        · simp [next, hn, hp, hp1] at h



theorem next_lt {g : FiniteGraph} (hg : g.WellFormed) {i p j : Nat}
    (h : g.next i p = some j) : j < i := by
  obtain ⟨n, r, hn, hr, hpos⟩ := next_spec h
  have ht := hg.2.1 i n hn r hr
  rcases hpos with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ht.1
  · exact ht.2

theorem next_position_lt {g : FiniteGraph} {i p j : Nat}
    (h : g.next i p = some j) : p < 2 := by
  obtain ⟨_, _, _, _, hpos⟩ := next_spec h
  rcases hpos with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide







theorem followFrom_length_bound {g : FiniteGraph} (hg : g.WellFormed)
    {i j : Nat} {a : LCS.TreeAddr} (h : g.followFrom i a = some j) :
    j + a.length ≤ i := by
  induction a generalizing i with
  | nil => simp [followFrom] at h; subst j; simp
  | cons p a ih =>
    cases hn : g.next i p with
    | none => simp [followFrom, hn] at h
    | some k =>
      have hk := next_lt hg hn
      have hj : g.followFrom k a = some j := by simpa [followFrom, hn] using h
      have hb := ih hj
      simp only [List.length_cons]
      omega

@[blueprint "chap4__definition_4_3_3"]
theorem follow_index_lt {g : FiniteGraph} (hg : g.WellFormed)
    {j : Nat} {a : LCS.TreeAddr} (h : g.follow a = some j) :
    j < g.table.length 



theorem follow_append (g : FiniteGraph) (a b : LCS.TreeAddr) :
    g.follow (a ++ b) = (g.follow a).bind (fun i => g.followFrom i b) :=
  followFrom_append g g.root a b

/-- The unfolding uses exactly the addresses whose successor traversal succeeds. -/
@[blueprint "chap4__definition_4_3_3"]
def domain (g : FiniteGraph) : Set LCS.TreeAddr :=
  fun a => (g.follow a).isSome = true

@[blueprint "chap4__definition_4_3_3"]
theorem domain_prefix_closed (g : FiniteGraph) (a b : LCS.TreeAddr)
    (h : (a ++ b) ∈ g.domain) : a ∈ g.domain 

@[blueprint "chap4__definition_4_3_3"]
theorem child_domain_iff (g : FiniteGraph) (a : LCS.TreeAddr) (p : Nat) :
    (a ++ [p]) ∈ g.domain ↔ p < 2 ∧ (a ++ [0]) ∈ g.domain 

@[blueprint "chap4__definition_4_3_3"]
def treeDomain (g : FiniteGraph) : LCS.TreeDomain where
  dom := g.domain
  root_mem := rfl
  prefix_closed := g.domain_prefix_closed
  left_sibling_closed := by
    intro a i h
    have hi := (g.child_domain_iff a (i + 1)).mp h
    have hi0 : i = 0 := by omega
    simpa [hi0] using hi.2

@[blueprint "chap4__definition_4_3_3"]
theorem domain_finite {g : FiniteGraph} (hg : g.WellFormed) :
    Set.Finite g.domain 

/-- Successful addresses carry the vertex ID. Each invalid address keeps its
own identity, as required by the source's globally defined equivalence relation. -/
@[blueprint "chap4__definition_4_3_3"]
def addressKey (g : FiniteGraph) (a : LCS.TreeAddr) : Nat ⊕ LCS.TreeAddr :=
  match g.follow a with
  | some i => .inl i
  | none => .inr a

@[blueprint "chap4__definition_4_3_3"]
def addressRel (g : FiniteGraph) (a b : LCS.TreeAddr) : Prop :=
  g.addressKey a = g.addressKey b

@[blueprint "chap4__definition_4_3_3"]
theorem addressRel_equiv (g : FiniteGraph) : Equivalence g.addressRel 

@[blueprint "chap4__definition_4_3_3"]
theorem addressRel_follow_eq {g : FiniteGraph} {a b : LCS.TreeAddr}
    (h : g.addressRel a b) : g.follow a = g.follow b 



@[blueprint "chap4__definition_4_3_3"]
theorem addressRel_independent {g : FiniteGraph} (hg : g.WellFormed)
    {a b : LCS.TreeAddr} (h : g.addressRel a b) (hne : a ≠ b) :
    ¬ List.isPrefixOf a b = true ∧ ¬ List.isPrefixOf b a = true 

@[blueprint "chap4__definition_4_3_3"]
def vertexAt (g : FiniteGraph) (a : LCS.TreeAddr) (ha : a ∈ g.domain) : Nat :=
  (g.follow a).get ha

@[blueprint "chap4__definition_4_3_3"]
theorem follow_vertexAt (g : FiniteGraph) (a : LCS.TreeAddr)
    (ha : a ∈ g.domain) : g.follow a = some (g.vertexAt a ha) 



@[blueprint "chap4__definition_4_3_3"]
def labeledTree (g : FiniteGraph) (hg : g.WellFormed) : LCS.LabeledTree Clause where
  domain := g.treeDomain
  label := fun a ha =>
    (g.table[g.vertexAt a ha]'(follow_index_lt hg (g.follow_vertexAt a ha))).clause

theorem node_vertexAt (g : FiniteGraph) (hg : g.WellFormed)
    (a : LCS.TreeAddr) (ha : a ∈ g.domain) :
    g.label (g.vertexAt a ha) = some ((g.labeledTree hg).label a ha) := by
  simp only [label, node, labeledTree,
    List.getElem?_eq_getElem (follow_index_lt hg (g.follow_vertexAt a ha)), Option.map_some]



@[blueprint "chap4__definition_4_3_3"]
theorem labelAtOpt_labeledTree (g : FiniteGraph) (hg : g.WellFormed)
    (a : LCS.TreeAddr) :
    labelAtOpt (g.labeledTree hg) a = (g.follow a).bind g.label 

@[blueprint "chap4__definition_4_3_3"]
theorem addressRel_children {g : FiniteGraph} {a b : LCS.TreeAddr}
    (h : g.addressRel a b) (p : Nat) :
    (a ++ [p]) ∈ g.domain ↔ (b ++ [p]) ∈ g.domain 

@[blueprint "chap4__definition_4_3_3"]
theorem addressRel_childRel {g : FiniteGraph} {a b : LCS.TreeAddr}
    (h : g.addressRel a b) (p : Nat) (ha : (a ++ [p]) ∈ g.domain) :
    g.addressRel (a ++ [p]) (b ++ [p]) 

/-- Unfold paths and identify exactly those paths ending at the same vertex.
Consequently shared vertices remain shared in Gallier's quotient presentation. -/
@[blueprint "chap4__definition_4_3_3"]
def toDAG (g : FiniteGraph) (hg : g.WellFormed) : DAG Clause where
  tree := g.labeledTree hg
  rel := g.addressRel
  rel_equiv := g.addressRel_equiv
  addr_independence := fun _ _ h hne => addressRel_independent hg h hne
  child_preservation := fun _ _ h p => addressRel_children h p
  child_equivalence := fun _ _ h p ha => addressRel_childRel h p ha
  label_agreement := by
    intro a b h
    rw [labelAtOpt_labeledTree, labelAtOpt_labeledTree, addressRel_follow_eq h]


theorem mem_reachableFrom_iff (g : FiniteGraph) (depth i j : Nat) :
    j ∈ g.reachableFrom depth i ↔
      ∃ a, g.followFrom i a = some j ∧ a.length < depth := by
  induction depth generalizing i j with
  | zero => simp [reachableFrom]
  | succ depth ih =>
    constructor
    · intro hj
      simp only [reachableFrom, List.mem_cons, List.mem_append] at hj
      rcases hj with rfl | hleft | hright
      · exact ⟨[], rfl, Nat.zero_lt_succ _⟩
      · cases hn : g.next i 0 with
        | none => simp [hn] at hleft
        | some k =>
          simp only [hn] at hleft
          obtain ⟨a, ha, hlen⟩ := (ih k j).mp hleft
          exact ⟨0 :: a, by simp [followFrom, hn, ha], by simp; omega⟩
      · cases hn : g.next i 1 with
        | none => simp [hn] at hright
        | some k =>
          simp only [hn] at hright
          obtain ⟨a, ha, hlen⟩ := (ih k j).mp hright
          exact ⟨1 :: a, by simp [followFrom, hn, ha], by simp; omega⟩
    · rintro ⟨a, ha, hlen⟩
      simp only [reachableFrom, List.mem_cons, List.mem_append]
      cases a with
      | nil => exact Or.inl (Option.some.inj ha).symm
      | cons p rest =>
        simp only [followFrom] at ha
        cases hn : g.next i p with
        | none => simp [hn] at ha
        | some k =>
          simp only [hn, Option.bind_some] at ha
          have hm : j ∈ g.reachableFrom depth k :=
            (ih k j).mpr ⟨rest, ha, by simp at hlen; omega⟩
          have hp : p = 0 ∨ p = 1 := by
            have := next_position_lt hn
            omega
          rcases hp with rfl | rfl
          · exact Or.inr (Or.inl (by simpa [hn] using hm))
          · exact Or.inr (Or.inr (by simpa [hn] using hm))

theorem mem_vertexIds_iff (g : FiniteGraph) (j : Nat) :
    j ∈ g.vertexIds ↔
      ∃ a, g.follow a = some j ∧ a.length < g.table.length := by
  simp only [vertexIds, List.mem_eraseDups, mem_reachableFrom_iff, follow]





theorem root_mem_vertexIds (g : FiniteGraph) (hwf : g.WellFormed) :
    g.root ∈ g.vertexIds :=
  (mem_vertexIds_iff g g.root).mpr ⟨[], rfl, by have := hwf.1; simp; omega⟩

theorem nodup_eraseDups_nat (l : List Nat) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a rest =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro h
      have hm := List.mem_eraseDups.mp h
      simp only [List.mem_filter, Bool.not_eq_true'] at hm
      simp at hm
    · exact nodup_eraseDups_nat _
termination_by l.length
 decreasing_by simp; have := List.length_filter_le (fun b => !(b == a)) rest; omega









theorem vertexIds_nodup (g : FiniteGraph) : g.vertexIds.Nodup :=
  nodup_eraseDups_nat _

theorem stepIds_nodup (g : FiniteGraph) : g.stepIds.Nodup :=
  (vertexIds_nodup g).filter _

theorem exists_leaf_path (g : FiniteGraph) (hwf : g.WellFormed)
    (i : Nat) (n : Node) (hn : g.node i = some n) :
    ∃ a j, g.followFrom i a = some j ∧ g.isInternal j = false ∧ a.length ≤ i := by
  cases hr : n.inference with
  | none =>
    exact ⟨[], i, rfl, by simp [isInternal, hn, hr], by simp⟩
  | some r =>
    have hl := (hwf.2.1 i n hn r hr).1
    have hi := (List.getElem?_eq_some_iff.mp hn).1
    have hleftbound : r.left < g.table.length := by omega
    have hleft : g.node r.left = some (g.table[r.left]'hleftbound) :=
      List.getElem?_eq_some_iff.mpr ⟨hleftbound, rfl⟩
    obtain ⟨a, j, ha, hj, hlen⟩ := exists_leaf_path g hwf r.left _ hleft
    refine ⟨0 :: a, j, ?_, hj, ?_⟩
    · simp [followFrom, next, hn, hr, ha]
    · simp; omega
termination_by i

















theorem follow_mem_vertexIds {g : FiniteGraph} (hg : g.WellFormed)
    {a : LCS.TreeAddr} {i : Nat} (h : g.follow a = some i) : i ∈ g.vertexIds := by
  apply (mem_vertexIds_iff g i).mpr
  have hb := followFrom_length_bound hg h
  exact ⟨a, h, by have := hg.1; omega⟩

@[blueprint "chap4__definition_4_3_3"]
theorem resolution_labels {g : FiniteGraph} (hg : g.WellFormed)
    (a : LCS.TreeAddr) (ha : a ∈ g.domain)
    (h0 : (a ++ [0]) ∈ g.domain) (h1 : (a ++ [1]) ∈ g.domain) :
    ∃ L, L ∈ (g.labeledTree hg).label (a ++ [0]) h0 ∧
      L.conjugate ∈ (g.labeledTree hg).label (a ++ [1]) h1 ∧
      (g.labeledTree hg).label a ha =
        GCNF.Clause.union
          (GCNF.Clause.remove ((g.labeledTree hg).label (a ++ [0]) h0) L)
          (GCNF.Clause.remove ((g.labeledTree hg).label (a ++ [1]) h1) L.conjugate) 

/-- Every valid finite node table gives the source's resolution DAG, including
its exact binary resolvents and shared quotient nodes. -/
@[blueprint "chap4__definition_4_3_3"]
def toResolutionDAG (g : FiniteGraph) (hg : g.WellFormed) : ResolutionDAG where
  dag := g.toDAG hg
  binary_branching := by
    intro a _ h0
    exact (g.child_domain_iff a 1).mpr ⟨by decide, h0⟩
  children_binary := fun a _ i hi => (g.child_domain_iff a i).mp hi |>.1
  resolvent_at_internal := fun a ha h0 =>
    resolution_labels hg a ha h0 ((g.child_domain_iff a 1).mpr ⟨by decide, h0⟩)
  dom_finite := domain_finite hg
  decidable_dom := fun a => inferInstanceAs (Decidable ((g.follow a).isSome = true))

open LCS.Resolution.GCNF






































































theorem node_index_lt {g : FiniteGraph} {i : Nat} {n : Node}
    (h : g.node i = some n) : i < g.table.length := by
  have := List.getElem?_eq_some_iff.mp h
  exact this.1

theorem vertexIds_index_lt {g : FiniteGraph} (hg : g.WellFormed)
    {i : Nat} (hi : i ∈ g.vertexIds) : i < g.table.length := by
  obtain ⟨a, ha, _⟩ := (mem_vertexIds_iff g i).mp hi
  exact follow_index_lt hg ha

theorem next_mem_vertexIds {g : FiniteGraph} (hg : g.WellFormed)
    {i p j : Nat} (hi : i ∈ g.vertexIds) (hnext : g.next i p = some j) :
    j ∈ g.vertexIds := by
  obtain ⟨a, ha, _⟩ := (mem_vertexIds_iff g i).mp hi
  have hf : g.follow (a ++ [p]) = some j := by
    simp [follow_append, ha, followFrom, hnext]
  have hb := followFrom_length_bound hg hf
  exact (mem_vertexIds_iff g j).mpr ⟨a ++ [p], hf, by have := hg.1; omega⟩

theorem followFrom_closed {g : FiniteGraph} {P : Nat → Prop}
    (hstep : ∀ i p j, P i → g.next i p = some j → P j)
    {i j : Nat} {a : LCS.TreeAddr} (hi : P i) (hpath : g.followFrom i a = some j) :
    P j := by
  induction a generalizing i with
  | nil => simp only [followFrom] at hpath; cases hpath; exact hi
  | cons p rest ih =>
    cases hn : g.next i p with
    | none => simp [followFrom, hn] at hpath
    | some k =>
      exact ih (hstep i p k hi hn) (by simpa [followFrom, hn] using hpath)

/-- Absence of sharing means that a reachable vertex has only one path from
the root. Distinct vertices with equal labels are still distinct. -/
theorem toResolutionDAG_isTreeShaped_iff (g : FiniteGraph) (hg : g.WellFormed) :
    (g.toResolutionDAG hg).isTreeShaped ↔
      ∀ a b i, g.follow a = some i → g.follow b = some i → a = b := by
  constructor
  · intro h a b i ha hb
    apply h a (by show (g.follow a).isSome = true; simp [ha])
      b (by show (g.follow b).isSome = true; simp [hb])
    show g.addressKey a = g.addressKey b
    simp [addressKey, ha, hb]
  · intro h a _ b _ hab
    change g.addressKey a = g.addressKey b at hab
    cases ha : g.follow a with
    | none =>
      cases hb : g.follow b with
      | none => simpa [addressKey, ha, hb] using hab
      | some j => simp [addressKey, ha, hb] at hab
    | some i =>
      cases hb : g.follow b with
      | none => simp [addressKey, ha, hb] at hab
      | some j =>
        have hij : i = j := by simpa [addressKey, ha, hb] using hab
        subst j
        exact h a b i ha hb

end FiniteGraph
end LCS.Resolution.Method
