import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.DAGs
import LCS.Resolution.Method.Resolvents
import LCS.Resolution.Method.ResolutionDAGs.ProofsStamp

/-! # Resolution DAGs and refutations (Definition 4.3.3)

Resolution DAGs, their axiom and resolution constructors, leaves, refutations,
step and node counts, forests of resolution DAGs, and tree-shaped resolution
proofs.
-/
section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

-- ========= Definition 4.3.3: Resolution DAGs =========

/-- Definition 4.3.3: A resolution DAG: a DAG whose labels are clauses,
    with binary branching and internal nodes labeled by resolvents. -/
@[blueprint "chap4__definition_4_3_3"]
structure ResolutionDAG where
  /-- The underlying DAG with clause labels -/
  dag : DAG Clause
  /-- Binary branching: if a node has a left child, it also has a right child -/
  binary_branching :
    ∀ (u : TreeAddr) (_hu : u ∈ dag.tree.domain.dom),
      (u ++ [0]) ∈ dag.tree.domain.dom →
      (u ++ [1]) ∈ dag.tree.domain.dom
  /-- No third or later successor: every internal node has exactly two children. -/
  children_binary :
    ∀ (u : TreeAddr) (_hu : u ∈ dag.tree.domain.dom) (i : Nat),
      (u ++ [i]) ∈ dag.tree.domain.dom → i < 2
  /-- Resolution constraint: each internal node's label is the resolvent
      of its two children's labels via some pivot literal. -/
  resolvent_at_internal :
    ∀ (u : TreeAddr) (hu : u ∈ dag.tree.domain.dom)
      (h0 : (u ++ [0]) ∈ dag.tree.domain.dom),
      let h1 := binary_branching u hu h0
      ∃ L : Literal,
        L ∈ dag.tree.label (u ++ [0]) h0 ∧
        Literal.conjugate L ∈ dag.tree.label (u ++ [1]) h1 ∧
        dag.tree.label u hu =
          GCNF.Clause.union
            (GCNF.Clause.remove (dag.tree.label (u ++ [0]) h0) L)
            (GCNF.Clause.remove (dag.tree.label (u ++ [1]) h1)
              (Literal.conjugate L))
  /-- Finite derivation reading of Definition 4.3.3. The generic `DAG`
      remains unrestricted, as in Definition 4.3.1. -/
  dom_finite : Set.Finite dag.tree.domain.dom
  /-- Domain membership is decidable for resolution DAGs -/
  decidable_dom : DecidablePred (· ∈ dag.tree.domain.dom)

attribute [blueprint "chap4__definition_4_3_3"] ResolutionDAG.dom_finite

namespace ResolutionDAG

/-- Definition 4.3.3 (companion def): The label at the root of the resolution
    DAG, obtained from the underlying labeled tree at address []. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def rootLabel (D : ResolutionDAG) : Clause :=
  D.dag.tree.label [] D.dag.tree.domain.root_mem

/-- Definition 4.3.3 (companion def): A node (equivalence class) in the
    resolution DAG is a leaf if its representative has no children. -/
@[blueprint "chap4__definition_4_3_3"]
def isLeafNode (D : ResolutionDAG) (S : Set TreeAddr) : Prop :=
  ∃ u, u ∈ D.dag.tree.domain.dom ∧ S = D.dag.eqClass u ∧
    ¬ ((u ++ [0]) ∈ D.dag.tree.domain.dom)

/-- Definition 4.3.3 (companion def): A node (equivalence class) in the
    resolution DAG is internal if its representative has children. -/
@[blueprint "chap4__definition_4_3_3"]
def isInternalNode (D : ResolutionDAG) (S : Set TreeAddr) : Prop :=
  ∃ u, u ∈ D.dag.tree.domain.dom ∧ S = D.dag.eqClass u ∧
    (u ++ [0]) ∈ D.dag.tree.domain.dom

/-- Definition 4.3.3 (companion def): All leaf labels in the resolution DAG
    are from the clause set S. -/
@[blueprint "chap4__definition_4_3_3"]
def leavesFrom (D : ResolutionDAG) (S : ClauseSequent) : Prop :=
  ∀ u, (hu : u ∈ D.dag.tree.domain.dom) →
    ¬ ((u ++ [0]) ∈ D.dag.tree.domain.dom) →
    (D.dag.tree.label u hu) ∈ S

/-- Definition 4.3.3 (companion def): A resolution DAG is a refutation for S
    if its leaves are from S and the root label is the empty clause. -/
@[blueprint "chap4__definition_4_3_3"]
def isRefutationFor (D : ResolutionDAG) (S : ClauseSequent) : Prop :=
  D.leavesFrom S ∧ D.rootLabel = GCNF.Clause.empty

/-- Definition 4.3.3 (companion def): A resolution DAG is tree-shaped if its
    equivalence relation is the identity (no sharing of subproofs). -/
@[blueprint "chap4__definition_4_3_3"]
def isTreeShaped (D : ResolutionDAG) : Prop :=
  ∀ u, u ∈ D.dag.tree.domain.dom →
    ∀ v, v ∈ D.dag.tree.domain.dom → D.dag.rel u v → u = v

/-- Definition 4.3.3 (companion): Prefix closure for the singleton `{[]}`
    domain used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_prefix_closed :
    ∀ u v, (u ++ v) ∈ (fun a : TreeAddr => a = []) →
      u ∈ (fun a : TreeAddr => a = []) 

/-- Definition 4.3.3 (companion): Left-sibling closure for the singleton
    `{[]}` domain used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_left_sibling_closed :
    ∀ u i, (u ++ [i + 1]) ∈ (fun a : TreeAddr => a = []) →
      (u ++ [i]) ∈ (fun a : TreeAddr => a = []) 

/-- Definition 4.3.3 (companion): Address independence for the identity
    equivalence used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_addr_independence :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → u ≠ v →
      ¬ List.isPrefixOf u v = true ∧ ¬ List.isPrefixOf v u = true 

/-- Definition 4.3.3 (companion): Child preservation for the identity
    equivalence used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_child_preservation
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom ↔ (v ++ [i]) ∈ tree.domain.dom 

/-- Definition 4.3.3 (companion): Child equivalence for the identity
    equivalence used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_child_equivalence
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom →
      (fun u v : TreeAddr => u = v) (u ++ [i]) (v ++ [i]) 

/-- Definition 4.3.3 (companion): Label agreement for the identity
    equivalence used by `mk_axiom`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_label_agreement
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v →
      labelAtOpt tree u = labelAtOpt tree v 

/-- Definition 4.3.3 (companion): Binary branching for the `mk_axiom`
    resolution DAG — there are no internal nodes so the hypothesis is
    vacuous. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_binary_branching
    (dag : DAG Clause)
    (hdom : ∀ a, a ∈ dag.tree.domain.dom ↔ a = []) :
    ∀ (u : TreeAddr) (_hu : u ∈ dag.tree.domain.dom),
      (u ++ [0]) ∈ dag.tree.domain.dom →
      (u ++ [1]) ∈ dag.tree.domain.dom 

/-- Definition 4.3.3 (companion): Resolvent constraint for `mk_axiom` —
    there are no internal nodes so the hypothesis is vacuous. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_axiom_resolvent_at_internal
    (dag : DAG Clause)
    (hdom : ∀ a, a ∈ dag.tree.domain.dom ↔ a = [])
    (binary_branching :
      ∀ (u : TreeAddr) (_hu : u ∈ dag.tree.domain.dom),
        (u ++ [0]) ∈ dag.tree.domain.dom →
        (u ++ [1]) ∈ dag.tree.domain.dom) :
    ∀ (u : TreeAddr) (hu : u ∈ dag.tree.domain.dom)
      (h0 : (u ++ [0]) ∈ dag.tree.domain.dom),
      let h1 := binary_branching u hu h0
      ∃ L : Literal,
        L ∈ dag.tree.label (u ++ [0]) h0 ∧
        Literal.conjugate L ∈ dag.tree.label (u ++ [1]) h1 ∧
        dag.tree.label u hu =
          GCNF.Clause.union
            (GCNF.Clause.remove (dag.tree.label (u ++ [0]) h0) L)
            (GCNF.Clause.remove (dag.tree.label (u ++ [1]) h1)
              (Literal.conjugate L)) 

/-- Definition 4.3.3 (companion def): Leaf DAG from a single clause (axiom):
    one node labeled C with identity equivalence. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def mk_axiom (C : Clause) : ResolutionDAG where
  dag := {
    tree := {
      domain := {
        dom := fun a => a = []
        root_mem := rfl
        prefix_closed := mk_axiom_prefix_closed
        left_sibling_closed := mk_axiom_left_sibling_closed
      }
      label := fun _a _ha => C
    }
    rel := fun u v => u = v
    rel_equiv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
    addr_independence := mk_axiom_addr_independence
    child_preservation := mk_axiom_child_preservation _
    child_equivalence := mk_axiom_child_equivalence _
    label_agreement := mk_axiom_label_agreement _
  }
  children_binary := by
    intro u hu i hi
    have : u ++ [i] = [] := hi
    simp at this
  binary_branching := mk_axiom_binary_branching _ (fun _ => Iff.rfl)
  resolvent_at_internal :=
    mk_axiom_resolvent_at_internal _ (fun _ => Iff.rfl) _
  dom_finite := ⟨[[]], fun a => by
    constructor
    · intro (h : a = []); rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
    · intro h; rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact absurd h List.not_mem_nil⟩
  decidable_dom := fun a => if h : a = [] then isTrue h else isFalse h

/-- Definition 4.3.3 (companion): The underlying domain predicate for the
    tree of `mk_resolve D1 D2 L`. -/
@[blueprint "chap4__definition_4_3_3"]
def mk_resolve_dom (D1 D2 : ResolutionDAG) : TreeAddr → Prop :=
  fun a =>
    a = [] ∨
    (∃ t, a = 0 :: t ∧ t ∈ D1.dag.tree.domain.dom) ∨
    (∃ t, a = 1 :: t ∧ t ∈ D2.dag.tree.domain.dom)

/-- Definition 4.3.3 (companion): Prefix closure for the `mk_resolve`
    domain. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_prefix_closed (D1 D2 : ResolutionDAG) :
    ∀ u v, (u ++ v) ∈ mk_resolve_dom D1 D2 → u ∈ mk_resolve_dom D1 D2 

/-- Definition 4.3.3 (companion): Left-sibling closure for the
    `mk_resolve` domain. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_left_sibling_closed (D1 D2 : ResolutionDAG) :
    ∀ u i, (u ++ [i + 1]) ∈ mk_resolve_dom D1 D2 →
      (u ++ [i]) ∈ mk_resolve_dom D1 D2 

/-- Definition 4.3.3 (companion): Tree domain for `mk_resolve D1 D2 L`. -/
@[blueprint "chap4__definition_4_3_3"]
def mk_resolve_domain (D1 D2 : ResolutionDAG) : TreeDomain where
  dom := mk_resolve_dom D1 D2
  root_mem := Or.inl rfl
  prefix_closed := mk_resolve_prefix_closed D1 D2
  left_sibling_closed := mk_resolve_left_sibling_closed D1 D2

/-- Definition 4.3.3 (companion): The labeling function for the tree
    underlying `mk_resolve D1 D2 L`. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def mk_resolve_label (D1 D2 : ResolutionDAG) (L : Literal)
    (a : TreeAddr) (ha : a ∈ (mk_resolve_domain D1 D2).dom) : Clause := by
  classical
  exact if a = [] then
    GCNF.Clause.union (GCNF.Clause.remove D1.rootLabel L)
      (GCNF.Clause.remove D2.rootLabel (Literal.conjugate L))
  else
    match a with
    | 0 :: t =>
      have ht : t ∈ D1.dag.tree.domain.dom := by
        rcases ha with h | ⟨t', ht_eq, ht_mem⟩ | ⟨t', ht_eq, ht_mem⟩
        · exact absurd h (List.cons_ne_nil 0 t)
        · have := List.cons.inj ht_eq; exact this.2 ▸ ht_mem
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
      D1.dag.tree.label t ht
    | 1 :: t =>
      have ht : t ∈ D2.dag.tree.domain.dom := by
        rcases ha with h | ⟨t', ht_eq, ht_mem⟩ | ⟨t', ht_eq, ht_mem⟩
        · exact absurd h (List.cons_ne_nil 1 t)
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
        · have := List.cons.inj ht_eq; exact this.2 ▸ ht_mem
      D2.dag.tree.label t ht
    | _ =>
      -- This case is unreachable for valid addresses
      GCNF.Clause.empty

/-- Definition 4.3.3 (companion): Labeled tree for `mk_resolve D1 D2 L`. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def mk_resolve_tree
    (D1 D2 : ResolutionDAG) (L : Literal) : LabeledTree Clause where
  domain := mk_resolve_domain D1 D2
  label := mk_resolve_label D1 D2 L

/-- Definition 4.3.3 (companion): Address independence for the identity
    equivalence used by `mk_resolve`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_addr_independence :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → u ≠ v →
      ¬ List.isPrefixOf u v = true ∧ ¬ List.isPrefixOf v u = true 

/-- Definition 4.3.3 (companion): Child preservation for the identity
    equivalence used by `mk_resolve`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_child_preservation
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom ↔ (v ++ [i]) ∈ tree.domain.dom 

/-- Definition 4.3.3 (companion): Child equivalence for the identity
    equivalence used by `mk_resolve`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_child_equivalence
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom →
      (fun u v : TreeAddr => u = v) (u ++ [i]) (v ++ [i]) 

/-- Definition 4.3.3 (companion): Label agreement for the identity
    equivalence used by `mk_resolve`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_label_agreement
    (tree : LabeledTree Clause) :
    ∀ u v, (fun u v : TreeAddr => u = v) u v →
      labelAtOpt tree u = labelAtOpt tree v 

/-- Definition 4.3.3 (companion): The DAG underlying `mk_resolve D1 D2 L`. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def mk_resolve_dag
    (D1 D2 : ResolutionDAG) (L : Literal) : DAG Clause where
  tree := mk_resolve_tree D1 D2 L
  rel := fun u v => u = v
  rel_equiv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  addr_independence := mk_resolve_addr_independence
  child_preservation := mk_resolve_child_preservation _
  child_equivalence := mk_resolve_child_equivalence _
  label_agreement := mk_resolve_label_agreement _

/-- Definition 4.3.3 (companion): Binary branching for the
    `mk_resolve D1 D2 L` resolution DAG. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_binary_branching (D1 D2 : ResolutionDAG) (L : Literal) :
    ∀ (u : TreeAddr) (_hu : u ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom),
      (u ++ [0]) ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom →
      (u ++ [1]) ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom 

/-- Both component trees and the new root have at most two successors. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_children_binary (D1 D2 : ResolutionDAG) (L : Literal) :
    ∀ (u : TreeAddr) (_hu : u ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom)
      (i : Nat), (u ++ [i]) ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom → i < 2 

/-- Definition 4.3.3 (companion): Resolvent constraint for `mk_resolve`. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_resolvent_at_internal
    (D1 D2 : ResolutionDAG) (L : Literal)
    (hL : L ∈ D1.rootLabel) (hLc : Literal.conjugate L ∈ D2.rootLabel) :
    ∀ (u : TreeAddr) (hu : u ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom)
      (h0 : (u ++ [0]) ∈ (mk_resolve_dag D1 D2 L).tree.domain.dom),
      let h1 := mk_resolve_binary_branching D1 D2 L u hu h0
      ∃ L' : Literal,
        L' ∈ (mk_resolve_dag D1 D2 L).tree.label (u ++ [0]) h0 ∧
        Literal.conjugate L' ∈ (mk_resolve_dag D1 D2 L).tree.label (u ++ [1]) h1 ∧
        (mk_resolve_dag D1 D2 L).tree.label u hu =
          GCNF.Clause.union
            (GCNF.Clause.remove
              ((mk_resolve_dag D1 D2 L).tree.label (u ++ [0]) h0) L')
            (GCNF.Clause.remove
              ((mk_resolve_dag D1 D2 L).tree.label (u ++ [1]) h1)
              (Literal.conjugate L')) 

/-- Definition 4.3.3 (companion): Finiteness of the `mk_resolve` domain. -/
@[blueprint "chap4__definition_4_3_3"]
theorem mk_resolve_dom_finite (D1 D2 : ResolutionDAG) (L : Literal) :
    Set.Finite (mk_resolve_dag D1 D2 L).tree.domain.dom 

/-- Definition 4.3.3 (companion def): Build a resolve DAG from two sub-DAGs
    by resolving on pivot L, tree-shaped. -/
@[blueprint "chap4__definition_4_3_3"]
noncomputable def mk_resolve (D1 D2 : ResolutionDAG) (L : Literal)
    (hL : L ∈ D1.rootLabel) (hLc : Literal.conjugate L ∈ D2.rootLabel) : ResolutionDAG where
  dag := mk_resolve_dag D1 D2 L
  binary_branching := mk_resolve_binary_branching D1 D2 L
  children_binary := mk_resolve_children_binary D1 D2 L
  resolvent_at_internal := mk_resolve_resolvent_at_internal D1 D2 L hL hLc
  dom_finite := mk_resolve_dom_finite D1 D2 L
  decidable_dom := fun a =>
    match a with
    | [] => isTrue (Or.inl rfl)
    | 0 :: t =>
      match D1.decidable_dom t with
      | isTrue h => isTrue (Or.inr (Or.inl ⟨t, rfl, h⟩))
      | isFalse h => isFalse (by
          intro habs
          rcases habs with heq | ⟨t', ht_eq, ht_mem⟩ | ⟨t', ht_eq, _⟩
          · exact absurd heq (List.cons_ne_nil 0 t)
          · exact h ((List.cons.inj ht_eq).2 ▸ ht_mem)
          · exact absurd (List.cons.inj ht_eq).1 (by omega))
    | 1 :: t =>
      match D2.decidable_dom t with
      | isTrue h => isTrue (Or.inr (Or.inr ⟨t, rfl, h⟩))
      | isFalse h => isFalse (by
          intro habs
          rcases habs with heq | ⟨t', ht_eq, _⟩ | ⟨t', ht_eq, ht_mem⟩
          · exact absurd heq (List.cons_ne_nil 1 t)
          · exact absurd (List.cons.inj ht_eq).1 (by omega)
          · exact h ((List.cons.inj ht_eq).2 ▸ ht_mem))
    | (n + 2) :: _ => isFalse (by
        intro habs
        rcases habs with heq | ⟨t', ht_eq, _⟩ | ⟨t', ht_eq, _⟩
        · exact absurd heq (List.cons_ne_nil _ _)
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
        · exact absurd (List.cons.inj ht_eq).1 (by omega))

/-- The root label of mk_resolve is the resolvent. -/
theorem rootLabel_resolve (D1 D2 : ResolutionDAG) (L : Literal)
    (hL : L ∈ D1.rootLabel) (hLc : Literal.conjugate L ∈ D2.rootLabel) :
    (mk_resolve D1 D2 L hL hLc).rootLabel =
      GCNF.Clause.union (GCNF.Clause.remove D1.rootLabel L)
        (GCNF.Clause.remove D2.rootLabel (Literal.conjugate L)) := by
-- BEGIN PROOF
  unfold rootLabel mk_resolve
  show (mk_resolve_dag D1 D2 L).tree.label [] _ = _
  unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
  simp [rootLabel]

/-- The leaves of mk_axiom C come from S iff S C. -/
theorem leavesFrom_axiom (C : Clause) (S : ClauseSequent) :
    (mk_axiom C).leavesFrom S ↔ C ∈ S := by
-- BEGIN PROOF
  unfold leavesFrom mk_axiom
  simp only
  constructor
  · -- Forward: if all leaves are from S, then C ∈ S
    intro h
    -- The only address in the domain is [], apply h to []
    have := h [] rfl (by show ¬([0] = []); simp)
    exact this
  · -- Backward: if C ∈ S, then for all u in domain (i.e., u = []), leaf → label u ∈ S
    intro hSC u (hu : u = []) _hleaf
    subst hu
    exact hSC

/-- Definition 4.3.3 (companion def): A resolution DAG is a resolution refutation
    for S iff its leaves are from S and its root is labeled with ∅. -/
@[blueprint "chap4__definition_4_3_3"]
def isResolutionRefutation (D : ResolutionDAG) (S : ClauseSequent) : Prop :=
  D.isRefutationFor S

/-- Theorem 4.3.1 (companion def): The number of resolution steps in a DAG,
    i.e., the number of equivalence classes of internal addresses. -/
@[blueprint "chap4__theorem_4_3_1"]
noncomputable def stepCount (D : ResolutionDAG) : Nat :=
  open Classical in
  let setoid : Setoid TreeAddr := ⟨D.dag.rel, D.dag.rel_equiv⟩
  let internalAddrs := D.dom_finite.choose.filter fun u =>
    match D.decidable_dom u, D.decidable_dom (u ++ [0]) with
    | isTrue _, isTrue _ => true
    | _, _ => false
  letI : DecidableEq (Quotient setoid) := fun _ _ => Classical.propDecidable _
  (internalAddrs.map (Quotient.mk setoid)).eraseDups.length

/-- Number of distinct quotient vertices, including shared leaves only once. -/
@[blueprint "chap4__lemma_4_3_3"]
noncomputable def nodeCount (D : ResolutionDAG) : Nat :=
  let setoid : Setoid TreeAddr := ⟨D.dag.rel, D.dag.rel_equiv⟩
  letI : DecidableEq (Quotient setoid) := fun _ _ => Classical.propDecidable _
  (D.dom_finite.choose.map (Quotient.mk setoid)).eraseDups.length

/-- Equality of textbook constituents: the labeled tree and the relation on
    its domain agree. Values of the global relation outside that domain are
    representation data and do not distinguish two source DAGs. -/
@[blueprint "chap4__definition_4_3_3"]
def sourceEquivalent (D E : ResolutionDAG) : Prop :=
  D.dag.tree = E.dag.tree ∧
    ∀ u v, u ∈ D.dag.tree.domain.dom → v ∈ D.dag.tree.domain.dom →
      (D.dag.rel u v ↔ E.dag.rel u v)

@[blueprint "chap4__definition_4_3_3"]
def sourceSetoid : Setoid ResolutionDAG where
  r := sourceEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro D; exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩
    · intro D E h
      refine ⟨h.1.symm, ?_⟩
      intro u v hu hv
      exact (h.2 u v (h.1.symm ▸ hu) (h.1.symm ▸ hv)).symm
    · intro D E F hDE hEF
      refine ⟨hDE.1.trans hEF.1, ?_⟩
      intro u v hu hv
      exact (hDE.2 u v hu hv).trans (hEF.2 u v (hDE.1 ▸ hu) (hDE.1 ▸ hv))

@[blueprint "chap4__definition_4_3_3"]
def sourceClass (D : ResolutionDAG) : Quotient sourceSetoid :=
  Quotient.mk sourceSetoid D

end ResolutionDAG

/-- Definition 4.3.3: a resolution DAG for S is a finite set of distinct
    constituent DAGs whose leaves belong to S. Constituents here use the finite
    derivation reading supported by the resolution method and soundness proof. -/
@[blueprint "chap4__definition_4_3_3" (main := true)]
structure ResolutionForest (S : ClauseSequent) where
  members : Set (Quotient ResolutionDAG.sourceSetoid)
  finite : Set.Finite members
  leavesFrom : ∀ D : ResolutionDAG, D.sourceClass ∈ members → D.leavesFrom S

namespace ResolutionForest

/-- A refutation consists of exactly one DAG, with empty root label. -/
@[blueprint "chap4__definition_4_3_3"]
def isRefutation {S : ClauseSequent} (F : ResolutionForest S) : Prop :=
  ∃ D : ResolutionDAG, F.members = (fun E => E = D.sourceClass) ∧ D.rootLabel = GCNF.Clause.empty

end ResolutionForest

/-- Theorem 4.3.1 (companion — tree type): Inductive resolution tree used
    as an algorithmic vehicle in the proof of Theorem 4.3.1. -/
@[blueprint "chap4__theorem_4_3_3"]
inductive ResolutionTree where
  | axiom_ : Clause → ResolutionTree
  | resolve : ResolutionTree → ResolutionTree → Literal → ResolutionTree

namespace ResolutionTree
open LCS.Resolution.GCNF

/-- Theorem 4.3.1 (companion — tree label): Root label of the resolution
    tree. -/
@[blueprint "chap4__theorem_4_3_3"]
def label : ResolutionTree → Clause
  | .axiom_ C => C
  | .resolve T1 T2 L =>
    GCNF.Clause.union
      (GCNF.Clause.remove T1.label L)
      (GCNF.Clause.remove T2.label (Literal.conjugate L))

/-- Theorem 4.3.1 (companion — tree leaf condition): All leaf labels
    of the resolution tree are members of S. -/
@[blueprint "chap4__theorem_4_3_3"]
def leavesFrom (T : ResolutionTree) (S : ClauseSequent) : Prop :=
  match T with
  | .axiom_ C => C ∈ S
  | .resolve T1 T2 _ => T1.leavesFrom S ∧ T2.leavesFrom S

/-- A structural certificate that every internal tree node performs a genuine
    resolution step: the pivot occurs in the left premise and its conjugate
    occurs in the right premise.  `ResolutionTree.label` already computes the
    corresponding resolvent, so these occurrence witnesses rule out malformed
    nodes whose labels merely erase absent literals. -/
@[blueprint "chap4__theorem_4_3_3"]
def IsWellFormed : ResolutionTree → Prop
  | .axiom_ _ => True
  | .resolve T1 T2 pivot =>
    T1.IsWellFormed ∧
    T2.IsWellFormed ∧
    pivot ∈ T1.label ∧
    Literal.conjugate pivot ∈ T2.label

/-- Number of resolve nodes (resolution steps). -/
@[blueprint "chap4__theorem_4_3_3"]
def treeStepCount : ResolutionTree → Nat
  | .axiom_ _ => 0
  | .resolve T1 T2 _ => 1 + T1.treeStepCount + T2.treeStepCount

/-- A well-formed resolution tree yields a finite resolution DAG, together
    with its exact root label. -/
noncomputable def toResolutionDAGWithLabel : (T : ResolutionTree) →
    T.IsWellFormed → {D : ResolutionDAG // D.rootLabel = T.label}
  | .axiom_ C, _ => ⟨ResolutionDAG.mk_axiom C, rfl⟩
  | .resolve T1 T2 L, h =>
    let D1 := toResolutionDAGWithLabel T1 h.1
    let D2 := toResolutionDAGWithLabel T2 h.2.1
    ⟨ResolutionDAG.mk_resolve D1.val D2.val L
      (D1.property.symm ▸ h.2.2.1) (D2.property.symm ▸ h.2.2.2), by
      rw [ResolutionDAG.rootLabel_resolve, D1.property, D2.property]
      rfl⟩

/-- Tree-to-DAG conversion requires a genuine pivot at every internal node. -/
noncomputable def toResolutionDAG (T : ResolutionTree) (h : T.IsWellFormed) : ResolutionDAG :=
  (T.toResolutionDAGWithLabel h).val

end ResolutionTree
end LCS.Resolution.Method
end
