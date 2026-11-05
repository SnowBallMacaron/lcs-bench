import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.Part1.ProofsStamp
attach_helper_namespace LCS.Resolution.Method.Proofs

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

/-- Example 4.3.2 (companion def): Optional label lookup for a LabeledTree. -/
@[blueprint "chap4__example_4_3_2"]
noncomputable def labelAtOpt (t : LabeledTree Delta)
    (addr : TreeAddr) : Option Delta :=
  open Classical in
  if h : addr ∈ t.domain.dom then some (t.label addr h) else none

/-- Example 4.3.2 (companion theorem): If the address is in the domain,
    labelAtOpt returns its label. -/
@[blueprint "chap4__example_4_3_2"]
theorem labelAtOpt_of_mem (t : LabeledTree Delta) (addr : TreeAddr)
    (h : addr ∈ t.domain.dom) :
    labelAtOpt t addr = some (t.label addr h) 

/-- Definition 4.3.1: A directed acyclic graph (DAG) is a pair (t, R), where
    t is a tree labeled with symbols from some alphabet Δ, and R is an
    equivalence relation on dom(t) satisfying: for any pair u, v ∈ dom(t),
    if (u, v) ∈ R, then either u = v or u and v are independent and, for all
    i > 0, (1) ui ∈ dom(t) iff vi ∈ dom(t); (2) if ui ∈ dom(t), then
    (ui, vi) ∈ R; (3) t(u) = t(v). The tree t is the underlying tree; the
    equivalence classes modulo R are the nodes of the DAG.

    Textbook Def 4.3.1 (docs/context/chap4/sec3/4_3_1_Resolution_DAGs.md).
    Examples 4.3.1 and 4.3.2 precede this definition as informal
    illustrations. -/
@[blueprint "chap4__definition_4_3_1" (main := true)]
structure DAG (Delta : Type) : Type 1 where
  /-- The underlying labeled tree -/
  tree : LabeledTree Delta
  /-- The equivalence relation on tree addresses -/
  rel : TreeAddr → TreeAddr → Prop
  /-- rel is an equivalence relation -/
  rel_equiv : Equivalence rel
  /-- Address independence: equivalent distinct addresses are independent
      (neither is a prefix of the other) -/
  addr_independence :
    ∀ u v, rel u v → u ≠ v → ¬ List.isPrefixOf u v = true ∧
                                ¬ List.isPrefixOf v u = true
  /-- Child preservation: for equivalent addresses u, v and any child
      index i, u ++ [i] is in the domain iff v ++ [i] is -/
  child_preservation :
    ∀ u v, rel u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom ↔ (v ++ [i]) ∈ tree.domain.dom
  /-- Child equivalence: for equivalent addresses u, v and any child
      index i, if u ++ [i] is in the domain then the children are
      also equivalent -/
  child_equivalence :
    ∀ u v, rel u v → ∀ i,
      (u ++ [i]) ∈ tree.domain.dom → rel (u ++ [i]) (v ++ [i])
  /-- Label agreement: equivalent addresses have the same label -/
  label_agreement :
    ∀ u v, rel u v → labelAtOpt tree u = labelAtOpt tree v

attribute [blueprint "chap4__definition_4_3_1"] DAG.rel_equiv

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

/-- Definition 4.3.1 (companion def): The equivalence class of a tree address
    u modulo the relation rel. -/
@[blueprint "chap4__definition_4_3_1"]
def eqClass (d : DAG Delta) (u : TreeAddr) : Set TreeAddr :=
  fun v => d.rel u v

/-- Definition 4.3.1 (companion def): The nodes of the DAG are the equivalence
    classes of tree addresses modulo the relation rel. -/
@[blueprint "chap4__definition_4_3_1"]
def nodes (d : DAG Delta) : Set (Set TreeAddr) :=
  fun S => ∃ u, u ∈ d.tree.domain.dom ∧ S = d.eqClass u

/-- Definition 4.3.1 (companion def): An edge from class [u] to class [ui]
    where ui = u ++ [i] is in the domain. -/
@[blueprint "chap4__definition_4_3_1"]
def edges (d : DAG Delta) : Set (Set TreeAddr × Set TreeAddr) :=
  fun ⟨S, T⟩ => ∃ u i, u ∈ d.tree.domain.dom ∧ (u ++ [i]) ∈ d.tree.domain.dom ∧
    S = d.eqClass u ∧ T = d.eqClass (u ++ [i])

/-- Definition 4.3.1 (companion): The root of the DAG is the equivalence
    class of the empty address []. -/
@[blueprint "chap4__definition_4_3_1"]
def root (d : DAG Delta) : Set TreeAddr :=
  d.eqClass []

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG
variable {Delta : Type}

/-- Representatives must actually be tree addresses. -/
@[blueprint "chap4__definition_4_3_1"]
def isDescendant (d : DAG Delta) (S T : Set TreeAddr) : Prop :=
  ∃ u v, u ∈ d.tree.domain.dom ∧ v ∈ d.tree.domain.dom ∧
    S = d.eqClass u ∧ T = d.eqClass v ∧ List.isPrefixOf v u = true

/-- A finite directed path in the quotient graph, including its length. -/
@[blueprint "chap4__definition_4_3_1"]
inductive DirectedPath (d : DAG Delta) : Set TreeAddr → Set TreeAddr → Nat → Prop where
  | nil {S} : S ∈ d.nodes → DirectedPath d S S 0
  | cons {S T U n} : (S, T) ∈ d.edges → DirectedPath d T U n →
      DirectedPath d S U (n + 1)

@[blueprint "chap4__definition_4_3_1"]
def pathBetween (d : DAG Delta) (S T : Set TreeAddr) : Prop :=
  ∃ n, DirectedPath d S T n

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem rel_of_eqClass_eq (d : DAG Delta) {u v : TreeAddr}
    (h : d.eqClass u = d.eqClass v) : d.rel u v := by
  have hv : v ∈ d.eqClass v := d.rel_equiv.refl v
  rw [← h] at hv
  exact hv

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem eqClass_eq_of_rel (d : DAG Delta) {u v : TreeAddr}
    (h : d.rel u v) : d.eqClass u = d.eqClass v := by
  funext w
  apply propext
  exact ⟨fun h' => d.rel_equiv.trans (d.rel_equiv.symm h) h',
    fun h' => d.rel_equiv.trans h h'⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem eqClass_eq_iff_rel (d : DAG Delta) (u v : TreeAddr) :
    d.eqClass u = d.eqClass v ↔ d.rel u v :=
  ⟨rel_of_eqClass_eq d, eqClass_eq_of_rel d⟩

















/-- An ancestor is a node from which the given descendant is reachable. -/
@[blueprint "chap4__definition_4_3_1"]
def isAncestor (d : DAG Delta) (S T : Set TreeAddr) : Prop :=
  d.isDescendant T S

/-- An infinite path inherited from the underlying tree, as in Chapter 2.
    The quotient images below are the corresponding DAG vertices. -/
@[blueprint "chap4__definition_4_3_1"]
structure InfinitePath (d : DAG Delta) where
  address : Nat → TreeAddr
  inDomain : ∀ n, address n ∈ d.tree.domain.dom
  successor : Nat → Nat
  next : ∀ n, address (n + 1) = address n ++ [successor n]

@[blueprint "chap4__definition_4_3_1"]
def InfinitePath.node {d : DAG Delta} (p : InfinitePath d) (n : Nat) : Set TreeAddr :=
  d.eqClass (p.address n)

@[blueprint "chap4__definition_4_3_1"]
theorem InfinitePath.successiveEdges {d : DAG Delta} (p : InfinitePath d) (n : Nat) :
    (p.node n, p.node (n + 1)) ∈ d.edges 

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace Clause

/-- Definition 4.3.2 (companion def): The conjugate of a literal, re-exported
    in the resolution namespace. -/
@[blueprint "chap4__definition_4_3_2"]
def conjugate : Literal → Literal :=
  Literal.conjugate

/-- Definition 4.3.2 (companion def): Remove all occurrences of a literal
    from a clause. -/
@[blueprint "chap4__definition_4_3_2"]
def remove (C : Clause) (L : Literal) : Clause :=
  GCNF.Clause.remove C L

/-- Definition 4.3.2: A clause C is a resolvent of C1 and C2 iff for some
    literal L in C1 with conjugate in C2, C = (C1 \ {L}) ∪ (C2 \ {~L}). -/
@[blueprint "chap4__definition_4_3_2" (main := true)]
def isResolvent (C C1 C2 : Clause) : Prop :=
  ∃ L : Literal, L ∈ C1 ∧ (Literal.conjugate L) ∈ C2 ∧
    C = GCNF.Clause.union (Clause.remove C1 L) (Clause.remove C2 (Literal.conjugate L))

end Clause
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
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



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The leaves of mk_resolve come from S iff both sub-DAGs' leaves do. -/
theorem leavesFrom_resolve (D1 D2 : ResolutionDAG) (L : Literal)
    (hL : L ∈ D1.rootLabel) (hLc : Literal.conjugate L ∈ D2.rootLabel) (S : ClauseSequent) :
    (mk_resolve D1 D2 L hL hLc).leavesFrom S ↔ D1.leavesFrom S ∧ D2.leavesFrom S := by
-- BEGIN PROOF
  -- Helper: the label at 0 :: t in mk_resolve equals D1's label at t
  have label_left : ∀ (t : TreeAddr) (ht : t ∈ D1.dag.tree.domain.dom)
      (h_in : (0 :: t) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom),
      (mk_resolve D1 D2 L hL hLc).dag.tree.label (0 :: t) h_in = D1.dag.tree.label t ht := by
    intro t ht h_in
    show (mk_resolve_dag D1 D2 L).tree.label (0 :: t) h_in = _
    unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
    simp [show (0 :: t ≠ []) from List.cons_ne_nil _ _]
    rfl
  -- Helper: the label at 1 :: t in mk_resolve equals D2's label at t
  have label_right : ∀ (t : TreeAddr) (ht : t ∈ D2.dag.tree.domain.dom)
      (h_in : (1 :: t) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom),
      (mk_resolve D1 D2 L hL hLc).dag.tree.label (1 :: t) h_in = D2.dag.tree.label t ht := by
    intro t ht h_in
    show (mk_resolve_dag D1 D2 L).tree.label (1 :: t) h_in = _
    unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
    simp [show (1 :: t ≠ []) from List.cons_ne_nil _ _]
    rfl
  constructor
  · -- Forward
    intro h
    constructor
    · -- D1.leavesFrom S
      intro u hu hleaf
      have h_in : (0 :: u) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom :=
        Or.inr (Or.inl ⟨u, rfl, hu⟩)
      have h_not_child : ¬((0 :: u) ++ [0]) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom := by
        simp only [List.cons_append]
        intro habs
        rcases habs with h1 | ⟨t, ht_eq, ht_mem⟩ | ⟨t, ht_eq, _⟩
        · exact absurd h1 (List.cons_ne_nil _ _)
        · have := (List.cons.inj ht_eq).2; subst this; exact hleaf ht_mem
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
      rw [← label_left u hu h_in]
      exact h (0 :: u) h_in h_not_child
    · -- D2.leavesFrom S
      intro u hu hleaf
      have h_in : (1 :: u) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom :=
        Or.inr (Or.inr ⟨u, rfl, hu⟩)
      have h_not_child : ¬((1 :: u) ++ [0]) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom := by
        simp only [List.cons_append]
        intro habs
        rcases habs with h1 | ⟨t, ht_eq, _⟩ | ⟨t, ht_eq, ht_mem⟩
        · exact absurd h1 (List.cons_ne_nil _ _)
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
        · have := (List.cons.inj ht_eq).2; subst this; exact hleaf ht_mem
      rw [← label_right u hu h_in]
      exact h (1 :: u) h_in h_not_child
  · -- Backward
    intro ⟨hD1, hD2⟩ u hu hleaf
    rcases hu with rfl | ⟨t, rfl, ht_mem⟩ | ⟨t, rfl, ht_mem⟩
    · -- u = [], root is not a leaf
      exfalso; apply hleaf
      exact Or.inr (Or.inl ⟨[], rfl, D1.dag.tree.domain.root_mem⟩)
    · -- u = 0 :: t, t ∈ D1.dom
      have h_in : (0 :: t) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom :=
        Or.inr (Or.inl ⟨t, rfl, ht_mem⟩)
      have hleaf_D1 : ¬(t ++ [0]) ∈ D1.dag.tree.domain.dom := by
        intro h_child; apply hleaf
        simp only [List.cons_append]
        exact Or.inr (Or.inl ⟨t ++ [0], rfl, h_child⟩)
      rw [label_left t ht_mem h_in]
      exact hD1 t ht_mem hleaf_D1
    · -- u = 1 :: t, t ∈ D2.dom
      have h_in : (1 :: t) ∈ (mk_resolve D1 D2 L hL hLc).dag.tree.domain.dom :=
        Or.inr (Or.inr ⟨t, rfl, ht_mem⟩)
      have hleaf_D2 : ¬(t ++ [0]) ∈ D2.dag.tree.domain.dom := by
        intro h_child; apply hleaf
        simp only [List.cons_append]
        exact Or.inr (Or.inr ⟨t ++ [0], rfl, h_child⟩)
      rw [label_right t ht_mem h_in]
      exact hD2 t ht_mem hleaf_D2




/-- Definition 4.3.3 (companion def): A resolution DAG D is a resolution DAG
    for a set S of clauses if the underlying DAG has nonempty domain and
    every leaf label is from S. -/
@[blueprint "chap4__definition_4_3_3"]
def isResolutionDAGFor (D : ResolutionDAG) (S : ClauseSequent) : Prop :=
  D.leavesFrom S

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

-- ATTACH-BLOCKER: private declaration
private theorem eraseDupsNodup {α : Type} [DecidableEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    match xs, hn with
    | [], _ => simp
    | x :: tl, hlen =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hx
        rw [List.mem_eraseDups, List.mem_filter] at hx
        simp at hx
      · apply ih _ _ _ rfl
        have := List.length_filter_le (fun b => !b == x) tl
        simp at hlen
        omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem quotientCount_eq_of_representatives {α : Type} (r : Setoid α)
    [DecidableEq (Quotient r)] (xs reps : List α)
    (hrep : ∀ v ∈ reps, v ∈ xs)
    (hnodup : (reps.map (Quotient.mk r)).Nodup)
    (hcover : ∀ u ∈ xs, ∃ v ∈ reps, r.r u v) :
    (xs.map (Quotient.mk r)).eraseDups.length = reps.length := by
  have hp := LCS.list_perm_of_nodup_of_mem_iff
    (eraseDupsNodup (xs.map (Quotient.mk r))) hnodup ?_
  · simpa using hp.length_eq
  intro q
  rw [List.mem_eraseDups]
  constructor
  · intro hx
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, huv⟩ := hcover u hu
    exact List.mem_map.mpr ⟨v, hv, (Quotient.sound huv).symm.trans heq⟩
  · intro hx
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨v, hrep v hv, heq⟩



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem stepCount_eq_of_representatives (D : ResolutionDAG) (reps : List TreeAddr)
    (hrep : ∀ u ∈ reps, u ∈ D.dag.tree.domain.dom ∧
      u ++ [0] ∈ D.dag.tree.domain.dom)
    (hnodup : (reps.map (Quotient.mk ⟨D.dag.rel, D.dag.rel_equiv⟩)).Nodup)
    (hcover : ∀ u, u ∈ D.dag.tree.domain.dom →
      u ++ [0] ∈ D.dag.tree.domain.dom → ∃ v ∈ reps, D.dag.rel u v) :
    D.stepCount = reps.length := by
  classical
  unfold LCS.Resolution.Method.ResolutionDAG.stepCount
  dsimp only
  apply @quotientCount_eq_of_representatives TreeAddr ⟨D.dag.rel, D.dag.rel_equiv⟩
    (fun _ _ => Classical.propDecidable _)
  · intro v hv
    obtain ⟨hvd, hvchild⟩ := hrep v hv
    apply List.mem_filter.mpr
    refine ⟨(D.dom_finite.choose_spec v).mp hvd, ?_⟩
    cases hd : D.decidable_dom v with
    | isFalse hf => exact False.elim (hf hvd)
    | isTrue ht =>
      cases hc : D.decidable_dom (v ++ [0]) with
      | isFalse hf => exact False.elim (hf hvchild)
      | isTrue ht => rfl
  · exact hnodup
  · intro u hu
    obtain ⟨humem, hfilter⟩ := List.mem_filter.mp hu
    have hud : u ∈ D.dag.tree.domain.dom := (D.dom_finite.choose_spec u).mpr humem
    apply hcover u hud
    cases hd : D.decidable_dom u with
    | isFalse hf => exact False.elim (hf hud)
    | isTrue ht =>
      cases hc : D.decidable_dom (u ++ [0]) with
      | isFalse hf => simp [hd, hc] at hfilter
      | isTrue ht => exact ht


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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem leavesFrom_sourceEquivalent {D E : ResolutionDAG}
    (h : D.sourceEquivalent E) (S : ClauseSequent) :
    D.leavesFrom S ↔ E.leavesFrom S := by
  unfold leavesFrom
  rw [h.1]

end ResolutionDAG
end LCS.Resolution.Method
end

