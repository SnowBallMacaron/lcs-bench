import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.DAGs.ProofsStamp

/-! # Resolution DAGs (Section 4.3.1)

Directed acyclic graphs as labelled trees with an equivalence on addresses
(Definition 4.3.1), with Examples 4.3.1 and 4.3.2.
-/
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

end DAG

/-- Example 4.3.1 (companion def): Valid tree addresses for the example tree,
    a 9-address domain encoding an f-h-f-f-f-b-b-b-b tree. -/
@[blueprint "chap4__example_4_3_1"]
def exDAGTreeAddrs : Set TreeAddr :=
  fun a => a ∈ ([[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]] : List TreeAddr)

/-- Example 4.3.1 (companion): The root address `[]` is in `exDAGTreeAddrs`. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_root_mem : [] ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion): `exDAGTreeAddrs` is closed under prefixes. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_prefix_closed :
    ∀ u v, (u ++ v) ∈ exDAGTreeAddrs → u ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion): `exDAGTreeAddrs` is closed under
    left-siblings. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_left_sibling_closed :
    ∀ u i, (u ++ [i + 1]) ∈ exDAGTreeAddrs → (u ++ [i]) ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion def): Tree domain with closure properties. -/
@[blueprint "chap4__example_4_3_1"]
def exDAGTreeDomain : TreeDomain where
  dom := exDAGTreeAddrs
  root_mem := exDAGTreeDomain_root_mem
  prefix_closed := exDAGTreeDomain_prefix_closed
  left_sibling_closed := exDAGTreeDomain_left_sibling_closed

/-- Example 4.3.1 (companion def): Labeling function for the example tree. -/
@[blueprint "chap4__example_4_3_1"]
noncomputable def exDAGTreeLabel (a : TreeAddr) (_ : a ∈ exDAGTreeDomain.dom) : Char :=
  match a with
  | []        => 'f'
  | [0]       => 'h'
  | [1]       => 'f'
  | [1, 0]    => 'f'
  | [1, 1]    => 'f'
  | [1, 0, 0] => 'b'
  | [1, 0, 1] => 'b'
  | [1, 1, 0] => 'b'
  | [1, 1, 1] => 'b'
  | _         => 'x'  -- unreachable for valid addresses

/-- Example 4.3.1: A concrete labeled tree over Char illustrating shared
    subtrees: root 'f', left leaf 'h', right subtree f(f(b,b), f(b,b)). -/
@[blueprint "chap4__example_4_3_1" (main := true)]
noncomputable def exDAGTree : LabeledTree Char where
  domain := exDAGTreeDomain
  label := exDAGTreeLabel

/-- Example 4.3.2 (companion def): List of valid tree addresses. -/
@[blueprint "chap4__example_4_3_2"]
def exDAGAddrs : List TreeAddr :=
  [[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]]

/-- Example 4.3.2 (companion theorem): Membership in the tree domain unfolds to
    list membership. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_dom_iff (a : TreeAddr) :
    a ∈ exDAGTree.domain.dom ↔ a ∈ exDAGAddrs 

/-- Example 4.3.2 (companion theorem): [1,0] is in the tree domain. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_10 : [1,0] ∈ exDAGTree.domain.dom 

/-- Example 4.3.2 (companion theorem): [1,1] is in the tree domain. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_11 : [1,1] ∈ exDAGTree.domain.dom 

-- ========= Example 4.3.2: Collapsed DAG =========

/-- Example 4.3.2 (companion): Equivalence relation identifying the two
    shared subtrees of `exDAGTree`. -/
@[blueprint "chap4__example_4_3_2"]
def exCollapsedDAG_rel : TreeAddr → TreeAddr → Prop :=
  fun u v => u = v ∨
    ((u = [1,0] ∧ v = [1,1]) ∨ (u = [1,1] ∧ v = [1,0])) ∨
    (u ∈ [[1,0,0], [1,0,1], [1,1,0], [1,1,1]] ∧
     v ∈ [[1,0,0], [1,0,1], [1,1,0], [1,1,1]])

/-- Example 4.3.2 (companion): `exCollapsedDAG_rel` is an equivalence
    relation. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_rel_equiv : Equivalence exCollapsedDAG_rel 

/-- Example 4.3.2 (companion): Address independence for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_addr_independence :
    ∀ u v, exCollapsedDAG_rel u v → u ≠ v →
      ¬ List.isPrefixOf u v = true ∧ ¬ List.isPrefixOf v u = true 

/-- Example 4.3.2 (companion): Child preservation for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_child_preservation :
    ∀ u v, exCollapsedDAG_rel u v → ∀ i,
      (u ++ [i]) ∈ exDAGTree.domain.dom ↔
      (v ++ [i]) ∈ exDAGTree.domain.dom 

/-- Example 4.3.2 (companion): Child equivalence for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_child_equivalence :
    ∀ u v, exCollapsedDAG_rel u v → ∀ i,
      (u ++ [i]) ∈ exDAGTree.domain.dom →
      exCollapsedDAG_rel (u ++ [i]) (v ++ [i]) 

/-- Example 4.3.2 (companion): Label agreement for `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_label_agreement :
    ∀ u v, exCollapsedDAG_rel u v →
      labelAtOpt exDAGTree u = labelAtOpt exDAGTree v 

/-- Example 4.3.2: DAG obtained by collapsing shared subtrees in exDAGTree,
    identifying the two f(b,b) subtrees and all four b leaves. -/
@[blueprint "chap4__example_4_3_2" (main := true)]
noncomputable def exCollapsedDAG : DAG Char where
  tree := exDAGTree
  rel := exCollapsedDAG_rel
  rel_equiv := exCollapsedDAG_rel_equiv
  addr_independence := exCollapsedDAG_addr_independence
  child_preservation := exCollapsedDAG_child_preservation
  child_equivalence := exCollapsedDAG_child_equivalence
  label_agreement := exCollapsedDAG_label_agreement

end LCS.Resolution.Method
end
