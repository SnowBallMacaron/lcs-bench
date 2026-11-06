import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.KonigLemma.ProofsStamp

/-! # König's lemma (Section 3.5.3, Lemma 3.5.1)

Tree domains, infinite paths, and König's lemma: a finite-branching tree
with infinite domain has an infinite path.
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

-- ========= Lemma 3.5.1: TreeDomain for Konig's Lemma =========

/-- Lemma 3.5.1 (required): An abstract tree domain for stating Konig's
    lemma. A TreeDomain consists of a type of nodes, a root node, a
    children relation, a predicate asserting that every node has finitely
    many children (finite branching), and that the set of all nodes is
    infinite. -/
@[blueprint "chap3__lemma_3_5_1"]
structure TreeDomain where
  Node : Type
  root : Node
  children : Node → Node → Prop
  isNode : Set Node
  rootIsNode : isNode root
  childrenAreNodes : ∀ p c, isNode p → children p c → isNode c
  finiteBranching : ∀ p, isNode p →
    Set.Finite (fun c => children p c)

namespace TreeDomain

/-- Lemma 3.5.1 (companion): An infinite path in a tree domain is a
    function Nat -> Node such that the first node is the root and each
    successive node is a child of the previous one. -/
@[blueprint "chap3__lemma_3_5_1"]
def InfinitePath (T : TreeDomain) (path : Nat → T.Node) : Prop :=
  path 0 = T.root ∧
  ∀ n, T.children (path n) (path (n + 1))

end TreeDomain
end LCS.Propositional.Infinite
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

-- ========= Lemma 3.5.1 (infrastructure): Reachable =========

/-- Lemma 3.5.1 (required helper): Reflexive transitive closure of the
    children relation. -/
@[blueprint "chap3__lemma_3_5_1"]
inductive Reachable (T : TreeDomain) : T.Node → T.Node → Prop where
  | refl : ∀ n, Reachable T n n
  | step : ∀ p c d, T.children p c → Reachable T c d → Reachable T p d

namespace TreeDomain

/-- The set of descendants of a node p: nodes reachable from p that are in isNode -/
def descendants (T : TreeDomain) (p : T.Node) : Set T.Node :=
  fun n => T.isNode n ∧ Reachable T p n

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If p is a node and c is reachable from p, then c is a node -/
theorem reachable_isNode (T : TreeDomain) (p c : T.Node)
    (hp : T.isNode p) (hr : Reachable T p c) : T.isNode c := by
-- BEGIN PROOF
  induction hr with
  | refl => exact hp
  | step p' c' d' hch _hrc ih =>
    exact ih (T.childrenAreNodes p' c' hp hch)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Pigeonhole for tree: if p has infinite descendants, some child of p
    has infinite descendants -/
theorem exists_child_infinite_desc (T : TreeDomain) (p : T.Node)
    (hp : T.isNode p)
    (hinf : ¬ Set.Finite (T.descendants p))
    (h_allReach : ∀ n, T.descendants p n → n = p ∨ ∃ c, T.children p c ∧ Reachable T c n) :
    ∃ c, T.children p c ∧ ¬ Set.Finite (T.descendants c) := by
-- BEGIN PROOF
  -- The descendants of p (minus p itself) are covered by descendants of children
  -- First, get the finite list of children
  obtain ⟨cl, hcl⟩ := T.finiteBranching p hp
  -- We show: descendants(p) minus {p} is covered by descendants of children in cl
  -- If descendants(p) were finite, done. We know it's not.
  -- We need: removing one element (p) from an infinite set is still infinite
  have hremove : ¬ Set.Finite (fun n => T.descendants p n ∧ n ≠ p) := by
    intro hfin
    apply hinf
    -- descendants(p) ⊆ {p} ∪ (descendants(p) \ {p})
    -- {p} is finite (singleton), and descendants(p) \ {p} is finite by hfin
    have hsingleton : Set.Finite (fun n : T.Node => n = p) :=
      ⟨[p], fun a => ⟨fun h => by simp [h], fun h => by simp at h; exact h⟩⟩
    have hunion := Set.Finite.union hsingleton hfin
    apply Set.Finite.subset hunion
    intro n hn
    simp only [Set.union]
    classical
    exact if heq : n = p then Or.inl heq else Or.inr ⟨hn, heq⟩
  -- Now apply pigeonhole: the non-root descendants are covered by children's descendants
  have hcover : ∀ n, (fun n => T.descendants p n ∧ n ≠ p) n →
      ∃ c ∈ cl, T.descendants c n := by
    intro n ⟨hdesc, hne⟩
    obtain ⟨hnode, hreach⟩ := hdesc
    rcases h_allReach n ⟨hnode, hreach⟩ with rfl | ⟨c, hch, hrc⟩
    · exact absurd rfl hne
    · exact ⟨c, (hcl c).mp hch, T.reachable_isNode c n (T.childrenAreNodes p c hp hch) hrc, hrc⟩
  obtain ⟨c, hcmem, hcinf⟩ :=
    Set.pigeonhole_list (fun n => T.descendants p n ∧ n ≠ p) cl
      (fun c => T.descendants c) hremove hcover
  exact ⟨c, (hcl c).mpr hcmem, hcinf⟩

end TreeDomain

/-- Lemma 3.5.1 (Konig's lemma): If T is a finitely-branching tree
    (every node has finitely many children) and T has infinitely many
    nodes (the node set is not finite), and every node is reachable
    from the root, then T contains an infinite path starting from the
    root. The proof constructs the path by recursion on Nat: at each
    step, select (by Classical.choose) a child with infinitely many
    descendants, which exists by the pigeonhole principle. -/
@[blueprint "chap3__lemma_3_5_1" (main := true)]
theorem konig_lemma (T : TreeDomain)
    (h_infinite : ¬ Set.Finite T.isNode)
    (h_allReachable : ∀ n, T.isNode n → Reachable T T.root n)
    (h_tree : ∀ p n, T.isNode n → Reachable T p n →
      n = p ∨ ∃ c, T.children p c ∧ Reachable T c n) :
    ∃ path : Nat → T.Node, T.InfinitePath path 

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Concatenate two paths in the same tree domain. -/
theorem Reachable.trans {T : TreeDomain} {a b c : T.Node}
    (hab : Reachable T a b) (hbc : Reachable T b c) : Reachable T a c := by
  induction hab with
  | refl => exact hbc
  | step p q r hp hqr ih => exact .step p q c hp (ih hbc)

end LCS.Propositional.Infinite
end
