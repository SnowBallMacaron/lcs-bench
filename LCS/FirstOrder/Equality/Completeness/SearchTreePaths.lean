import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Equality.Completeness.SearchRounds

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch
open LCS.FirstOrder.Completeness

-- ===================================================================
-- Definition 5.6.3 (normalized): SearchTreeDataEq
-- ===================================================================

/-- Structural data for the legacy equality search: a finitely branching tree,
its node sequents and states, and their local expansion invariants. -/
structure SearchTreeDataEq (L : Language) (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) where
  /-- The tree domain of the search tree -/
  treeDom : LCS.TreeDomain
  /-- The sequent at each tree address -/
  nodeSequent : (addr : TreeAddr) → addr ∈ treeDom.dom → Sequent L
  /-- The equality search state at each tree address -/
  nodeStateEq : (addr : TreeAddr) → addr ∈ treeDom.dom → SearchStateEq L
  /-- Root has the input sequent -/
  root_sequent : nodeSequent [] treeDom.root_mem = seq
  /-- Axiom nodes are leaves: if the sequent at u is an axiom, then
      u has no children in the search tree -/
  axiom_is_leaf : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    isAxiom (nodeSequent u hu) →
    ¬ ((u ++ [0]) ∈ treeDom.dom)
  /-- The tree is finitely branching -/
  finBranching : treeDom.FinitelyBranching
  /-- Non-axiom nodes have at least one child -/
  non_axiom_has_child : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    ¬ isAxiom (nodeSequent u hu) →
    (u ++ [0]) ∈ treeDom.dom
  /-- Antecedent monotonicity along paths: parent antecedent ⊆ child antecedent -/
  path_ant_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (A : FormulaN L),
    A ∈ (nodeSequent u hu).antecedent →
    A ∈ (nodeSequent (u ++ [i]) hc).antecedent
  /-- Succedent monotonicity along paths: parent succedent ⊆ child succedent -/
  path_succ_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (B : FormulaN L),
    B ∈ (nodeSequent u hu).succedent →
    B ∈ (nodeSequent (u ++ [i]) hc).succedent
  /-- The base for fresh variable generation -/
  freshBase : Nat
  /-- freshBase is large enough to avoid all bound variables in seq -/
  freshBase_bound : ∀ v, ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∈ formulaBVN A → v < freshBase
  /-- Path expansion with equality injection: along any infinite path f,
      the nodeSequent at depth n+1 equals branchStepEqN applied to the
      nodeSequent at depth n with appropriate equality state. -/
  path_expansion : ∀ (f : Nat → Nat) (n : Nat)
    (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ treeDom.dom),
    nodeSequent (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1)) =
    branchStepEqN (nodeSequent (List.ofFn (fun i : Fin n => f i)) (hPath n))
      n freshBase (f n) (nodeStateEq (List.ofFn (fun i : Fin n => f i)) (hPath n)) seq

end LCS.FirstOrder.Equality.Completeness
end
