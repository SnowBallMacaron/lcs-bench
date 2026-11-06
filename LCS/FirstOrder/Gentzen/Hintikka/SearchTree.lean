import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.HintikkaSets
import LCS.FirstOrder.Gentzen.Hintikka.Branching

/-! # The search tree and its paths (Section 5.4.7)

The search state, the search tree built from closure and branching steps, the
signed set of a path, path monotonicity, and the conversion of a finite tree
into a proof tree (Theorem 5.4.1 (i)).
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): SearchState
record from the pre-refactor pipeline, used only by Thm 5.5.1's
abstract-existence scaffolding (`goedelExtendedCompletenessG`) and
its downstream Thm 5.6.1 callers. Uses `SignedFormula`-keyed usage
records and a finite `availVars : Nat → Nat` stream — neither is
textbook-faithful; the faithful Def 5.4.9 state lives in
`LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState` with `FormulaN`
keys and an implicit countably-infinite `availNext : Nat` stream.
Remove together with the unfaithful Thm 5.5.1 main and its
scaffolding chain. -/
structure SearchState (L : Language) where
  /-- TERM0 list: pairs of activated terms and their usage records -/
  termRecords : List (Term L × List (SignedFormula L))
  /-- AVAIL0 stream: maps indices to fresh variable numbers -/
  availVars : Nat → Nat
  /-- Current index into the AVAIL0 stream -/
  availIdx : Nat

namespace SearchState

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Initialize
the legacy SearchState record. Doesn't collect constants (only FV),
uses `Term.var 0` as y₀ without checking freshness, and produces a
truncated `availVars` stream keyed by `startIdx`. Faithful counterpart
is `SearchState.init` in `LCS.FirstOrder.Gentzen.Search.NoFunction`.
Used only by unfaithful Thm 5.5.1 scaffolding. -/
def init {L : Language} (seq : Sequent L) : SearchState L :=
  -- Collect variable terms from free variables in all formulae
  let fvIndices := (seq.antecedent ++ seq.succedent).flatMap formulaFreeVarIndices
  let fvTerms := fvIndices.eraseDups.map Term.var
  -- If no terms found, use a single fresh variable y0
  let initialTerms : List (Term L) :=
    if fvTerms.isEmpty then [Term.var 0] else fvTerms
  let records := initialTerms.map (fun t => (t, ([] : List (SignedFormula L))))
  -- AVAIL0 starts at a fresh variable index beyond all used variables
  let startIdx := initialTerms.length
  { termRecords := records
  , availVars := fun n => startIdx + n
  , availIdx := 0 }

/-- Definition 5.5.1 (normalized companion): A sequent is a finished
leaf with respect to a (Hintikka-layer) search state `st` iff it is
an axiom, OR every antecedent formula A is atomic or has been used
with every term in TERM0 (witnessed by `SignedFormula.trueF A`
appearing in the usage list for every record), AND symmetrically for
succedent formulae B via `SignedFormula.falseF B`.

This is the normalized-pipeline parallel of
`LCS.FirstOrder.Completeness.SearchState.isFinishedLeaf` (which is
defined over the compatibility `Completeness.SearchState`). The
textbook "finished leaf" definition (Def 5.5.1) is the same; the
two layers only differ on how the usage records are keyed (SignedFormula
here vs FormulaN there). -/
def isFinishedLeaf {L : Language} (st : SearchState L)
    (seq : Sequent L) : Prop :=
  isAxiom seq ∨
  ((∀ A ∈ seq.antecedent,
    A.isAtomic ∨
    (∀ rec ∈ st.termRecords, SignedFormula.trueF A ∈ rec.2)) ∧
   (∀ B ∈ seq.succedent,
    B.isAtomic ∨
    (∀ rec ∈ st.termRecords, SignedFormula.falseF B ∈ rec.2)))

end SearchState

-- ===================================================================
-- SearchTreeData: Normalized search tree data structure
-- ===================================================================

/-- Theorem 5.5.1 (companion, normalized): A search tree data structure over
FormulaN/Sequent, containing the tree domain, node sequents, node
states, and structural invariants. The path Hintikka properties
(H0-H6) and finite-valid-to-proof conversion are stated as separate
sorry'd theorems below, following the textbook's separation of the
search tree construction from its properties. -/
structure SearchTreeData (L : Language) [Countable (Term L)] (seq : Sequent L) where
  /-- The tree domain of the search tree -/
  treeDom : LCS.TreeDomain
  /-- The sequent at each tree address -/
  nodeSequent : (addr : TreeAddr) → addr ∈ treeDom.dom → Sequent L
  /-- The search state at each tree address -/
  nodeState : (addr : TreeAddr) → addr ∈ treeDom.dom → SearchState L
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
  /-- The input sequent has no free-bound variable overlap -/
  input_noFreeBound : noFreeBound seq
  /-- The input sequent has cross-formula free/bound disjointness
      (textbook section 5.4.7 assumption). -/
  input_crossNoFreeBound : crossNoFreeBound seq
  /-- The input sequent has no eq_ formulas -/
  input_seqNoEq : seqNoEq seq
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
  /-- Non-axiom nodes have no eq_ formulas. (Axiom leaf nodes may
      contain eq_ sentinels, but they are never on infinite paths.) -/
  node_seqNoEq : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    ¬ isAxiom (nodeSequent u hu) → seqNoEq (nodeSequent u hu)
  /-- The base for fresh variable generation -/
  freshBase : Nat
  /-- freshBase is large enough to avoid all bound variables in seq -/
  freshBase_bound : ∀ v, ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∈ formulaBVN A → v < freshBase
  /-- Path expansion: along any infinite path f, the nodeSequent at depth
      n+1 equals branchStep applied to the nodeSequent at depth n. -/
  path_expansion : ∀ (f : Nat → Nat) (n : Nat)
    (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ treeDom.dom),
    nodeSequent (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1)) =
    branchStep (nodeSequent (List.ofFn (fun i : Fin n => f i)) (hPath n)) n freshBase (f n) seq
  /-- Provability extraction from finite tree: if the search tree domain
      is finite then the input sequent is G-provable under the §5.4.8
      standing assumption. Populated by buildSearchTree: axiom case gives
      direct proof, provable case delegates, not-provable case derives
      contradiction (the tree is actually infinite, so IsFinite yields
      False). -/
  provable_if_finite : treeDom.IsFinite → sequentProvableExt seq

-- ===================================================================
-- SearchTreeData.pathSignedSet: helper for path signed set
-- ===================================================================

/-- Theorem 5.4.1 (normalized, helper): The signed formula set along
a path f : Nat -> Nat in a SearchTreeData. Collects all signed
formulae from the antecedent (as trueF) and succedent (as falseF) of
every sequent along the path. This avoids repeating the `let S := ...`
definition in every path property theorem. -/
def SearchTreeData.pathSignedSet {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq) (f : Nat → Nat)
    (_hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    Set (SignedFormula L) := fun sf =>
  ∃ n : Nat, ∃ (h : (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom),
    let seq_n := w.nodeSequent (List.ofFn (fun i : Fin n => f i)) h
    (∃ A ∈ seq_n.antecedent, sf = SignedFormula.trueF A) ∨
    (∃ B ∈ seq_n.succedent, sf = SignedFormula.falseF B)

end LCS.FirstOrder.Gentzen.Hintikka
end
