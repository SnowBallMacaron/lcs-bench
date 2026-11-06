import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.SearchTrees
import LCS.Propositional.Infinite.KonigLemma
import LCS.Propositional.Infinite.Search.ProofsStamp

/-! # The search procedure for infinite sequents (Definition 3.5.1)

The procedures search and expand with the global sequences L and R,
finished and closed leaves, the limit tree, and the statement pieces of
Theorem 3.5.1 (halting, closed trees, an infinite path when search does
not halt).
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- The global remaining sequences and a finite stage with a fixed root. -/
@[blueprint "chap3__definition_3_5_1"]
structure InfSearchState where
  L : Nat → Option PropFormulaNormalized
  R : Nat → Option PropFormulaNormalized
  L_noHoles : NoHoles L
  R_noHoles : NoHoles R
  rootSeq : Sequent
  tree : InfDeductionTree rootSeq

attribute [blueprint "chap3__definition_3_5_1"]
  InfSearchState.L_noHoles InfSearchState.R_noHoles

open LCS.Propositional.Systems.G.Search

/-- Definition 3.5.1 (companion): Initializes the search state from an
    infinite sequent. The tree is the one-node tree labeled with
    head(Gamma_0) -> head(Delta_0), L = tail(Gamma_0),
    R = tail(Delta_0). -/
@[blueprint "chap3__definition_3_5_1"]
def infSearchInit (seq : InfSequent) : InfSearchState :=
  let headAnt := match InfSeq.head seq.antecedent with
    | some A => [A]
    | none => []
  let headSuc := match InfSeq.head seq.succedent with
    | some B => [B]
    | none => []
  { L := InfSeq.tail seq.antecedent
    R := InfSeq.tail seq.succedent
    rootSeq := Sequent.mk headAnt headSuc
    L_noHoles := fun n => seq.antecedent_noHoles (n + 1)
    R_noHoles := fun n => seq.succedent_noHoles (n + 1)
    tree := InfDeductionTree.leaf (Sequent.mk headAnt headSuc) }

-- ========= Definition 3.5.1 (companion): Finished Leaf =========

/-- Definition 3.5.1 (companion): A leaf is finished in the infinite
    search if it is an axiom (closed leaf) OR (L and R are both empty
    at all remaining positions AND all propositions in the leaf's
    antecedent and succedent are atomic). -/
@[blueprint "chap3__definition_3_5_1"]
def infIsFinishedLeaf (state : InfSearchState) (s : Sequent) : Prop :=
  isAxiom s ∨
  ((∀ n, state.L n = none) ∧ (∀ n, state.R n = none) ∧
   (∀ A ∈ s.antecedent ++ s.succedent, isAtomicFormula A))

/-- Definition 3.5.1 (companion): All leaves of the tree in an `InfSearchState`
    are finished in the infinite-search sense (axiom OR L=R=empty AND all-atomic).
    This is the textbook-faithful halt predicate of the search procedure. -/

@[blueprint "chap3__definition_3_5_1"]
def infIsFinishedTree (state : InfSearchState) : Prop :=
  ∀ s ∈ state.tree.leaves, infIsFinishedLeaf state s

/-- Decidable axiom test. -/
@[blueprint "chap3__definition_3_4_4"]
def isAxiomBool (s : Sequent) : Bool :=
  s.antecedent.any (fun A => s.succedent.any (fun B => A == B))

/-- Exact executable finished-leaf check, including both remaining sequences. -/
@[blueprint "chap3__definition_3_5_1"]
def infIsFinishedLeafBool (state : InfSearchState) (s : Sequent) : Bool :=
  isAxiomBool s ||
    (state.L 0 == none && state.R 0 == none &&
      (s.antecedent ++ s.succedent).all isAtomicBool)

/-- Exact executable while-loop guard. -/
def infIsFinishedTreeBool (state : InfSearchState) : Bool :=
  state.tree.leaves.all (infIsFinishedLeafBool state)

/-- Add one child to each open leaf; closed leaves and all old labels remain. -/
@[blueprint "chap3__definition_3_5_1"]
def appendToLeavesCore {s : Sequent} (t : InfDeductionTree s)
    (newAnt newSuc : Option PropFormulaNormalized) : InfDeductionTree s :=
  t.bindLeaves fun leaf =>
    if isAxiomBool leaf then .leaf leaf
    else .extend newAnt newSuc (.leaf (extendSeq leaf newAnt newSuc))

/-- A round visits exactly the old leaves. It decomposes the snapshot of
both sides of each unfinished label, then introduces the current heads at
its open descendants. The two global sequences advance once per round. -/
@[blueprint "chap3__definition_3_5_1"]
def infExpand (state : InfSearchState) : InfSearchState :=
  { L := InfSeq.tail state.L
    R := InfSeq.tail state.R
    L_noHoles := fun n => state.L_noHoles (n + 1)
    R_noHoles := fun n => state.R_noHoles (n + 1)
    rootSeq := state.rootSeq
    tree := state.tree.bindLeaves fun s =>
      if infIsFinishedLeafBool state s then .leaf s
      else appendToLeavesCore
        (InfDeductionTree.ofDeductionTree (searchRound .systematic (.leaf s)))
        (InfSeq.head state.L) (InfSeq.head state.R) }

/-- Definition 3.5.1: Search with the exact infinite-sequent stopping condition.
The total finite-stage sequence `infSearchSteps` below also represents runs
that never halt. -/
@[blueprint "chap3__definition_3_5_1" (main := true)]
partial def infSearch (seq : InfSequent) : InfSearchState :=
  infSearchLoop (infSearchInit seq)
where
  infSearchLoop (state : InfSearchState) : InfSearchState :=
    if infIsFinishedTreeBool state then state
    else infSearchLoop (infExpand state)

-- ========= Theorem 3.5.1: Main Statement (faithful, proof deferred) =========

/-- Theorem 3.5.1 (required helper): Non-partial k-rounds unroll of `infSearch`:
    `infSearchSteps seq k` is the `InfSearchState` after k calls to `infExpand`,
    starting from `infSearchInit seq`. Unlike `infSearch`, this function is
    total: it does not test termination and simply exposes the k-th state.
    Used to state Theorem 3.5.1 without `partial def`: the finite cases
    assert `∃ k` with a halted tree; the infinite case asserts `∀ k`. -/
@[blueprint "chap3__theorem_3_5_1"]
def infSearchSteps (seq : InfSequent) : Nat → InfSearchState
  | 0     => infSearchInit seq
  | k + 1 => infExpand (infSearchSteps seq k)

/-- The limit tree contains exactly the nodes appearing in finite stages. -/
@[blueprint "chap3__definition_3_5_1"]
def infSearchLimit (seq : InfSequent) (p : List Nat) (label : Sequent) : Prop :=
  ∃ k, (infSearchSteps seq k).tree.labelAt p = some label

/-- The address domain of the limit is a rooted, finitely branching tree.
Its edge relation is the immediate-child relation, not stage succession. -/
@[blueprint "chap3__definition_3_5_1"]
def infSearchTreeDomain (seq : InfSequent) : TreeDomain where
  Node := List Nat
  root := []
  isNode := fun p => ∃ label, infSearchLimit seq p label
  children := fun p c =>
    (c = p ++ [0] ∨ c = p ++ [1]) ∧ ∃ label, infSearchLimit seq c label
  rootIsNode := ⟨(infSearchInit seq).rootSeq, 0, rfl⟩
  childrenAreNodes := fun _ _ _ h => h.2
  finiteBranching := by
    intro p _
    apply Set.Finite.subset (s := fun c : List Nat => c = p ++ [0] ∨ c = p ++ [1])
    · exact ⟨[p ++ [0], p ++ [1]], by intro c; simp⟩
    · intro c h; exact h.1



























/-- Theorem 3.5.1 (required helper): The search procedure halts on input
    sequent `seq` iff there exists some step `k` at which every leaf of
    the deduction tree in `infSearchSteps seq k` is finished in the
    infinite-search sense (axiom OR L=R=empty AND all-atomic). Matches
    textbook Def 3.5.1 via `infIsFinishedTree`. -/

@[blueprint "chap3__theorem_3_5_1"]
def infSearchHalts (seq : InfSequent) : Prop :=
  ∃ k, infIsFinishedTree (infSearchSteps seq k)

/-- Theorem 3.5.1 (required helper): An infinite sequent is `finite` when its
    antecedent and succedent both eventually return `none`. Used as the
    discriminator between cases (1)(i) (infinite Γ → Δ: search runs forever)
    and (1)(ii) (finite Γ → Δ: search produces a finite tree with a non-axiom
    leaf). -/

@[blueprint "chap3__theorem_3_5_1"]
def infSeqIsFinite (seq : InfSequent) : Prop :=
  (∃ N, ∀ n, n ≥ N → seq.antecedent n = none) ∧
  (∃ M, ∀ n, n ≥ M → seq.succedent n = none)

/-- Theorem 3.5.1 (required helper): A deduction tree is `closed` when every
    leaf is an axiom. Context-introduction edges are converted to a
    finite proof separately. Textbook: "search terminates with a
    closed tree T." -/

@[blueprint "chap3__theorem_3_5_1"]
def isClosedTree {s : Sequent} (dt : InfDeductionTree s) : Prop :=
  ∀ leaf ∈ dt.leaves, isAxiom leaf

/-- Theorem 3.5.1 (required helper): The first `n` values of an `InfSeq`,
    collected as a list, omitting empty positions (which form a suffix). Used to bind
    Theorem 3.5.1's `C₁,…,Cₘ` / `D₁,…,Dₙ` (textbook: "the initial subsequence
    of propositions in Γ that were deleted from Γ to obtain L") to the
    initial prefix of the input sequent consumed during the first k rounds
    of `infSearchSteps`. After `k` rounds, exactly `k+1` heads have been
    consumed: one by `infSearchInit` (placed at the root) and `k` by the
    `k` subsequent `infExpand` calls (introduced on unfinished branches). -/

@[blueprint "chap3__theorem_3_5_1"]
def initialPrefix (s : Nat → Option PropFormulaNormalized) : Nat → List PropFormulaNormalized
  | 0 => []
  | n + 1 =>
    match s n with
    | some A => initialPrefix s n ++ [A]
    | none => initialPrefix s n

/-- A genuinely nonterminating search has an infinite path in its own limit tree. -/
@[blueprint "chap3__theorem_3_5_1"]
theorem infSearch_infinitePath_of_not_halts (seq : InfSequent) (h : ¬ infSearchHalts seq) :
    ∃ address : Nat → List Nat, (infSearchTreeDomain seq).InfinitePath address 

end LCS.Propositional.Infinite
end
