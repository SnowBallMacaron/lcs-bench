import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Part2.ProofsStamp
import LCS.Propositional.Infinite.Part1
attach_helper_namespace LCS.Propositional.Infinite.Proofs

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- Example 3.5.2 (companion type): The textbook informally introduces
    signed formulae in this example: "The pair (U, V) can be encoded as
    a single set if we prefix every proposition in U with the letter T
    (standing for true), and every proposition in V with the letter F
    (standing for false)." This is the informal version; the formal
    definition is Definition 3.5.3 in SignedFormulae.lean. -/
@[blueprint "chap3__example_3_5_2"]
inductive SignedFormula where
  | trueSign : PropFormulaNormalized → SignedFormula
  | falseSign : PropFormulaNormalized → SignedFormula
  deriving DecidableEq, Repr

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
namespace InfSeq

/-- Definition 3.5.1 (companion): The empty sequence, returning none for
    all indices. Represents the empty sequence <>. -/
@[blueprint "chap3__definition_3_5_1"]
def empty : Nat → Option PropFormulaNormalized := fun _ => none

/-- Definition 3.5.1 (companion): Returns the element at index 0 of the
    sequence, or none if the sequence is empty at index 0. -/
@[blueprint "chap3__definition_3_5_1"]
def head (s : Nat → Option PropFormulaNormalized) : Option PropFormulaNormalized := s 0

/-- Definition 3.5.1 (companion): Shifts the sequence by one position:
    tail s n = s (n + 1). If s is empty, tail returns the empty
    sequence. -/
@[blueprint "chap3__definition_3_5_1"]
def tail (s : Nat → Option PropFormulaNormalized) : Nat → Option PropFormulaNormalized :=
  fun n => s (n + 1)

end InfSeq
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
namespace PropFormulaNormalized

/-- Definition 3.5.1 (companion): True iff the formula is a propositional
    variable (PropFormulaNormalized.var _). Mirrors isAtomicFormula from G.Search. -/
@[blueprint "chap3__definition_3_5_1"]
def isAtomic : PropFormulaNormalized → Prop
  | .var _ => True
  | _ => False

end PropFormulaNormalized
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

/-- Theorem 3.5.1 (required helper): A deduction tree has a non-axiom leaf
    iff one of its leaves is not an axiom. Textbook case (1)(ii): "search
    produces a finite tree T with some non-axiom leaf." -/
@[blueprint "chap3__theorem_3_5_1"]
def hasNonAxiomLeaf {s : Sequent} (dt : InfDeductionTree s) : Prop :=
  ∃ leaf ∈ dt.leaves, ¬ isAxiom leaf

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

-- ========= Definition 3.5.2: Semantic Notions for Infinite Sequents =========

/-- Definition 3.5.2: A valuation v falsifies an infinite sequent
    Gamma -> Delta if v satisfies every formula A in Gamma (evalExtN v A = T)
    and v falsifies every formula B in Delta (evalExtN v B = F). -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqFalsifies (v : Valuation) (seq : InfSequent) : Prop :=
  (∀ n A, seq.antecedent n = some A → evalExtN v A = BoolVal.T) ∧
  (∀ n B, seq.succedent n = some B → evalExtN v B = BoolVal.F)

/-- Definition 3.5.2: An infinite sequent is falsifiable
    if there exists a valuation that falsifies it. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqFalsifiable (seq : InfSequent) : Prop :=
  ∃ v : Valuation, infSeqFalsifies v seq

/-- Definition 3.5.2: A valuation v satisfies an infinite
    sequent Gamma -> Delta if, whenever v satisfies every formula A
    in Gamma, then there exists some formula B in Delta such that
    v satisfies B. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqSatisfies (v : Valuation) (seq : InfSequent) : Prop :=
  (∀ n A, seq.antecedent n = some A → evalExtN v A = BoolVal.T) →
  (∃ n B, seq.succedent n = some B ∧ evalExtN v B = BoolVal.T)

/-- Definition 3.5.2: An infinite sequent is satisfiable
    if there exists a valuation that satisfies it. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqSatisfiable (seq : InfSequent) : Prop :=
  ∃ v : Valuation, infSeqSatisfies v seq

/-- Definition 3.5.2: An infinite sequent is valid if it
    is satisfied by every valuation. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqValid (seq : InfSequent) : Prop :=
  ∀ v : Valuation, infSeqSatisfies v seq

/-- Definition 3.5.2: An infinite sequent is provable if
    there exist finite subsequences Gamma_fin of the antecedent and
    Delta_fin of the succedent such that the finite sequent
    Gamma_fin -> Delta_fin is provable in G'. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqProvable (seq : InfSequent) : Prop :=
  ∃ (Gamma_fin : List PropFormulaNormalized) (Delta_fin : List PropFormulaNormalized),
    (∀ A ∈ Gamma_fin, ∃ n, seq.antecedent n = some A) ∧
    (∀ B ∈ Delta_fin, ∃ n, seq.succedent n = some B) ∧
    sequentProvable (Sequent.mk Gamma_fin Delta_fin)

-- ========= Lemma 3.5.1 (companion def): Infinite Path =========



-- ========= Example 3.5.1: Closed Infinite Search =========

/-- Example 3.5.1: The infinite sequent with
    Gamma_0 = <P0, P0=>P1, P1=>P2, ...> and Delta_0 = <Q, P3>.
    The antecedent is: index 0 -> P0, index n+1 -> (Pn => P(n+1)).
    The succedent is: index 0 -> Q (var 0), index 1 -> P3,
    all other indices -> none. -/
@[blueprint "chap3__example_3_5_1" (main := true)]
def exInfSearchClosedAntecedent : InfSequent :=
  { antecedent := fun n =>
      if n = 0 then some (.var 1)
      else some (.impl (.var n) (.var (n + 1)))
    succedent := fun n =>
      if n = 0 then some (.var 0)
      else if n = 1 then some (.var 4)
      else none
    antecedent_noHoles := by
      intro n h
      cases n <;> simp at h
    succedent_noHoles := by
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
        cases n with
        | zero => simp_all
        | succ n => simp }

/-- Example 3.5.1 (companion): The initial search state for the closed
    example. Tree = leaf (P0 -> Q), L = <P0=>P1, P1=>P2, ...>,
    R = <P3>. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedInit : InfSearchState :=
  infSearchInit exInfSearchClosedAntecedent

/-- Example 3.5.1 (companion): The search state after four rounds of
    infExpand. Demonstrates that the infinite search terminates in
    4 rounds on this particular input (all leaves become axioms). -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound4 : InfSearchState :=
  let s0 := exInfSearchClosedInit
  let s1 := infExpand s0
  let s2 := infExpand s1
  let s3 := infExpand s2
  infExpand s3

/-- Example 3.5.1: The displayed initial state. Here var 0 is Q and
    var (i + 1) is Pᵢ; L starts with P₀ ⊃ P₁ and R contains only P₃. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedInitDisplayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 1)) (.var (n + 2)))
    R := fun n => match n with | 0 => some (.var 4) | _ + 1 => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; cases n with | zero => cases h | succ n => rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .leaf ⟨[.var 1], [.var 0]⟩ }

/-- Initialization produces the displayed tree and both remaining streams. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedInit_eq_displayed :
    exInfSearchClosedInit = exInfSearchClosedInitDisplayed

/-- Example 3.5.1: The complete displayed round-1 state. The tree
    retains all introduction edges and axiom branches; L starts with P₁ ⊃ P₂
    and R is empty. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound1Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 2)) (.var (n + 3)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.leaf ⟨[.var 1, .impl (.var 1) (.var 2)], [.var 0, .var 4]⟩) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound1_eq_displayed :
    infExpand exInfSearchClosedInitDisplayed = exInfSearchClosedRound1Displayed

/-- Example 3.5.1: The complete displayed round-2 state. The tree
    retains all introduction edges and axiom branches; L starts with P₂ ⊃ P₃
    and R is empty. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound2Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 3)) (.var (n + 4)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.leaf ⟨[.var 2, .var 1, .impl (.var 2) (.var 3)], [.var 0, .var 4]⟩))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound2_eq_displayed :
    infExpand exInfSearchClosedRound1Displayed = exInfSearchClosedRound2Displayed

/-- Example 3.5.1: The complete displayed round-3 state. The tree
    retains all introduction edges and axiom branches; L starts with P₃ ⊃ P₄
    and R is empty. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound3Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 4)) (.var (n + 5)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.twoPremise (.implLeft [.var 2, .var 1] [] [.var 0, .var 4] (.var 2) (.var 3))
            (.leaf ⟨[.var 2, .var 1], [.var 2, .var 0, .var 4]⟩)
            (.extend (some (.impl (.var 3) (.var 4))) none
              (.leaf ⟨[.var 3, .var 2, .var 1, .impl (.var 3) (.var 4)], [.var 0, .var 4]⟩))))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound3_eq_displayed :
    infExpand exInfSearchClosedRound2Displayed = exInfSearchClosedRound3Displayed

/-- Example 3.5.1: The complete displayed round-4 state. The tree
    retains all introduction edges and axiom branches; L starts with P₄ ⊃ P₅
    and R is empty. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound4Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 5)) (.var (n + 6)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.twoPremise (.implLeft [.var 2, .var 1] [] [.var 0, .var 4] (.var 2) (.var 3))
            (.leaf ⟨[.var 2, .var 1], [.var 2, .var 0, .var 4]⟩)
            (.extend (some (.impl (.var 3) (.var 4))) none
              (.twoPremise (.implLeft [.var 3, .var 2, .var 1] [] [.var 0, .var 4] (.var 3) (.var 4))
                (.leaf ⟨[.var 3, .var 2, .var 1], [.var 3, .var 0, .var 4]⟩)
                (.leaf ⟨[.var 4, .var 3, .var 2, .var 1], [.var 0, .var 4]⟩)))))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound4_eq_displayed :
    infExpand exInfSearchClosedRound3Displayed = exInfSearchClosedRound4Displayed

/-- The original four-round computation equals the complete final display. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound4_computation_eq_displayed :
    exInfSearchClosedRound4 = exInfSearchClosedRound4Displayed

/-- Example 3.5.1 (companion): A proof tree extracted from the closed
    search tree by propagating introduced propositions upward and
    deleting duplicate nodes. Proves a finite sequent P0, P0=>P1,
    P1=>P2, P2=>P3 -> Q, P3 that witnesses provability of the
    original infinite sequent. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedProofTreeSeq : Sequent :=
  Sequent.mk
    [.var 1, .impl (.var 1) (.var 2), .impl (.var 2) (.var 3), .impl (.var 3) (.var 4)]
    [.var 0, .var 4]

/-- Example 3.5.1 (companion): The finite witness sequent is valid —
chain of modus ponens yields P3, which is in the succedent. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedProofTreeSeq_valid :
    sequentValid exInfSearchClosedProofTreeSeq 

/-- The finite proof obtained by propagating the three introduced
implications toward the root and deleting the introduction edges. Its
three implication-left rules are the rules used in the four-round search. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedProofTree : ProofTree exInfSearchClosedProofTreeSeq := by
  apply ProofTree.twoPremise (GentzenStep2.implLeft
    [.var 1] [.impl (.var 2) (.var 3), .impl (.var 3) (.var 4)]
    [.var 0, .var 4] (.var 1) (.var 2))
  · exact .axiom_ _ ⟨.var 1, by simp, by simp⟩
  · apply ProofTree.twoPremise (GentzenStep2.implLeft
      [.var 2, .var 1] [.impl (.var 3) (.var 4)]
      [.var 0, .var 4] (.var 2) (.var 3))
    · exact .axiom_ _ ⟨.var 2, by simp, by simp⟩
    · apply ProofTree.twoPremise (GentzenStep2.implLeft
        [.var 3, .var 2, .var 1] [] [.var 0, .var 4] (.var 3) (.var 4))
      · exact .axiom_ _ ⟨.var 3, by simp, by simp⟩
      · exact .axiom_ _ ⟨.var 4, by simp, by simp⟩

@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedProofTree_nonempty :
    Nonempty (ProofTree exInfSearchClosedProofTreeSeq) 

-- ========= Example 3.5.2: Non-Terminating Infinite Search =========

/-- Example 3.5.2: The infinite sequent with the same antecedent as
    Example 3.5.1 but succedent Delta_0 = <Q> only. The absence of P3
    in the succedent means the search does not terminate: the rightmost
    branch is infinite. -/
@[blueprint "chap3__example_3_5_2" (main := true)]
def exInfSearchNonTerminating : InfSequent :=
  { antecedent := fun n =>
      if n = 0 then some (.var 1)
      else some (.impl (.var n) (.var (n + 1)))
    succedent := fun n =>
      if n = 0 then some (.var 0)
      else none
    antecedent_noHoles := by
      intro n h
      cases n <;> simp at h
    succedent_noHoles := by
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
        cases n with
        | zero => simp_all
        | succ n => simp }

/-- Example 3.5.2 (companion): The set U of all propositions occurring
    as premises along the infinite rightmost branch:
    U = {P0, P1, P2, ...} ∪ {Pi ⇒ P(i+1) | i ∈ Nat}. -/
@[blueprint "chap3__example_3_5_2"]
def exInfBranchPremises : Set PropFormulaNormalized :=
  fun A => (∃ i : Nat, A = .var (i + 1)) ∨ (∃ i : Nat, A = .impl (.var (i + 1)) (.var (i + 2)))

/-- Example 3.5.2 (companion): The set V of all propositions occurring
    as conclusions along the infinite rightmost branch: V = {Q}. -/
@[blueprint "chap3__example_3_5_2"]
def exInfBranchConclusions : Set PropFormulaNormalized :=
  fun A => A = .var 0

/-- Example 3.5.2 (companion): The Hintikka set of signed formulae
    combining T-prefixed premises and F-prefixed conclusions:
    {T(P₀⊃P₁), ..., TP₀, TP₁, ..., FQ}. The textbook says: "The
    resulting set ... is a set having some remarkable properties, and
    called a Hintikka set." -/
@[blueprint "chap3__example_3_5_2"]
def exInfHintikkaSet : Set SignedFormula :=
  fun sf => match sf with
    | .trueSign A => exInfBranchPremises A
    | .falseSign A => exInfBranchConclusions A

/-- Example 3.5.2 (companion): The falsifying valuation v where
    v(Pi) = T for all i >= 0 and v(Q) = F (where Q = var 0).
    This valuation satisfies all premises and falsifies Q,
    thereby falsifying the original sequent. -/
@[blueprint "chap3__example_3_5_2"]
def exInfFalsifyingValuation : Valuation :=
  fun n => if n = 0 then BoolVal.F else BoolVal.T



/-- The stated countervaluation really falsifies Example 3.5.2. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfFalsifyingValuation_falsifies :
    infSeqFalsifies exInfFalsifyingValuation exInfSearchNonTerminating 







/-- Example 3.5.1 closes after the textbook's four rounds. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound4_closed :
    isClosedTree exInfSearchClosedRound4.tree 

/-- Atomic checkpoint antecedent Pₙ,…,P₀ on the rightmost branch. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostAtoms : Nat → List PropFormulaNormalized
  | 0 => [.var 1]
  | n + 1 => .var (n + 2) :: exInfRightmostAtoms n

@[blueprint "chap3__example_3_5_2"]
def exInfRightmostCheckpoint (n : Nat) : Sequent :=
  Sequent.mk (exInfRightmostAtoms n) [.var 0]

/-- The intermediate label obtained by introducing Pₙ⇒Pₙ₊₁. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostIntroduced (n : Nat) : Sequent :=
  Sequent.mk (exInfRightmostAtoms n ++ [.impl (.var (n + 1)) (.var (n + 2))]) [.var 0]

/-- The full rightmost path alternates introduction child 0 and implication child 1. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostAddress (n : Nat) : List Nat :=
  (List.range n).map (fun i => i % 2)

/-- Full labels include the intermediate implication-bearing sequents. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostLabel (n : Nat) : Sequent :=
  if n % 2 = 0 then exInfRightmostCheckpoint (n / 2)
  else exInfRightmostIntroduced (n / 2)





















-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem InfDeductionTree.ofDeductionTree_cast {s t : Sequent} (h : s = t)
    (tree : DeductionTree s) :
    ofDeductionTree (h ▸ tree) = h ▸ ofDeductionTree tree := by
  subst h
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem InfDeductionTree.bindLeaves_cast (f : (s : Sequent) → InfDeductionTree s)
    {s t : Sequent} (h : s = t) (tree : InfDeductionTree s) :
    bindLeaves f (h ▸ tree) = h ▸ bindLeaves f tree := by
  subst h
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem InfDeductionTree.labelAt_cast {s t : Sequent} (h : s = t)
    (tree : InfDeductionTree s) (p : List Nat) :
    (h ▸ tree : InfDeductionTree t).labelAt p = tree.labelAt p := by
  subst h
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem InfDeductionTree.leafAt_cast {s t : Sequent} (h : s = t)
    (tree : InfDeductionTree s) (p : List Nat) :
    (h ▸ tree : InfDeductionTree t).leafAt p = tree.leafAt p := by
  subst h
  rfl












/-- Example 3.5.2's rightmost path is an infinite path of the tree actually built by search. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfRightmost_is_infinite_path :
    (infSearchTreeDomain exInfSearchNonTerminating).InfinitePath exInfRightmostAddress 

/-- The source's atomic displayed labels are exactly the even checkpoints.
Odd path positions retain the mandatory intermediate implication labels. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfRightmost_checkpoints (n : Nat) :
    infSearchLimit exInfSearchNonTerminating (exInfRightmostAddress (2 * n))
      (Sequent.mk (exInfRightmostAtoms n) [.var 0]) 

/-- The source's signed set is exactly the union along this actual full branch. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfHintikkaSet_actual_branch (sf : SignedFormula) :
    exInfHintikkaSet sf ↔
      match sf with
      | .trueSign A => ∃ n, A ∈ (exInfRightmostLabel n).antecedent
      | .falseSign A => ∃ n, A ∈ (exInfRightmostLabel n).succedent 

/-- The stated valuation satisfies every signed formula on the actual rightmost branch. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfHintikkaSet_satisfied (sf : SignedFormula) (h : exInfHintikkaSet sf) :
    match sf with
    | .trueSign A => evalExtN exInfFalsifyingValuation A = BoolVal.T
    | .falseSign A => evalExtN exInfFalsifyingValuation A = BoolVal.F 

/-- The explicit rightmost leaf stays unfinished at every stage. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfSearchNonTerminating_does_not_halt :
    ¬ infSearchHalts exInfSearchNonTerminating 

-- ========= Definition 3.5.2 (companion theorem): Provability implies Validity =========

/-- Definition 3.5.2 (companion): If an infinite sequent is provable
    (i.e., there exist finite subsequences of Gamma and Delta forming a
    provable finite sequent), then it is valid (satisfied by every
    valuation). The proof proceeds by extracting the finite witnessing
    sequent, applying finite soundness (Lemma 3.4.3), and lifting the
    result to the infinite sequent. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
theorem infSeqProvable_implies_valid (seq : InfSequent)
    (h : infSeqProvable seq) : infSeqValid seq 

-- ========= Lemma 3.5.1 (infrastructure): Reachable =========

/-- Lemma 3.5.1 (required helper): Reflexive transitive closure of the
    children relation. -/
@[blueprint "chap3__lemma_3_5_1"]
inductive Reachable (T : TreeDomain) : T.Node → T.Node → Prop where
  | refl : ∀ n, Reachable T n n
  | step : ∀ p c d, T.children p c → Reachable T c d → Reachable T p d

end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
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
end LCS.Propositional.Infinite
end

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

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



/-- A genuinely nonterminating search has an infinite path in its own limit tree. -/
@[blueprint "chap3__theorem_3_5_1"]
theorem infSearch_infinitePath_of_not_halts (seq : InfSequent) (h : ¬ infSearchHalts seq) :
    ∃ address : Nat → List Nat, (infSearchTreeDomain seq).InfinitePath address 

end LCS.Propositional.Infinite
end

