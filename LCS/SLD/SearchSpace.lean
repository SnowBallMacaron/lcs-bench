import LCS.SLD.FirstOrder
import Attach

/-! # The SLD search space (§9.5.5)

SQ40 retains raw derivation records. SQ42 treats fair exploration of finite,
effectively listed children as sufficient for completeness. The executable
breadth-first scheduler is deferred (OD-A17; OD-9-10 (1)); OD-9-6 leaves the qualitative
expense remark outside the mathematical statements.
-/

namespace LCS.SLD.SearchSpace

open LCS.FirstOrder.Basic LCS.FOResolution.ClauseForm LCS.SLD.FirstOrder

/-- A rooted search space. Its tree nodes are finite rooted paths, so distinct
histories remain distinct even when their endpoint labels coincide (SQ40). -/
structure SLDSearchTree where
  Node : Type
  root : Node
  edge : Node → Node → Prop
  success : Node → Prop

def SLDSearchTree.endpoint (t : SLDSearchTree) (p : List t.Node) : t.Node :=
  p.getLast?.getD t.root

/-- Paths omit the root from their list; the empty list is the root path. -/
inductive SLDSearchTree.Path (t : SLDSearchTree) : List t.Node → Prop where
  | root : Path t []
  | extend {p : List t.Node} (hp : Path t p) {v : t.Node}
      (hv : t.edge (t.endpoint p) v) : Path t (p ++ [v])

structure SLDSearchTree.SuccessPath (t : SLDSearchTree) where
  nodes : List t.Node
  valid : t.Path nodes
  successful : t.success (t.endpoint nodes)

/-- One fixed decoder is used both for correspondence and for production. -/
def SLDSearchTree.decodes {t : SLDSearchTree} {R : Type}
    (d : t.SuccessPath → R) (p : t.SuccessPath) (r : R) : Prop := d p = r

/-- Horn inputs use the current first-order derivation interface. The program
is definite and every initial clause is a negative goal (OD-9-1, SQ17). -/
structure HornInput (L : Language) (hNoEq : L.withoutEquality) where
  program : List (FOHornClause L hNoEq)
  goals : List (FOHornClause L hNoEq)
  definite : ∀ c ∈ program, c.isDefinite hNoEq
  negative : ∀ c ∈ goals, ∃ body, c = FOHornClause.goal (hNoEq := hNoEq) body

/-- No quotient or representative policy is imposed on raw derivations. -/
abbrev RawDerivation {L : Language} {hNoEq : L.withoutEquality}
    (q : HornInput L hNoEq) :=
  Σ g : LCS.Finset (FOAtom L hNoEq), FOSLDDerivation hNoEq (fun c => c ∈ q.program) q.goals g

def RawDerivation.refutes {L : Language} {hNoEq : L.withoutEquality}
    {q : HornInput L hNoEq} (r : RawDerivation q) : Prop :=
  r.2.isRefutation hNoEq

/-- Deleting exactly the last constructor retains all stored resolution data. -/
def RawDerivation.parent {L : Language} {hNoEq : L.withoutEquality}
    {q : HornInput L hNoEq} (r : RawDerivation q) : Option (RawDerivation q) :=
  match r with
  | ⟨_, .init _ _⟩ => none
  | ⟨_, .step prev _ _ _ _ _ _ _ _ _ _ _⟩ => some ⟨_, prev⟩

/-- The common tree of all finite raw derivations of this input. The extra
root joins the possible initial goals. Every other edge extends a derivation. -/
def rawSearchTree {L : Language} {hNoEq : L.withoutEquality}
    (q : HornInput L hNoEq) : SLDSearchTree where
  Node := Option (RawDerivation q)
  root := none
  edge a b := ∃ r, b = some r ∧ r.parent = a
  success n := ∃ r, n = some r ∧ r.refutes

/-- Decode the terminal raw record, retaining the record itself, not its answer. -/
noncomputable def rawPathDecoder {L : Language} {hNoEq : L.withoutEquality}
    {q : HornInput L hNoEq} (p : (rawSearchTree q).SuccessPath) : RawDerivation q :=
  Classical.choose p.successful

/-- Both directions hold for every raw record, with the same tree and decoder
fixed before the record is quantified (SQ40). -/
theorem sldRefutation_iff_successfulPath {L : Language} {hNoEq : L.withoutEquality}
    (q : HornInput L hNoEq) (r : RawDerivation q) :
    r.refutes ↔ ∃ p : (rawSearchTree q).SuccessPath,
      SLDSearchTree.decodes rawPathDecoder p r := by
  -- REPAIR(T9-43): proof pending — reconstruct all raw prefixes and decode the endpoint exactly.
  sorry

/-- Refutation output at a stage is exactly decoding a successful path visited
at that stage in the same raw search tree. -/
def traversalProduces {L : Language} {hNoEq : L.withoutEquality}
    {q : HornInput L hNoEq}
    (visited : Nat → List (List (rawSearchTree q).Node)) (n : Nat)
    (r : RawDerivation q) : Prop :=
  ∃ p : (rawSearchTree q).SuccessPath,
    p.nodes ∈ visited n ∧ SLDSearchTree.decodes rawPathDecoder p r

/-- A traversal covering all successful paths produces exactly this input's
refutations, using the decoder of the representation theorem (SQ40). -/
theorem traversalProduces_iff_refutes {L : Language} {hNoEq : L.withoutEquality}
    (q : HornInput L hNoEq)
    (visited : Nat → List (List (rawSearchTree q).Node))
    (covers : ∀ p : (rawSearchTree q).SuccessPath, ∃ n, p.nodes ∈ visited n)
    (r : RawDerivation q) :
    (∃ n, traversalProduces visited n r) ↔ r.refutes := by
  -- REPAIR(T9-43): proof pending — combine path coverage with the exact raw-record correspondence.
  sorry

/-- SQ42's finite effective branching and decidable success interface.
It is conditional on the supplied tree and does not identify finite child
lists with all raw freshening choices. -/
structure EffectiveChildren (t : SLDSearchTree) where
  children : t.Node → List t.Node
  exactChildren : ∀ a b, b ∈ children a ↔ t.edge a b
  successTest : t.Node → Bool
  exactSuccess : ∀ a, successTest a = true ↔ t.success a

structure FrontierState (t : SLDSearchTree) where
  frontier : List (List t.Node)
  visited : List (List t.Node)

def initialFrontier (t : SLDSearchTree) : FrontierState t := ⟨[[]], []⟩

def childPaths {t : SLDSearchTree} (e : EffectiveChildren t)
    (p : List t.Node) : List (List t.Node) :=
  (e.children (t.endpoint p)).map (fun v => p ++ [v])

/-- Service one particular frontier occurrence, enqueue its children, and
record its visit. Frontier order is left to the traversal policy. Empty frontiers idle, allowing runs to have all finite stages. -/
inductive FrontierExpansion {t : SLDSearchTree} (e : EffectiveChildren t) :
    FrontierState t → Option (List t.Node) → FrontierState t → Prop where
  | service (before after seen : List (List t.Node)) (p : List t.Node)
      (next : List (List t.Node))
      (order : next.Perm (before ++ after ++ childPaths e p)) :
      FrontierExpansion e ⟨before ++ p :: after, seen⟩ (some p) ⟨next, p :: seen⟩
  | idle (seen : List (List t.Node)) :
      FrontierExpansion e ⟨[], seen⟩ none ⟨[], seen⟩

/-- Fairness is eventual service of every queued path entry, independently of
success. It is not defined as eventual discovery of successful paths (SQ42). -/
structure FairFrontierRun {t : SLDSearchTree} (e : EffectiveChildren t) where
  state : Nat → FrontierState t
  serviced : Nat → Option (List t.Node)
  initial : state 0 = initialFrontier t
  transition : ∀ n, FrontierExpansion e (state n) (serviced n) (state (n + 1))
  fair : ∀ n p, p ∈ (state n).frontier → ∃ m, n ≤ m ∧ serviced m = some p

/-- Fair exploration visits every successful finite path by a finite stage.
This does not assert termination on failure or exclusivity of breadth-first
search; the effective BFS scheduler remains deferred (SQ42, OD-A17). -/
theorem successfulPath_eventuallyVisited {t : SLDSearchTree}
    (e : EffectiveChildren t) (run : FairFrontierRun e) (p : t.SuccessPath) :
    ∃ n, p.nodes ∈ (run.state n).visited := by
  -- REPAIR(T9-44): proof pending — induct on path length using eventual servicing of each queued prefix.
  sorry

/-- Deterministic depth-first expansion: service the first entry and put its
children before the remaining frontier, in the given child order. -/
def depthFirstStep {t : SLDSearchTree} (e : EffectiveChildren t)
    (s : FrontierState t) : FrontierState t :=
  match s.frontier with
  | [] => s
  | p :: rest => ⟨childPaths e p ++ rest, p :: s.visited⟩

def DepthFirstTransition {t : SLDSearchTree} (e : EffectiveChildren t)
    (s s' : FrontierState t) : Prop := s' = depthFirstStep e s

/-- The actual finite stages of the same deterministic depth-first strategy. -/
def DepthFirstRun {t : SLDSearchTree} (e : EffectiveChildren t) :
    Nat → FrontierState t
  | 0 => initialFrontier t
  | n + 1 => depthFirstStep e (DepthFirstRun e n)

open LCS.Resolution.GCNF LCS.SLD.Propositional LCS.SLD.SLDForm

/-- The propositional atom p is an independent atom, represented by index 0. -/
def recursiveBeforeFact_atom : Nat := 0

/-- The ordered definite program p :- p, followed by the fact p. -/
def recursiveBeforeFact_program : List Clause :=
  [LCS.Finset.ofList [.pos recursiveBeforeFact_atom, .neg recursiveBeforeFact_atom],
   LCS.Finset.ofList [.pos recursiveBeforeFact_atom]]

/-- The initial negative goal :- p. -/
def recursiveBeforeFact_query : Clause :=
  LCS.Finset.ofList [.neg recursiveBeforeFact_atom]

/-- False labels the residual goal :- p; true labels the empty goal. The
rooted paths distinguish all repeated recursive calls from each other. -/
def recursiveBeforeFact_goal (done : Bool) : Clause :=
  if done then Clause.empty else recursiveBeforeFact_query

/-- The ordered unfolding has a recursive child first and a fact child second
at each :- p goal, and no children at the empty goal. -/
def recursiveBeforeFact_tree : SLDSearchTree where
  Node := Bool
  root := false
  edge a _ := a = false
  success a := a = true

def recursiveBeforeFact_children : EffectiveChildren recursiveBeforeFact_tree where
  children := fun (a : Bool) => if a then [] else [false, true]
  exactChildren := by
    change ∀ a b : Bool, b ∈ (if a then [] else [false, true]) ↔ a = false
    intro a b
    cases a <;> cases b <;> decide
  successTest a := a
  exactSuccess _ := Iff.rfl

/-- The displayed tree is an admissible SLD unfolding of the concrete ordered
program, with child order exactly the order of its clause applications. This
connects the traversal example to SLD inference, not just to a binary tree. -/
def recursiveBeforeFact_admissible : Prop :=
  (∀ c ∈ recursiveBeforeFact_program, isDefiniteClause c) ∧
  allNegative recursiveBeforeFact_query ∧
  (∀ a : Bool,
    (recursiveBeforeFact_children.children a).map recursiveBeforeFact_goal =
      if a then [] else recursiveBeforeFact_program.map
        (resolveStep (recursiveBeforeFact_goal a) recursiveBeforeFact_atom)) ∧
  (∀ a b : Bool, recursiveBeforeFact_tree.edge a b →
    ∃ c ∈ recursiveBeforeFact_program,
      selectedAtomMatches (recursiveBeforeFact_goal a) recursiveBeforeFact_atom c ∧
      resolveStep (recursiveBeforeFact_goal a) recursiveBeforeFact_atom c =
        recursiveBeforeFact_goal b)

/-- For p :- p followed by p, the fact gives a one-step successful path.
The specified DFS strategy instead keeps descending the first, recursive
branch and never visits that success at any finite stage (SQ42). -/
theorem recursiveBeforeFact_DFS_missesSuccess :
    recursiveBeforeFact_admissible ∧
    recursiveBeforeFact_tree.Path [true] ∧
    recursiveBeforeFact_tree.success (recursiveBeforeFact_tree.endpoint [true]) ∧
    (∃ r : SLDDerivation,
      r.definiteClauses = (fun c => c ∈ recursiveBeforeFact_program) ∧
      r.goals = [recursiveBeforeFact_query] ∧
      r.sequence = [recursiveBeforeFact_query, Clause.empty] ∧
      isSLDRefutation r) ∧
    (∀ n, (DepthFirstRun recursiveBeforeFact_children n).frontier.head? =
      some (List.replicate n false)) ∧
    (∀ n, [true] ∉ (DepthFirstRun recursiveBeforeFact_children n).visited) := by
  -- REPAIR(T9-45): proof pending — certify the SLD edges and fact refutation, then induct on DFS stages.
  sorry

end LCS.SLD.SearchSpace
