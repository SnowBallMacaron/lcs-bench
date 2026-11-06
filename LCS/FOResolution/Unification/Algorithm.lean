import LCS.Item
import LCS.Util
import LCS.FOResolution.Unification
import LCS.FOResolution.ClauseForm
import Attach
import LCS.FOResolution.Unification.Algorithm.ProofsStamp

/-! # FOResolution.Unification.Algorithm
    Formalization of Chapter 8, Section 8.4.2.
    The unification algorithm: tree functions, the algorithm itself,
    and its correctness proof.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.Unification.Algorithm

-- ===================================================================
-- Definition 8.4.3: Tree navigation functions
-- ===================================================================

/-- Definition 8.4.3 (companion): A tree address is a sequence of natural
numbers identifying a position in a tree (as in Section 2.2). -/
@[blueprint "chap8__definition_8_4_3"]
abbrev TreeAddr := List Nat

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Labels of ranked trees distinguish variables from rigid symbols,
    even when a rigid symbol has rank zero. -/
@[blueprint "chap8__definition_8_4_3"]
inductive RankedTreeLabel (Symbol : Type) where
  | variable (name : Nat)
  | rigid (symbol : Symbol)
  deriving DecidableEq

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Variable labels have rank zero; rigid labels retain their prescribed rank. -/
def RankedTreeLabel.rank {Symbol : Type} (rank : Symbol → Nat) :
    RankedTreeLabel Symbol → Nat
  | .variable _ => 0
  | .rigid f => rank f

/-- Finite ranked trees. Variables are leaves; a rigid symbol has exactly
    its prescribed finite number of ordered children. Nullary rigid symbols
    are constants, distinct from variables. -/
@[blueprint "chap8__definition_8_4_3"]
inductive RankedTreeData (Symbol : Type) (rank : Symbol → Nat) where
  | var (name : Nat)
  | node (symbol : Symbol) (children : Fin (rank symbol) → RankedTreeData Symbol rank)

/-- Rigid syntax labels retain their syntactic sort. Equality is a binary
    label available exactly when the language has equality. -/
@[blueprint "chap8__definition_8_4_1"]
inductive SyntaxTreeSymbol (L : LCS.FirstOrder.Basic.Language) where
  | constant : L.constSymbols → SyntaxTreeSymbol L
  | function : L.funSymbols → SyntaxTreeSymbol L
  | predicate : L.predSymbols → SyntaxTreeSymbol L
  | equality : L.hasEquality = true → SyntaxTreeSymbol L

/-- Ranks are inherited from the signature; equality has rank two. -/
@[blueprint "chap8__definition_8_4_1"]
def SyntaxTreeSymbol.rank {L : LCS.FirstOrder.Basic.Language} :
    SyntaxTreeSymbol L → Nat
  | .constant _ => 0
  | .function f => L.funArity f
  | .predicate p => L.predArity p
  | .equality _ => 2

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The actual root label of a ranked tree. -/
def RankedTreeData.rootLabel {Symbol : Type} {rank : Symbol → Nat} :
    RankedTreeData Symbol rank → RankedTreeLabel Symbol
  | .var x => .variable x
  | .node f _ => .rigid f

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Structural subtree lookup. The empty list names the root; child positions
    are one-based as in the source. Zero, out-of-rank children, and descent
    through a variable return none. -/
@[blueprint "chap8__definition_8_4_3"]
def RankedTreeData.subtreeAt {Symbol : Type} {rank : Symbol → Nat} :
    RankedTreeData Symbol rank → TreeAddr → Option (RankedTreeData Symbol rank)
  | t, [] => some t
  | .var _, _ :: _ => none
  | .node _ _, 0 :: _ => none
  | .node f children, (i + 1) :: rest =>
      if h : i < rank f then (children ⟨i, h⟩).subtreeAt rest else none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Actual label lookup, defined exactly where structural subtree lookup succeeds. -/
@[blueprint "chap8__definition_8_4_3"]
def RankedTreeData.labelAt {Symbol : Type} {rank : Symbol → Nat}
    (t : RankedTreeData Symbol rank) (u : TreeAddr) : Option (RankedTreeLabel Symbol) :=
  (t.subtreeAt u).map RankedTreeData.rootLabel

-- ATTACH-BLOCKER: unsupported untagged structure
/-- General navigation operations for the existing polymorphic algorithm
    consumers. The source-facing TreeNav restricts the tree and address types. -/
@[blueprint "chap8__definition_8_4_3"]
structure TreeNavCore (Tree : Type) (Addr : Type) (Subst : Type) :
    Type where
  /-- leaf(u) = true iff u is a leaf in tree t -/
  isLeaf : Tree → Addr → Bool
  /-- variable(t(u)) = true iff the label at address u in tree t
  is a variable -/
  isVariable : Tree → Addr → Bool
  /-- left(u) = u1 if not a leaf, nil (none) otherwise -/
  left : Tree → Addr → Option Addr
  /-- right(ui) = u(i+1) if in dom(t), nil (none) otherwise -/
  right : Tree → Addr → Option Addr
  /-- dosubstitution(t, sigma) applies substitution sigma to
  tree t -/
  doSubstitution : Tree → Subst → Tree

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A finite-support substitution on ranked trees. The support list may
    contain fixed variables; outside it the map is the identity. -/
@[blueprint "chap8__definition_8_4_3"]
structure FiniteTreeSubstitution (Symbol : Type) (rank : Symbol → Nat) where
  support : List Nat
  map : Nat → RankedTreeData Symbol rank
  outsideSupport : ∀ x, x ∉ support → map x = .var x

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Structural leafhood at a current-tree address; invalid addresses are false. -/
def RankedTreeData.isLeaf {Symbol : Type} {rank : Symbol → Nat}
    (t : RankedTreeData Symbol rank) (u : TreeAddr) : Bool :=
  match t.subtreeAt u with
  | some (.var _) => true
  | some (.node f _) => rank f == 0
  | none => false

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Variable classification consults the actual label, distinguishing constants. -/
def RankedTreeData.isVariable {Symbol : Type} {rank : Symbol → Nat}
    (t : RankedTreeData Symbol rank) (u : TreeAddr) : Bool :=
  match t.labelAt u with
  | some (.variable _) => true
  | _ => false

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- First child in the current tree, or none at leaves and invalid addresses. -/
def RankedTreeData.firstChild {Symbol : Type} {rank : Symbol → Nat}
    (t : RankedTreeData Symbol rank) (u : TreeAddr) : Option TreeAddr :=
  if (t.subtreeAt u).isSome && !t.isLeaf u then some (u ++ [1]) else none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Next sibling in the current tree. The root has no sibling.
    For a nonroot address ui, test the actual domain at u(i+1). -/
def RankedTreeData.nextSibling {Symbol : Type} {rank : Symbol → Nat}
    (t : RankedTreeData Symbol rank) (u : TreeAddr) : Option TreeAddr :=
  match u.getLast? with
  | none => none
  | some i =>
      let next := u.dropLast ++ [i + 1]
      if (t.subtreeAt next).isSome then some next else none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Simultaneous homomorphic substitution. Replacement trees are returned as
    supplied, and are not recursively substituted again. Rigid labels and the
    Fin-indexed order of their children are preserved. -/
@[blueprint "chap8__definition_8_4_3"]
def RankedTreeData.substitute {Symbol : Type} {rank : Symbol → Nat} :
    RankedTreeData Symbol rank → (Nat → RankedTreeData Symbol rank) →
      RankedTreeData Symbol rank
  | .var x, sigma => sigma x
  | .node f children, sigma =>
      .node f (fun i => (children i).substitute sigma)

/-- Definition 8.4.3: the five concrete operations on finite ranked trees.
    Navigation always inspects the supplied current tree. Substitution is the
    simultaneous homomorphic extension of a finite-support variable map. -/
@[blueprint "chap8__definition_8_4_3" (main := true)]
def TreeNav (Symbol : Type) (rank : Symbol → Nat) :
    TreeNavCore (RankedTreeData Symbol rank) TreeAddr (FiniteTreeSubstitution Symbol rank) where
  isLeaf := RankedTreeData.isLeaf
  isVariable := RankedTreeData.isVariable
  left := RankedTreeData.firstChild
  right := RankedTreeData.nextSibling
  doSubstitution t sigma := t.substitute sigma.map

/-- Preorder visits the root first, then recursively visits every child from
    left to right. Child indices are one-based in addresses. Variables and
    nullary rigid nodes both contribute just the root address. -/
@[blueprint "chap8__definition_8_4_3"]
def preorderAddresses {Symbol : Type} {rank : Symbol → Nat} :
    RankedTreeData Symbol rank → List TreeAddr
  | .var _ => [[]]
  | .node _ children =>
      [] :: (List.ofFn fun i =>
        (preorderAddresses (children i)).map (fun u => (i.val + 1) :: u)).flatten

-- ===================================================================
-- Definition 8.4.4: Unification algorithm types
-- ===================================================================

/-- A variable occurs in a finite ranked tree exactly when it labels a leaf.
    Rigid nullary symbols are constants and contain no variable. -/
@[blueprint "chap8__definition_8_4_4"]
def treeOccurs {Symbol : Type} {rank : Symbol → Nat} (x : Nat) :
    RankedTreeData Symbol rank → Prop
  | .var y => x = y
  | .node _ children => ∃ i, treeOccurs x (children i)

/-- Definition 8.4.4 (companion): The output of the unification algorithm:
a flag indicating whether the trees are unifiable, the accumulated
substitution (unifier), and the resulting most common form tree. -/
@[blueprint "chap8__definition_8_4_4"]
structure UnificationResult (Tree : Type) (Subst : Type) :
    Type where
  /-- True iff the two input trees are unifiable -/
  unifiable : Bool
  /-- The accumulated substitution (most general unifier if
  unifiable) -/
  unifier : Subst
  /-- First stored tree at return; on success it is the common image of both inputs. -/
  resultTree : Tree

/-- Definition 8.4.4 (companion): The mutable state of the unification
algorithm: the two trees being unified, the current traversal
position (node), the accumulated unifier, and the success flag. -/
@[blueprint "chap8__definition_8_4_4"]
structure UnifyState (Symbol : Type) (rank : Symbol → Nat) where
  /-- First and second stored trees, returned after each completed update. -/
  tree1 : RankedTreeData Symbol rank
  tree2 : RankedTreeData Symbol rank
  /-- This frame's node reference. The child cursor is local to the recursive frame. -/
  node : Option TreeAddr
  /-- Accumulated finite unifier and success flag, passed by state return. -/
  unifier : FiniteTreeSubstitution Symbol rank
  unifiable : Bool

/-- Each stored tree is the accumulated substitution applied to its own
    original input. This invariant is asserted at initialization and completed
    paired updates, rather than between the source's individual assignments. -/
@[blueprint "chap8__definition_8_4_4"]
def StoredTreeInvariant {Symbol : Type} {rank : Symbol → Nat}
    (t1 t2 : RankedTreeData Symbol rank) (state : UnifyState Symbol rank) : Prop :=
  state.tree1 = t1.substitute state.unifier.map ∧
  state.tree2 = t2.substitute state.unifier.map

-- ===================================================================
-- Example 8.4.2: Types for unification example
-- ===================================================================

/-- Example 8.4.2 (companion): Symbols used in the unification example:
function symbols f (binary), g (unary); constant a; and
variables x, y, z. -/
@[blueprint "chap8__example_8_4_2"]
inductive ExSym : Type where
  | f : ExSym
  | g : ExSym
  | a : ExSym
  | x : ExSym
  | y : ExSym
  | z : ExSym
  deriving DecidableEq

/-- Example 8.4.2 (companion): A simple tree type built from ExSym, where
each node has a label and a list of children. This serves as the
concrete tree representation for the unification example. -/
@[blueprint "chap8__example_8_4_2"]
inductive ExTree : Type where
  /-- A leaf node with a symbol label -/
  | leaf : ExSym → ExTree
  /-- An internal node with a symbol label and children -/
  | node : ExSym → List ExTree → ExTree

/-- Example 8.4.2 (companion): A substitution pair (t/x) recording a single
substitution step: replace variable varIdx with the subtree. -/
@[blueprint "chap8__example_8_4_2"]
structure SubstitutionPair : Type where
  /-- The replacement subtree -/
  subtree : ExTree
  /-- The variable being replaced (as ExSym) -/
  variable_ : ExSym

/-- Look up one variable image in an explicit finite substitution list. -/
@[blueprint "chap8__example_8_4_2"]
def exSubstitutionImage (pairs : List SubstitutionPair) (v : ExSym) : ExTree :=
  match pairs with
  | [] => .leaf v
  | p :: rest => if v = p.variable_ then p.subtree else exSubstitutionImage rest v

/-- Simultaneous substitution on the example trees fixes rigid symbols and
    replaces only x, y and z; replacement values are not substituted again. -/
@[blueprint "chap8__example_8_4_2"]
def exApplySubstitution (pairs : List SubstitutionPair) : ExTree → ExTree
  | .leaf .x => exSubstitutionImage pairs .x
  | .leaf .y => exSubstitutionImage pairs .y
  | .leaf .z => exSubstitutionImage pairs .z
  | .leaf v => .leaf v
  | .node f children => .node f (children.map (exApplySubstitution pairs))

/-- Old-then-new composition: apply the new substitution to the old images,
    then retain new bindings for variables absent from the old domain. -/
@[blueprint "chap8__example_8_4_2"]
def exComposeSubstitution (old new : List SubstitutionPair) : List SubstitutionPair :=
  old.map (fun p => { p with subtree := exApplySubstitution new p.subtree }) ++
    new.filter (fun p => !old.any (fun q => decide (q.variable_ = p.variable_)))

/-- One-based address lookup in the example's explicit ordered trees. -/
@[blueprint "chap8__example_8_4_2"]
def exSubtreeAt : ExTree → TreeAddr → Option ExTree
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node _ _, 0 :: _ => none
  | .node _ children, (i + 1) :: rest =>
      children[i]?.bind (fun child => exSubtreeAt child rest)

/-- Ranks of the example's rigid symbols; x, y and z are encoded as variables. -/
@[blueprint "chap8__example_8_4_2"]
def exRank : ExSym → Nat
  | .f => 2
  | .g => 1
  | _ => 0

/-- Translate the displayed ordered trees into the algorithm's ranked carrier.
    Malformed rigid nodes are rejected; x, y, z use distinct names 0, 1, 2. -/
@[blueprint "chap8__example_8_4_2"]
def exToRankedTree : ExTree → Option (RankedTreeData ExSym exRank)
  | .leaf .x => some (.var 0)
  | .leaf .y => some (.var 1)
  | .leaf .z => some (.var 2)
  | .leaf .a => some (.node .a (fun i => Fin.elim0 i))
  | .node .f [s, t] => do
      let s' ← exToRankedTree s
      let t' ← exToRankedTree t
      pure (.node .f (fun i => if i.val = 0 then s' else t'))
  | .node .g [s] => do
      let s' ← exToRankedTree s
      pure (.node .g (fun _ => s'))
  | _ => none

/-- Example 8.4.2 (companion): A trace of the unification algorithm's
execution on the Example 8.4.2 inputs, recording each address, local pair,
completed pair of stores and accumulated substitution. -/
@[blueprint "chap8__example_8_4_2"]
structure ExampleUnificationTrace : Type where
  /-- Input tree t1 = f(x, f(x, y)) -/
  t1 : ExTree
  /-- Input tree t2 = f(g(y), f(g(a), z)) -/
  t2 : ExTree
  /-- First disagreement resolution: (g(y)/x) at node 1 -/
  step1 : SubstitutionPair
  /-- Second disagreement resolution: (a/y) at node 211 -/
  step2 : SubstitutionPair
  /-- Third disagreement resolution: (a/z) at node 22 -/
  step3 : SubstitutionPair
  /-- Addresses in the current stores, with one-based child indices. -/
  address1 : TreeAddr
  address2 : TreeAddr
  address3 : TreeAddr
  /-- Both stores after each completed paired update. -/
  stores1 : ExTree × ExTree
  stores2 : ExTree × ExTree
  stores3 : ExTree × ExTree
  /-- Accumulated substitutions after the first and second updates. -/
  unifier1 : List SubstitutionPair
  unifier2 : List SubstitutionPair
  /-- The final mgu: (g(a)/x, a/y, a/z) -/
  mgu : List SubstitutionPair
  /-- The unified tree: f(g(a), f(g(a), a)) -/
  unifiedTree : ExTree
  /-- Actual initialized root state and the returned state of its execution. -/
  initialState : UnifyState ExSym exRank
  finalState : UnifyState ExSym exRank

-- ===================================================================
-- Definition 8.4.4: Unification algorithm definitions
-- ===================================================================

/-- Finite identity map on ranked trees. -/
def FiniteTreeSubstitution.identity {Symbol : Type} {rank : Symbol → Nat} :
    FiniteTreeSubstitution Symbol rank where
  support := []
  map := RankedTreeData.var
  outsideSupport := by intros; rfl

/-- Replace exactly one variable; all other variables are fixed. -/
@[blueprint "chap8__definition_8_4_4"]
def FiniteTreeSubstitution.singleton {Symbol : Type} {rank : Symbol → Nat}
    (x : Nat) (t : RankedTreeData Symbol rank) : FiniteTreeSubstitution Symbol rank where
  support := [x]
  map y := if y = x then t else .var y
  outsideSupport := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [hy]

/-- Source composition: apply the old substitution first, then the new one. -/
def FiniteTreeSubstitution.compose {Symbol : Type} {rank : Symbol → Nat}
    (old new : FiniteTreeSubstitution Symbol rank) : FiniteTreeSubstitution Symbol rank where
  support := old.support ++ new.support
  map x := (old.map x).substitute new.map
  outsideSupport := by
    intro x hx
    have ho : x ∉ old.support := fun h => hx (List.mem_append_left _ h)
    have hn : x ∉ new.support := fun h => hx (List.mem_append_right _ h)
    rw [old.outsideSupport x ho]
    exact new.outsideSupport x hn

/-- Actual singleton selection. Invalid addresses or a rigid source label
    give none; a variable label and an actual opposing subtree give (t/x). -/
def rankedNewPair {Symbol : Type} {rank : Symbol → Nat}
    (t1 : RankedTreeData Symbol rank) (addr1 : TreeAddr)
    (t2 : RankedTreeData Symbol rank) (addr2 : TreeAddr) :
    Option (FiniteTreeSubstitution Symbol rank) :=
  match t1.labelAt addr1, t2.subtreeAt addr2 with
  | some (.variable x), some t => some (FiniteTreeSubstitution.singleton x t)
  | _, _ => none

/-- General operation bundle with explicit failure of partial tree selections. -/
@[blueprint "chap8__definition_8_4_4"]
structure SubstOpsCore (Tree : Type) (Addr : Type) (Subst : Type) where
  identity : Subst
  compose : Subst → Subst → Subst
  newPair : Tree → Addr → Tree → Addr → Option Subst
  subtreeAt : Tree → Addr → Option Tree

/-- Definition 8.4.4: concrete finite substitution operations and structural lookup. -/
@[blueprint "chap8__definition_8_4_4"]
def SubstOps (Symbol : Type) (rank : Symbol → Nat) :
    SubstOpsCore (RankedTreeData Symbol rank) TreeAddr (FiniteTreeSubstitution Symbol rank) where
  identity := FiniteTreeSubstitution.identity
  compose := FiniteTreeSubstitution.compose
  newPair := rankedNewPair
  subtreeAt := RankedTreeData.subtreeAt

/-- The initialized root call stores the two input values, the empty-address
    root, the finite identity substitution and the true success flag. -/
@[blueprint "chap8__definition_8_4_4"]
def initialUnifyState {Symbol : Type} {rank : Symbol → Nat}
    (t1 t2 : RankedTreeData Symbol rank) : UnifyState Symbol rank where
  tree1 := t1
  tree2 := t2
  node := some []
  unifier := (SubstOps Symbol rank).identity
  unifiable := true

/-- Definition 8.4.4: compose the old accumulated map with the new component,
    in that order, on every variable. -/
@[blueprint "chap8__definition_8_4_4"]
def composeSubstitution {Symbol : Type} {rank : Symbol → Nat}
    (unifier np : FiniteTreeSubstitution Symbol rank) : FiniteTreeSubstitution Symbol rank :=
  (SubstOps Symbol rank).compose unifier np

/-- Definition 8.4.4: select the source variable and opposing subtree from
    current trees, returning their singleton substitution when both exist. -/
@[blueprint "chap8__definition_8_4_4"]
def newPair {Symbol : Type} {rank : Symbol → Nat}
    (t1 : RankedTreeData Symbol rank) (addr1 : TreeAddr)
    (t2 : RankedTreeData Symbol rank) (addr2 : TreeAddr) :
    Option (FiniteTreeSubstitution Symbol rank) :=
  (SubstOps Symbol rank).newPair t1 addr1 t2 addr2

/-- Exhaustive structural occurrence checking compares variable names and
    examines every child of a rigid node. Nullary rigid nodes contain no variable. -/
@[blueprint "chap8__definition_8_4_4"]
def treeOccursBool {Symbol : Type} {rank : Symbol → Nat} (x : Nat) :
    RankedTreeData Symbol rank → Bool
  | .var y => x == y
  | .node _ children => (List.ofFn fun i => treeOccursBool x (children i)).any id

/-- Definition 8.4.4 (companion): test whether the actual variable at addr1
    occurs anywhere in the opposing subtree at addr2. Invalid selections and
    a nonvariable first label return false; newPair separately rejects them. -/
@[blueprint "chap8__definition_8_4_4"]
def occurCheck {Symbol : Type} {rank : Symbol → Nat}
    (t1 : RankedTreeData Symbol rank) (addr1 : TreeAddr)
    (t2 : RankedTreeData Symbol rank) (addr2 : TreeAddr) :
    Bool :=
  match t1.labelAt addr1, t2.subtreeAt addr2 with
  | some (.variable x), some t => treeOccursBool x t
  | _, _ => false

/-- Definition 8.4.4: Procedure test-and-substitute performs the occur
    check, swapping operands when the second tree supplies the variable.
    A repair composes the old unifier with the singleton and substitutes
    simultaneously throughout both stored trees. -/
@[blueprint "chap8__definition_8_4_4" (main := true)]
def testAndSubstitute {Symbol : Type} {rank : Symbol → Nat}
    (state : UnifyState Symbol rank) :
    UnifyState Symbol rank :=
  let nav := TreeNav Symbol rank
  match state.node with
  | none => state
  | some addr =>
    let isVar1 := nav.isVariable state.tree1 addr
    let isVar2 := nav.isVariable state.tree2 addr
    if !isVar1 && !isVar2 then
      -- Fatal disagreement kind (i): both non-variables and unequal
      { state with unifiable := false }
    else
      -- At least one is a variable; determine which tree has the
      -- variable and which has the opposing subtree
      let (varTree, varAddr, oppTree, oppAddr) :=
        if isVar1 then (state.tree1, addr, state.tree2, addr)
        else (state.tree2, addr, state.tree1, addr)
      if occurCheck varTree varAddr oppTree oppAddr then
        -- Fatal disagreement kind (ii): occur check failure
        { state with unifiable := false }
      else
        -- Repairable disagreement: create newpair and update
        match newPair varTree varAddr oppTree oppAddr with
        | none => { state with unifiable := false }
        | some np =>
          let newUnifier := composeSubstitution state.unifier np
          let newTree1 := nav.doSubstitution state.tree1 np
          let newTree2 := nav.doSubstitution state.tree2 np
          { state with tree1 := newTree1, tree2 := newTree2, unifier := newUnifier }

/-- Distinct variable names of a finite ranked tree, obtained by structural
    traversal of every child. Rigid nullary symbols contribute no names. -/
@[blueprint "chap8__theorem_8_4_1"]
def treeVarNames {Symbol : Type} {rank : Symbol → Nat} :
    RankedTreeData Symbol rank → List Nat
  | .var x => [x]
  | .node _ children => (List.ofFn fun i => treeVarNames (children i)).flatten.eraseDups

/-- The primary termination measure counts the union of variable names in
    both current stores. A name shared by the two trees is counted once. -/
@[blueprint "chap8__theorem_8_4_1"]
def varCount {Symbol : Type} {rank : Symbol → Nat}
    (t1 t2 : RankedTreeData Symbol rank) : Nat :=
  (treeVarNames t1 ++ treeVarNames t2).eraseDups.length

/-- The two work phases of a recursive traversal: visit a node, or continue
    its child loop. The loop cursor is zero-based; tree addresses are one-based. -/
@[blueprint "chap8__theorem_8_4_1"]
inductive UnifyFrame where
  | visit (node : TreeAddr)
  | children (parent : TreeAddr) (nextChild : Nat)

/-- A visit has weight twice its current subtree size. A child-loop frame
    has weight one plus twice the total size of its remaining child subtrees.
    The extra unit separates entry, child calls and loop advancement. -/
@[blueprint "chap8__theorem_8_4_1"]
def frameWeight {Symbol : Type} {rank : Symbol → Nat}
    (state : UnifyState Symbol rank) : UnifyFrame → Nat
  | .visit u => 2 * ((state.tree1.subtreeAt u).map
      (fun t => (preorderAddresses t).length)).getD 0
  | .children u next => 1 + 2 *
      (match state.tree1.subtreeAt u with
       | some (.node _ children) =>
           (List.ofFn fun i => if next ≤ i.val then
             (preorderAddresses (children i)).length else 0).sum
       | _ => 0)

/-- The lexicographic recursion measure combines the distinct-name union
    of both stores with the size of the current traversal work frame. -/
@[blueprint "chap8__theorem_8_4_1"]
def unifyMeasure {Symbol : Type} {rank : Symbol → Nat}
    (state : UnifyState Symbol rank) (frame : UnifyFrame) : Nat × Nat :=
  (varCount state.tree1 state.tree2, frameWeight state frame)

/-- Internal return invariant supporting the well-founded child loop:
    the union of variable names never grows, and equal counts imply that
    the first stored tree is unchanged. -/
@[blueprint "chap8__definition_8_4_4"]
def UnifyReturnInvariant {Symbol : Type} {rank : Symbol → Nat}
    (before after : UnifyState Symbol rank) : Prop :=
  varCount after.tree1 after.tree2 ≤ varCount before.tree1 before.tree2 ∧
  (varCount after.tree1 after.tree2 = varCount before.tree1 before.tree2 →
    after.tree1 = before.tree1)

/-- Internal return invariants compose across consecutive procedure steps. -/
@[blueprint "chap8__definition_8_4_4"]
theorem unifyReturnInvariant_trans {Symbol : Type} {rank : Symbol → Nat}
    {a b c : UnifyState Symbol rank}
    (hab : UnifyReturnInvariant a b) (hbc : UnifyReturnInvariant b c) :
    UnifyReturnInvariant a c

/-- A local repair or failure preserves the internal termination invariant. -/
@[attach_debt, blueprint "chap8__definition_8_4_4"]
theorem testAndSubstitute_returnInvariant {Symbol : Type} {rank : Symbol → Nat}
    (state : UnifyState Symbol rank) :
    UnifyReturnInvariant state (testAndSubstitute state)

/-- The unbounded node/child-loop worker compares actual labels, repairs at
    most once per visit, then visits children left-to-right. Its proof component
    supplies the return invariant needed for the next recursive child frame. -/
@[blueprint "chap8__definition_8_4_4"]
def unifyRun {Symbol : Type} {rank : Symbol → Nat} [DecidableEq Symbol]
    (state : UnifyState Symbol rank) (frame : UnifyFrame) :
    {result : UnifyState Symbol rank // UnifyReturnInvariant state result} :=
  if !state.unifiable then ⟨state, ⟨Nat.le_refl _, fun _ => rfl⟩⟩
  else
    match frame with
    | .visit addr =>
      let current := { state with node := some addr }
      have hCurrent : UnifyReturnInvariant state current :=
        ⟨Nat.le_refl _, fun _ => rfl⟩
      match hLabels : (current.tree1.labelAt addr, current.tree2.labelAt addr) with
      | (some a, some b) =>
        let prepared := if a = b then current else testAndSubstitute current
        have hPrepared : UnifyReturnInvariant state prepared := by
          dsimp only [prepared]
          split
          · exact hCurrent
          · exact unifyReturnInvariant_trans hCurrent (testAndSubstitute_returnInvariant current)
        if !prepared.unifiable then ⟨prepared, hPrepared⟩
        else
          match hLeft : (TreeNav Symbol rank).left prepared.tree1 addr with
          | none => ⟨prepared, hPrepared⟩
          | some firstChild =>
            let result := unifyRun prepared (.children addr 0)
            ⟨result.val, unifyReturnInvariant_trans hPrepared result.property⟩
      | _ => ⟨{ current with unifiable := false }, ⟨Nat.le_refl _, fun _ => rfl⟩⟩
    | .children parent i =>
      match hParent : state.tree1.subtreeAt parent with
      | some (.node f children) =>
        if i < rank f then
          let child := parent ++ [i + 1]
          let childState := { state with node := some child }
          have hChild : UnifyReturnInvariant state childState :=
            ⟨Nat.le_refl _, fun _ => rfl⟩
          let returned := unifyRun childState (.visit child)
          let restored := { returned.val with node := some parent }
          have hRestored : UnifyReturnInvariant state restored :=
            unifyReturnInvariant_trans hChild returned.property
          if !restored.unifiable then ⟨restored, hRestored⟩
          else
            match hNext : (TreeNav Symbol rank).right restored.tree1 child with
            | none => ⟨restored, hRestored⟩
            | some nextChild =>
              let result := unifyRun restored (.children parent (i + 1))
              ⟨result.val, unifyReturnInvariant_trans hRestored result.property⟩
        else ⟨state, ⟨Nat.le_refl _, fun _ => rfl⟩⟩
      | _ => ⟨state, ⟨Nat.le_refl _, fun _ => rfl⟩⟩
termination_by unifyMeasure state frame
decreasing_by
  all_goals
    -- REPAIR(T8-18): proof pending
    sorry

/-- Definition 8.4.4: run the well-founded traversal at the supplied current
    node, preserving the caller's node reference on return. Decidable equality
    on rigid symbols implements the source's actual-label comparison. -/
@[blueprint "chap8__definition_8_4_4" (main := true)]
def unify {Symbol : Type} {rank : Symbol → Nat} [DecidableEq Symbol]
    (state : UnifyState Symbol rank) : UnifyState Symbol rank :=
  match state.node with
  | none => state
  | some addr => (unifyRun state (.visit addr)).val

/-- Definition 8.4.4: take two input values, initialize the root reference and
    identity unifier, and return the updated flag, unifier and first stored tree. -/
@[blueprint "chap8__definition_8_4_4" (main := true)]
def unification {Symbol : Type} {rank : Symbol → Nat} [DecidableEq Symbol]
    (t1 t2 : RankedTreeData Symbol rank) :
    UnificationResult (RankedTreeData Symbol rank) (FiniteTreeSubstitution Symbol rank) :=
  let finalState := unify (initialUnifyState t1 t2)
  { unifiable := finalState.unifiable
    unifier := finalState.unifier
    resultTree := finalState.tree1 }

-- ===================================================================
-- Example 8.4.2: Concrete unification example
-- ===================================================================

/-- Example 8.4.2: The input tree t1 = f(x, f(x, y)), built as
a concrete ExTree value. -/
@[blueprint "chap8__example_8_4_2" (main := true)]
def exTree_t1 : ExTree :=
  ExTree.node ExSym.f [
    ExTree.leaf ExSym.x,
    ExTree.node ExSym.f [
      ExTree.leaf ExSym.x,
      ExTree.leaf ExSym.y
    ]
  ]

/-- Example 8.4.2: The input tree t2 = f(g(y), f(g(a), z)), built
as a concrete ExTree value. -/
@[blueprint "chap8__example_8_4_2" (main := true)]
def exTree_t2 : ExTree :=
  ExTree.node ExSym.f [
    ExTree.node ExSym.g [ExTree.leaf ExSym.y],
    ExTree.node ExSym.f [
      ExTree.node ExSym.g [ExTree.leaf ExSym.a],
      ExTree.leaf ExSym.z
    ]
  ]

/-- Example 8.4.2: The most general unifier (g(a)/x, a/y, a/z)
as a list of substitution pairs recording each step. -/
@[blueprint "chap8__example_8_4_2" (main := true)]
def exMgu_8_4_2 : List SubstitutionPair :=
  [ { subtree := ExTree.node ExSym.g [ExTree.leaf ExSym.a],
      variable_ := ExSym.x },
    { subtree := ExTree.leaf ExSym.a,
      variable_ := ExSym.y },
    { subtree := ExTree.leaf ExSym.a,
      variable_ := ExSym.z } ]

/-- Example 8.4.2: The unified tree f(g(a), f(g(a), a)), the most
common form after applying the mgu to t1. -/
@[blueprint "chap8__example_8_4_2" (main := true)]
def exUnifiedTree_8_4_2 : ExTree :=
  ExTree.node ExSym.f [
    ExTree.node ExSym.g [ExTree.leaf ExSym.a],
    ExTree.node ExSym.f [
      ExTree.node ExSym.g [ExTree.leaf ExSym.a],
      ExTree.leaf ExSym.a
    ]
  ]

/-- Example 8.4.2: Demonstration of the unification algorithm on
    t1 and t2, with explicit current addresses, paired stores and accumulated
    substitutions, producing mgu (g(a)/x, a/y, a/z). -/
@[blueprint "chap8__example_8_4_2" (main := true)]
def exampleUnification_8_4_2 : ExampleUnificationTrace :=
  let initial := initialUnifyState
    ((exToRankedTree exTree_t1).get (by decide))
    ((exToRankedTree exTree_t2).get (by decide))
  {
  t1 := exTree_t1
  t2 := exTree_t2
  step1 := {
    subtree := ExTree.node ExSym.g [ExTree.leaf ExSym.y],
    variable_ := ExSym.x
  }
  step2 := {
    subtree := ExTree.leaf ExSym.a,
    variable_ := ExSym.y
  }
  step3 := {
    subtree := ExTree.leaf ExSym.a,
    variable_ := ExSym.z
  }
  address1 := [1]
  address2 := [2, 1, 1]
  address3 := [2, 2]
  stores1 := (
    .node .f [.node .g [.leaf .y], .node .f [.node .g [.leaf .y], .leaf .y]],
    .node .f [.node .g [.leaf .y], .node .f [.node .g [.leaf .a], .leaf .z]])
  stores2 := (
    .node .f [.node .g [.leaf .a], .node .f [.node .g [.leaf .a], .leaf .a]],
    .node .f [.node .g [.leaf .a], .node .f [.node .g [.leaf .a], .leaf .z]])
  stores3 := (
    .node .f [.node .g [.leaf .a], .node .f [.node .g [.leaf .a], .leaf .a]],
    .node .f [.node .g [.leaf .a], .node .f [.node .g [.leaf .a], .leaf .a]])
  unifier1 := [{ subtree := .node .g [.leaf .y], variable_ := .x }]
  unifier2 := [{ subtree := .node .g [.leaf .a], variable_ := .x },
    { subtree := .leaf .a, variable_ := .y }]
  mgu := exMgu_8_4_2
  unifiedTree := exUnifiedTree_8_4_2
  initialState := initial
  finalState := unify initial
}

/-- The stored inputs encode exactly the initialized stores, with the root
    reference, identity accumulator and successful initial flag. The recorded
    final state is the actual run from this initialization. -/
@[blueprint "chap8__example_8_4_2"]
theorem exampleUnification_8_4_2_run :
    let t := exampleUnification_8_4_2
    exToRankedTree t.t1 = some t.initialState.tree1 ∧
    exToRankedTree t.t2 = some t.initialState.tree2 ∧
    t.initialState = initialUnifyState t.initialState.tree1 t.initialState.tree2 ∧
    t.finalState = unify t.initialState ∧
    unification t.initialState.tree1 t.initialState.tree2 =
      { unifiable := t.finalState.unifiable, unifier := t.finalState.unifier,
        resultTree := t.finalState.tree1 }

/-- The three actual disagreements occur at 1, 211 and 22 in the current
    stores. At 22 the variable z is in the second store, requiring swapped roles. -/
@[blueprint "chap8__example_8_4_2"]
theorem exampleUnification_8_4_2_disagreements :
    let t := exampleUnification_8_4_2
    exSubtreeAt t.t1 t.address1 = some (.leaf t.step1.variable_) ∧
    exSubtreeAt t.t2 t.address1 = some t.step1.subtree ∧
    exSubtreeAt t.stores1.1 t.address2 = some (.leaf t.step2.variable_) ∧
    exSubtreeAt t.stores1.2 t.address2 = some t.step2.subtree ∧
    exSubtreeAt t.stores2.1 t.address3 = some t.step3.subtree ∧
    exSubtreeAt t.stores2.2 t.address3 = some (.leaf t.step3.variable_)

/-- Each recorded pair of stores is the completed simultaneous update of both
    previous stores, and both final stores are the displayed common tree. -/
@[blueprint "chap8__example_8_4_2"]
theorem exampleUnification_8_4_2_updates :
    let t := exampleUnification_8_4_2
    t.stores1 = (exApplySubstitution [t.step1] t.t1,
      exApplySubstitution [t.step1] t.t2) ∧
    t.stores2 = (exApplySubstitution [t.step2] t.stores1.1,
      exApplySubstitution [t.step2] t.stores1.2) ∧
    t.stores3 = (exApplySubstitution [t.step3] t.stores2.1,
      exApplySubstitution [t.step3] t.stores2.2) ∧
    t.stores3 = (t.unifiedTree, t.unifiedTree)

/-- The accumulated substitutions use old-then-new composition, including
    replacing y inside the previously recorded image g(y) of x. -/
@[blueprint "chap8__example_8_4_2"]
theorem exampleUnification_8_4_2_composition :
    let t := exampleUnification_8_4_2
    exComposeSubstitution [] [t.step1] = t.unifier1 ∧
    exComposeSubstitution t.unifier1 [t.step2] = t.unifier2 ∧
    exComposeSubstitution t.unifier2 [t.step3] = t.mgu

-- ===================================================================
-- Lemma 8.4.3: Incremental unification of argument trees
-- ===================================================================

/-- Lemma 8.4.3 (companion): keep the first prefixLen.val arguments of the
    rigid root and pad the remaining positions by the given rank-zero symbol.
    Prefix zero is the all-constant tree; the full prefix keeps every argument.
    The padding constant may already occur in the trees. -/
@[blueprint "chap8__lemma_8_4_3"]
def partialArgTree {Symbol : Type} {rank : Symbol → Nat}
    (root : Symbol) (args : Fin (rank root) → RankedTreeData Symbol rank)
    (prefixLen : Fin (rank root + 1)) (padding : Symbol) (hPadding : rank padding = 0) :
    RankedTreeData Symbol rank :=
  let constant : RankedTreeData Symbol rank :=
    .node padding (fun i => Fin.elim0 (Fin.cast hPadding i))
  .node root (fun j => if j.val < prefixLen.val then args j else constant)

/-- Two finite ranked trees are unifiable by a finite-support substitution. -/
@[blueprint "chap8__lemma_8_4_3"]
def TreeUnifiable {Symbol : Type} {rank : Symbol → Nat}
    (t1 t2 : RankedTreeData Symbol rank) : Prop :=
  ∃ sigma : FiniteTreeSubstitution Symbol rank,
    t1.substitute sigma.map = t2.substitute sigma.map

/-- A finite-support MGU unifies the two trees, changes only their variables,
    and factors every finite-support unifier globally on all variable names.
    The support condition concerns actual changes, not extra fixed entries in
    a support list; factorization equates maps, not support-list certificates. -/
@[blueprint "chap8__lemma_8_4_3"]
def IsTreeMGU {Symbol : Type} {rank : Symbol → Nat}
    (sigma : FiniteTreeSubstitution Symbol rank)
    (t1 t2 : RankedTreeData Symbol rank) : Prop :=
  t1.substitute sigma.map = t2.substitute sigma.map ∧
  (∀ x, sigma.map x ≠ .var x → treeOccurs x t1 ∨ treeOccurs x t2) ∧
  ∀ tau : FiniteTreeSubstitution Symbol rank,
    t1.substitute tau.map = t2.substitute tau.map →
      ∃ theta : FiniteTreeSubstitution Symbol rank,
        tau.map = (composeSubstitution sigma theta).map

/-- The initialized example run succeeds with the displayed substitution,
    an input-support MGU factoring every finite-support unifier on all names.
    Both final stores are the displayed common tree and the respective input
    images. The displayed bindings fix every variable other than x, y and z. -/
@[attach_debt, blueprint "chap8__example_8_4_2"]
theorem exampleUnification_8_4_2_result :
    let t := exampleUnification_8_4_2
    let sigma := t.finalState.unifier
    t.finalState.unifiable = true ∧
    IsTreeMGU sigma t.initialState.tree1 t.initialState.tree2 ∧
    exToRankedTree (exSubstitutionImage t.mgu .x) = some (sigma.map 0) ∧
    exToRankedTree (exSubstitutionImage t.mgu .y) = some (sigma.map 1) ∧
    exToRankedTree (exSubstitutionImage t.mgu .z) = some (sigma.map 2) ∧
    (∀ x, 3 ≤ x → sigma.map x = .var x) ∧
    exToRankedTree t.unifiedTree = some t.finalState.tree1 ∧
    exToRankedTree t.unifiedTree = some t.finalState.tree2 ∧
    t.finalState.tree1 = t.initialState.tree1.substitute sigma.map ∧
    t.finalState.tree2 = t.initialState.tree2.substitute sigma.map

/-- Lemma 8.4.3: for any rank-zero padding constant, an MGU of the previous
    padded prefixes preserves unifiability of the next prefixes, and composing
    it with an MGU of the next substituted arguments gives an MGU of those
    next prefixes. The zero-based i names the source's argument i+1. -/
@[attach_debt, blueprint "chap8__lemma_8_4_3" (main := true)]
theorem incremental_unification {Symbol : Type} {rank : Symbol → Nat}
    (root padding : Symbol) (hPadding : rank padding = 0)
    (ss ts : Fin (rank root) → RankedTreeData Symbol rank)
    (i : Fin (rank root)) (sigma : FiniteTreeSubstitution Symbol rank)
    (h_mgu_prev : IsTreeMGU sigma
      (partialArgTree root ss ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ padding hPadding)
      (partialArgTree root ts ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ padding hPadding)) :
    let s := partialArgTree root ss ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ padding hPadding
    let t := partialArgTree root ts ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ padding hPadding
    (TreeUnifiable s t ↔
      TreeUnifiable (s.substitute sigma.map) (t.substitute sigma.map)) ∧
    (∀ theta : FiniteTreeSubstitution Symbol rank,
      IsTreeMGU theta ((ss i).substitute sigma.map) ((ts i).substitute sigma.map) →
        IsTreeMGU (composeSubstitution sigma theta) s t)

-- ===================================================================
-- Theorem 8.4.1: Correctness of the unification algorithm
-- ===================================================================

/-- The direct recursive calls of `unifyRun`, with the callee first.
    The visit case enters its prepared child loop; a child-loop frame visits
    the current child and, on successful return, advances in the updated tree.
    Accessibility of this relation states termination of these actual calls. -/
@[blueprint "chap8__theorem_8_4_1"]
def UnifyCall {Symbol : Type} {rank : Symbol → Nat} [DecidableEq Symbol]
    (callee caller : UnifyState Symbol rank × UnifyFrame) : Prop :=
  let state := caller.1
  state.unifiable = true ∧
    match caller.2 with
    | .visit addr =>
      let current := { state with node := some addr }
      match current.tree1.labelAt addr, current.tree2.labelAt addr with
      | some a, some b =>
        let prepared := if a = b then current else testAndSubstitute current
        prepared.unifiable = true ∧
          ((TreeNav Symbol rank).left prepared.tree1 addr).isSome = true ∧
          callee = (prepared, .children addr 0)
      | _, _ => False
    | .children parent i =>
      match state.tree1.subtreeAt parent with
      | some (.node f _) =>
        i < rank f ∧
          let child := parent ++ [i + 1]
          let childState := { state with node := some child }
          callee = (childState, .visit child) ∨
            let returned := (unifyRun childState (.visit child)).val
            let restored := { returned with node := some parent }
            restored.unifiable = true ∧
              ((TreeNav Symbol rank).right restored.tree1 child).isSome = true ∧
              callee = (restored, .children parent (i + 1))
      | _ => False

/-- Theorem 8.4.1: the actual initialized root run terminates, succeeds
    exactly for unifiable inputs, and returns a finite-support MGU with support
    bounded by the input variables and global factorization. Both completed
    stores are accumulated input images; on success the returned tree is their
    common image, with no changed variable remaining in either store.
    Termination is accessibility of the worker's direct recursive calls, not
    a claim that its retained caller address becomes `none`. The independent
    MGU-existence conclusion is stated as well as correctness of the output. -/
@[attach_debt, blueprint "chap8__theorem_8_4_1" (main := true)]
theorem unification_correctness
    {Symbol : Type} {rank : Symbol → Nat} [DecidableEq Symbol]
    (t1 t2 : RankedTreeData Symbol rank) :
    let initial := initialUnifyState t1 t2
    let finalState := unify initial
    let result := unification t1 t2
    Acc UnifyCall (initial, .visit []) ∧
    StoredTreeInvariant t1 t2 finalState ∧
    (result.unifiable = true ↔ TreeUnifiable t1 t2) ∧
    (result.unifiable = true →
      IsTreeMGU result.unifier t1 t2 ∧
      result.resultTree = t1.substitute result.unifier.map ∧
      result.resultTree = t2.substitute result.unifier.map ∧
      finalState.tree1 = result.resultTree ∧ finalState.tree2 = result.resultTree ∧
      (∀ x, result.unifier.map x ≠ .var x →
        ¬ treeOccurs x finalState.tree1 ∧ ¬ treeOccurs x finalState.tree2)) ∧
    (TreeUnifiable t1 t2 → ∃ sigma, IsTreeMGU sigma t1 t2)

-- ===================================================================
-- Local infinite unfolding of an occurs equation
-- ===================================================================

/-- An address labeling has a root and exactly the one-based children required
    by each rigid label. Missing nodes and variable leaves have no children.
    No finite-domain or bounded-depth condition is imposed. -/
@[blueprint "chap8__definition_8_4_4"]
def IsInfiniteRankedLabeling {Symbol : Type} (rank : Symbol → Nat)
    (labels : TreeAddr → Option (RankedTreeLabel Symbol)) : Prop :=
  (labels []).isSome = true ∧
    ∀ u i, (labels (u ++ [i])).isSome = true ↔
      match labels u with
      | none => False
      | some (.variable _) => False
      | some (.rigid f) => 0 < i ∧ i ≤ rank f

/-- Possibly infinite, finitely branching ranked trees presented by their
    labels at finite addresses. The domain is exactly the addresses with a
    present label. The rank law implies prefix closure and ordered children;
    equality is equality of all address labels, with proof fields irrelevant. -/
@[blueprint "chap8__definition_8_4_4"]
structure InfiniteRankedTree (Symbol : Type) (rank : Symbol → Nat) where
  labelAt : TreeAddr → Option (RankedTreeLabel Symbol)
  ranked : IsInfiniteRankedLabeling rank labelAt

end LCS.FOResolution.Unification.Algorithm
