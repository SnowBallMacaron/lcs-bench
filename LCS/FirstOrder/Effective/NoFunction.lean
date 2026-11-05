import LCS.FirstOrder.Effective.Syntax
import Attach
import LCS.FirstOrder.Effective.NoFunction.ProofsStamp

/-! # Executable no-function search

The runtime tree stores every ordered inference incidence and sequent label,
with separate records at each leaf. The source observation erases rule proofs,
not nodes or records. Simulation with the existing classical implementation is
conditional on its occurrence choices agreeing with the D3 leftmost policy.
-/

namespace LCS.FirstOrder.Effective

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen.Search.NoFunction (BranchRecords TermStream Init SearchState SearchTree)

/-- Definition 5.4.9: Ordered runtime nodes and branch-local formula histories. -/
@[blueprint "chap5__definition_5_4_9"]
inductive NoFunctionTree (L : Language) where
  | leaf (label : Sequent L) (records : BranchRecords L)
  | one (label : Sequent L) (child : NoFunctionTree L)
  | two (label : Sequent L) (left right : NoFunctionTree L)

/-- Definition 5.4.9: Both global term snapshots and the availability cursor,
together with the entire finite runtime tree. Repeated terms occupy distinct positions. -/
@[blueprint "chap5__definition_5_4_9"]
structure NoFunctionState (L : Language) where
  tree : NoFunctionTree L
  TERM0 : List (Term L)
  TERM1 : List (Term L)
  availNext : Nat

/-- Invalid supplied states fail explicitly when an eigenvariable is unavailable
or a capture-free substitution side condition is violated. -/
@[blueprint "chap5__definition_5_4_9"]
inductive NoFunctionError where
  | unavailableVariable
  | capture
  deriving Repr, DecidableEq

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Observe all source labels, ordered edges and leaf histories. -/
def NoFunctionTree.ofSource {L : Language} : {s : Sequent L} → SearchTree s → NoFunctionTree L
  | _, .leaf s r => .leaf s r
  | s, .onePremise _ t => .one s (ofSource t)
  | s, .twoPremise _ l r => .two s (ofSource l) (ofSource r)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Observe a source tree and its global state without discarding any stored history. -/
def noFunctionObserve {L : Language} {supply : TermStream L} {s : Sequent L}
    (tree : SearchTree s) (st : SearchState L supply) : NoFunctionState L :=
  ⟨NoFunctionTree.ofSource tree, st.TERM0, st.TERM1, st.availNext⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- D3 compatibility of the existing classical split with the executable
leftmost occurrence policy. This is a condition on the old choice-selected
realization; it is not asserted for an arbitrary classical choice function. -/
def NoFunctionSourcePolicy (p : EffectivePresentation) : Prop :=
  ∀ (xs : List (FormulaN p.toLanguage)) (A : FormulaN p.toLanguage) (h : A ∈ xs),
    ∃ r : OccurrenceSplit xs, splitOccurrence A xs = some r ∧
      (LCS.FirstOrder.Gentzen.Search.NoFunction.splitListAt xs A h).val = (r.prefix, r.suffix)

/-- Definition 5.4.9: Stage zero preserves the supplied term list verbatim
and allocates one empty history per list position at the root. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionInit {L : Language} (seq : Sequent L) (terms : List (Term L)) : NoFunctionState L :=
  let forms := List.replicate terms.length []
  ⟨.leaf seq ⟨forms, forms⟩, terms, terms, 0⟩

/-- Definition 5.4.9: Commit each branch's FORM₁ and pad newly appended term
positions with empty histories. -/
@[blueprint "chap5__definition_5_4_9"]
def NoFunctionTree.commit {L : Language} (n : Nat) : NoFunctionTree L → NoFunctionTree L
  | .leaf s r =>
    let forms := r.form1 ++ List.replicate (n - r.form1.length) []
    .leaf s ⟨forms, forms⟩
  | .one s t => .one s (commit n t)
  | .two s l r => .two s (commit n l) (commit n r)

/-- All leaves, retaining duplicate labels as separate branch occurrences. -/
@[blueprint "chap5__definition_5_4_9"]
def NoFunctionTree.leaves {L : Language} : NoFunctionTree L → List (Sequent L × BranchRecords L)
  | .leaf s r => [(s,r)]
  | .one _ t => t.leaves
  | .two _ l r => l.leaves ++ r.leaves

/-- Extend only existing leaves, preserving all original internal nodes and order. -/
@[blueprint "chap5__definition_5_4_9"]
def NoFunctionTree.mapLeaves {L : Language}
    (f : Sequent L → BranchRecords L → Except NoFunctionError (NoFunctionTree L)) :
    NoFunctionTree L → Except NoFunctionError (NoFunctionTree L)
  | .leaf s r => f s r
  | .one s t => do return .one s (← t.mapLeaves f)
  | .two s l r => do return .two s (← l.mapLeaves f) (← r.mapLeaves f)

/-- One principal-formula application at a nonaxiom leaf. Extended ∀:left
and ∃:right use every unused TERM₀ position, preserving repetitions and updating
only that branch's FORM₁. Eigenvariable rules receive the grow call's shared y. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionGrowLeaf {p : EffectivePresentation} (left : Bool)
    (A : FormulaN p.toLanguage) (terms : List (Term p.toLanguage)) (y : Option Nat)
    (s : Sequent p.toLanguage) (r : BranchRecords p.toLanguage) :
    Except NoFunctionError (NoFunctionTree p.toLanguage) := do
  if axiomDecide s then return .leaf s r
  let xs := if left then s.antecedent else s.succedent
  match splitOccurrence A xs with
  | none => return .leaf s r
  | some pos =>
    let pre := pos.prefix
    let post := pos.suffix
    let unary := fun ant suc records => NoFunctionTree.one s (.leaf ⟨ant,suc⟩ records)
    let binary := fun a b c d => NoFunctionTree.two s (.leaf ⟨a,b⟩ r) (.leaf ⟨c,d⟩ r)
    match left, A with
    | true, .conj B C => return unary (pre ++ [B,C] ++ post) s.succedent r
    | true, .disj B C => return binary (pre ++ [B] ++ post) s.succedent (pre ++ [C] ++ post) s.succedent
    | true, .impl B C => return binary (pre ++ post) (B :: s.succedent) (C :: (pre ++ post)) s.succedent
    | true, .neg B => return unary (pre ++ post) (B :: s.succedent) r
    | false, .conj B C => return binary s.antecedent (pre ++ [B] ++ post) s.antecedent (pre ++ [C] ++ post)
    | false, .disj B C => return unary s.antecedent (pre ++ [B,C] ++ post) r
    | false, .impl B C => return unary (B :: s.antecedent) (C :: (pre ++ post)) r
    | false, .neg B => return unary (B :: s.antecedent) (pre ++ post) r
    | true, .all x B | false, .ex x B =>
      let selected := (terms.mapIdx fun i t => (i,t)).filter fun it =>
        !((r.form0[it.1]?).getD []).any (fun F => formulaEq F A)
      if selected.isEmpty then return .leaf s r
      if !(selected.all fun it => freeForDecide it.2 x B) then throw .capture
      let instances := selected.map fun it => formulaSubstN B it.2 x
      let records := selected.foldl (fun acc it =>
        LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState.appendFORM1 acc it.1 A) r
      if left then return unary (pre ++ instances ++ [A] ++ post) s.succedent records
      else return unary s.antecedent (pre ++ instances ++ [A] ++ post) records
    | true, .ex x B | false, .all x B =>
      match y with
      | none => throw .unavailableVariable
      | some v =>
        if !(freeForDecide (.var v) x B) then throw .capture
        let instBody := formulaSubstN B (.var v) x
        if left then return unary (pre ++ [instBody] ++ post) s.succedent r
        else return unary s.antecedent (pre ++ [instBody] ++ post) r
    | _, _ => return .leaf s r

/-- Apply one principal formula across the current subtree. An eigenvariable
is read once and appended once when at least one nonaxiom leaf is eligible;
all eligible leaves use that same variable. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionGrow {p : EffectivePresentation} (entries : Nat → Option (Term p.toLanguage))
    (left : Bool) (A : FormulaN p.toLanguage) (st : NoFunctionState p.toLanguage) :
    Except NoFunctionError (NoFunctionState p.toLanguage) := do
  let eigen := match left, A with | true, .ex _ _ | false, .all _ _ => true | _, _ => false
  let eligible := st.tree.leaves.any fun leaf =>
    !axiomDecide leaf.1 && (if left then leaf.1.antecedent else leaf.1.succedent).any (fun F => formulaEq F A)
  if eigen && eligible then
    let forbidden := st.tree.leaves.flatMap fun leaf =>
      (leaf.1.antecedent ++ leaf.1.succedent).flatMap formulaFreeVarIndices
    match freshVariableAt entries st.availNext forbidden with
    | none => throw .unavailableVariable
    | some y =>
      let tree ← st.tree.mapLeaves (noFunctionGrowLeaf left A st.TERM0 (some y))
      return { st with tree := tree, TERM1 := st.TERM1 ++ [.var y], availNext := st.availNext + 1 }
  else
    let tree ← st.tree.mapLeaves (noFunctionGrowLeaf left A st.TERM0 none)
    return { st with tree := tree }

/-- Expand each original leaf left to right. Within a leaf, visit its original
antecedent formulae and then its original succedent formulae in list order.
Newly constructed leaves are not new outer-loop entries in the current round. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionExpand {p : EffectivePresentation} (entries : Nat → Option (Term p.toLanguage)) :
    NoFunctionTree p.toLanguage → NoFunctionState p.toLanguage →
      Except NoFunctionError (NoFunctionState p.toLanguage)
  | .leaf s r, st => do
    if axiomDecide s then return {st with tree := .leaf s r}
    let start := {st with tree := .leaf s r}
    let l ← s.antecedent.foldlM (fun acc A => noFunctionGrow entries true A acc) start
    s.succedent.foldlM (fun acc A => noFunctionGrow entries false A acc) l
  | .one s t, st => do
    let out ← noFunctionExpand entries t st
    return {out with tree := .one s out.tree}
  | .two s l r, st => do
    let outL ← noFunctionExpand entries l st
    let outR ← noFunctionExpand entries r outL
    return {outR with tree := .two s outL.tree outR.tree}

/-- Definition 5.4.9: One executable round, including the final global and
branch-local commits. TERM₀ remains the fixed instance snapshot throughout
all expansions in the round. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionRound {p : EffectivePresentation} (entries : Nat → Option (Term p.toLanguage))
    (st : NoFunctionState p.toLanguage) : Except NoFunctionError (NoFunctionState p.toLanguage) := do
  let out ← noFunctionExpand entries st.tree st
  return {out with tree := out.tree.commit out.TERM1.length, TERM0 := out.TERM1}

/-- Definition 5.4.9: Iterate complete executable rounds from the supplied
initial term list and availability stream. The input list is never deduplicated. -/
@[blueprint "chap5__definition_5_4_9"]
def noFunctionSearch {p : EffectivePresentation} (seq : Sequent p.toLanguage)
    (terms : List (Term p.toLanguage)) (entries : Nat → Option (Term p.toLanguage)) :
    Nat → Except NoFunctionError (NoFunctionState p.toLanguage)
  | 0 => .ok (noFunctionInit seq terms)
  | k + 1 => do noFunctionRound entries (← noFunctionSearch seq terms entries k)

/-- Definition 5.4.9: Under D3-compatible occurrence choices, every executable
stage of every source-admissible no-function initialization succeeds and has
exactly the source stage's ordered labels, leaf records, global term snapshots,
and stream cursor. Admissibility allows repeated initial terms. -/
theorem noFunctionSearch_spec {p : EffectivePresentation}
    (hNoEq : p.toLanguage.hasEquality = false)
    (hNoFunc : p.toLanguage.funSymbols → False)
    (policy : NoFunctionSourcePolicy p)
    (seq : Sequent p.toLanguage)
    (hFB : LCS.FirstOrder.Gentzen.Hintikka.crossNoFreeBound seq)
    (initial : Init seq) (k : Nat) :
    noFunctionSearch seq initial.term0 initial.avail0.entries k =
      .ok (let out := LCS.FirstOrder.Gentzen.Search.NoFunction.search hNoEq hNoFunc seq hFB initial k
        noFunctionObserve out.1 out.2) := by
  -- REPAIR(T151): proof pending
  sorry

end LCS.FirstOrder.Effective
