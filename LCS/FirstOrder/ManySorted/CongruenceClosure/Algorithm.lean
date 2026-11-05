import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.CongruenceClosure
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm.ProofsStamp

/-! # FirstOrder.ManySorted.CongruenceClosure.Algorithm
    Formalization of Chapter 10, Subsection 10.6.6 (Computing the
    Congruence Closure).

    Sorted specifications for the Nelson-Oppen algorithm, ordinary
    two-block UNION, and the extensional R₁/R₂/R₃ lemma.
    Effective MERGE and the driver have no computable realization:
    deferred (OD-A17). SQ45 initialization remains open.

    Builds on §10.6 graph/congruence machinery
    (LCS.FirstOrder.ManySorted.CongruenceClosure).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm

open LCS.FirstOrder.ManySorted

-- ===================================================================
-- Definition 10.6.4: Partition / UNION / FIND model
-- ===================================================================

/-- Definition 10.6.4 (companion): The partition representing the
equivalence relation `R` — the set of its equivalence classes
`[u] = {w | R u w}`. An equivalence relation is operated on through this
partition (the set-of-classes view that `UNION`/`FIND` act on). -/
@[blueprint "chap10__definition_10_6_4"]
def msPartitionOf (G : MSLabeledGraph) (R : G.Node → G.Node → Prop) :
    Set (Set G.Node) :=
  fun B => ∃ u : G.Node, B = (fun w => R u w)

/-- Definition 10.6.4 (companion): The equivalence class
`[u] = {w | R u w}`, the block of the partition containing `u` (all nodes
equivalent to `u` under the current relation `R`). -/
@[blueprint "chap10__definition_10_6_4"]
def msEquivClass (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u : G.Node) : Set G.Node :=
  fun w => R u w

/-- Definition 10.6.4 (companion): ordinary two-block UNION. For an
 equivalence relation `R`, retain every old pair and join precisely the
 blocks of `u` and `v`. Other blocks are unchanged. -/
@[blueprint "chap10__definition_10_6_4"]
def msUnion (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u v : G.Node) : G.Node → G.Node → Prop :=
  fun a b => R a b ∨ (R a u ∧ R v b) ∨ (R a v ∧ R u b)

/-- Ordinary UNION is the least equivalence extension joining the selected
blocks, and preserves the class of every node outside those blocks. -/
@[attach_debt, blueprint "chap10__definition_10_6_4"]
theorem msUnion_spec (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (hR : Equivalence R) (u v : G.Node) :
    Equivalence (msUnion G R u v) ∧
    (∀ a b, R a b → msUnion G R u v a b) ∧ msUnion G R u v u v ∧
    (∀ S, Equivalence S → (∀ a b, R a b → S a b) → S u v →
      ∀ a b, msUnion G R u v a b → S a b) ∧
    (∀ a, ¬ R a u → ¬ R a v → ∀ b, msUnion G R u v a b ↔ R a b)

/-- Definition 10.6.4 (companion): `FIND(u)` returns the unique name
(representative) of the class of `u`, modelled as the class itself
`{w | R u w}`; two nodes have the same `FIND` iff their classes coincide. -/
@[blueprint "chap10__definition_10_6_4"]
def msFindClass (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u : G.Node) : Set G.Node :=
  msEquivClass G R u

/-- Definition 10.6.4 (companion): the `FIND`-comparison `FIND(u) = FIND(v)`:
true iff `u` and `v` are currently equivalent (in the same class). When
`R` is an equivalence relation, this is exactly equality of the names
returned by `msFindClass`; used as the guard test of `msMerge` and
`msCongruentPairs`. -/
@[blueprint "chap10__definition_10_6_4"]
def msSameClass (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  R u v

-- ===================================================================
-- Definition 10.6.4: the CONGRUENT function
-- ===================================================================

/-- Definition 10.6.4 (companion): the guard `if Λ(u) = Λ(v)` of
`CONGRUENT`. The test can only succeed when `u` and `v` carry the same
label; if the labels differ `CONGRUENT` returns false. This is the
standalone label-equality test. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruentLabelGuard (G : MSLabeledGraph) (u v : G.Node) : Prop :=
  G.Lambda u = G.Lambda v

/-- Definition 10.6.4 (companion): the value `n = |w|` where
`r(Λ(u)) = (w, s)` — the number of successors (arity) determined by the
rank of `u`'s label, the loop bound `for i := 1 to n` of `CONGRUENT`. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruentArity (G : MSLabeledGraph) (u : G.Node) : Nat :=
  (G.Sigma.rank (G.Lambda u)).1.length

/-- Definition 10.6.4 (companion): the loop
`for i := 1 to n do if FIND(u[i]) ≠ FIND(v[i]) then flag := false`: the
conjunction over all successor indices `i` that the `i`-th successors
`u[i]`, `v[i]` are in the same class; false as soon as one pair is
inequivalent. When `h : |w_u| = |w_v|`, the index `i` of `u`'s domain is
transported to `v`'s by `Fin.cast h i`. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruentSuccessorLoop (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (u v : G.Node)
    (h : (G.Sigma.rank (G.Lambda u)).1.length =
      (G.Sigma.rank (G.Lambda v)).1.length) : Prop :=
  ∀ i : Fin (G.Sigma.rank (G.Lambda u)).1.length,
    msSameClass G R (G.delta u i) (G.delta v (Fin.cast h i))

/-- Definition 10.6.4 (the function `CONGRUENT(R, u, v)` as a `Prop`): `u`
and `v` are congruent iff their labels are equal and, with `n` the arity
of the shared label, `FIND(u[i]) = FIND(v[i])` for every successor index
`i` (the flag computed by the loop). The `Prop` is false when the labels
differ. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruent (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  G.Lambda u = G.Lambda v ∧
    ∃ h : (G.Sigma.rank (G.Lambda u)).1.length =
        (G.Sigma.rank (G.Lambda v)).1.length,
      ∀ i : Fin (G.Sigma.rank (G.Lambda u)).1.length,
        msSameClass G R (G.delta u i) (G.delta v (Fin.cast h i))

/-- Definition 10.6.4 (companion): the boolean flag returned by
`CONGRUENT`, true iff `Λ(u) = Λ(v)` and `FIND(u[i]) = FIND(v[i])` for all
`i` in `1..n`; the result value `CONGRUENT := flag`. Named separately so
the result-flag concept has its own declaration. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruentFlag (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  msCongruent G R u v

-- ===================================================================
-- Definition 10.6.4: the MERGE procedure
-- ===================================================================

/-- Definition 10.6.4 (companion): `X` = the union of the predecessor sets
`P_x` of all nodes `x` in `[u]`, the equivalence class of `u` (using the
core module's `G.predecessors`). The set of nodes that are predecessors of
some member of `u`'s class. -/
@[blueprint "chap10__definition_10_6_4"]
def msPredecessorUnionX (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (u : G.Node) : Set G.Node :=
  fun p => ∃ x : G.Node, msEquivClass G R u x ∧ G.predecessors x p

/-- Definition 10.6.4 (companion): `Y` = the union of the predecessor sets
`P_y` of all nodes `y` in `[v]`, the equivalence class of `v`. Same shape
as `msPredecessorUnionX` but for the class of `v`. -/
@[blueprint "chap10__definition_10_6_4"]
def msPredecessorUnionY (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (v : G.Node) : Set G.Node :=
  fun q => ∃ y : G.Node, msEquivClass G R v y ∧ G.predecessors y q

/-- Definition 10.6.4 (companion): candidate recursive calls from the
snapshots in `before`, tested against the current partition `current`.
The current partition changes after each recursive call in the printed program. -/
@[blueprint "chap10__definition_10_6_4"]
def msCongruentPairs (G : MSLabeledGraph)
    (before current : G.Node → G.Node → Prop)
    (u v : G.Node) : G.Node → G.Node → Prop :=
  fun x y => msPredecessorUnionX G before u x ∧ msPredecessorUnionY G before v y ∧
    ¬ msSameClass G current x y ∧ msCongruent G current x y

/-- Definition 10.6.4 (companion): the extensional seed consisting of
ordinary UNION and the compatible pairs tested immediately after that UNION,
using the saved pre-UNION predecessor sets. Sequential traversal is deferred. -/
@[blueprint "chap10__definition_10_6_4"]
def msMergeStep (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (u v : G.Node) : G.Node → G.Node → Prop :=
  fun a b => msUnion G R u v a b ∨
    msCongruentPairs G R (msUnion G R u v) u v a b

/-- A relation with an erased witness that all its pairs have equal sorts. -/
@[blueprint "chap10__definition_10_6_4"]
def MSSortedRelation (G : MSLabeledGraph) :=
  {R : G.Node → G.Node → Prop // MSSortSupported G R}

/-- A generating pair whose two endpoints belong to the same sort. -/
@[blueprint "chap10__definition_10_6_4"]
def MSSortedNodePair (G : MSLabeledGraph) :=
  {p : G.Node × G.Node // G.nodeSort p.1 = G.nodeSort p.2}

/-- Definition 10.6.4 (companion): the sorted relation obtained by ordinary
UNION; the proof component records the same-sort invariant. -/
@[blueprint "chap10__definition_10_6_4"]
def msUnionState (G : MSLabeledGraph) (R : MSSortedRelation G)
    (p : MSSortedNodePair G) : MSSortedRelation G :=
  ⟨msUnion G R.val p.val.1 p.val.2, by
    intro a b hab
    rcases hab with hab | ⟨hau, hvb⟩ | ⟨hav, hub⟩
    · exact R.property a b hab
    · exact (R.property a _ hau).trans (p.property.trans (R.property _ b hvb))
    · exact (R.property a _ hav).trans (p.property.symm.trans (R.property _ b hub))⟩

/-- Definition 10.6.4: a noncomputable MERGE output specification on a
sort-supported state and a same-sort pair. A congruence input is required by
its correctness contract. The inequivalence guard is retained; the other
branch takes the least sorted closure of the post-UNION seed.
No computable realization: deferred (OD-A17). -/
@[blueprint "chap10__definition_10_6_4" (main := true)]
noncomputable def msMerge (G : MSLabeledGraph) (R : MSSortedRelation G)
    (p : MSSortedNodePair G) : MSSortedRelation G := by
  classical
  let step := msMergeStep G R.val p.val.1 p.val.2
  have hs : MSSortSupported G step := by
    intro a b hab
    rcases hab with hu | hc
    · exact (msUnionState G R p).property a b hu
    · exact (G.lambda_rank_sort a).symm.trans
        ((congrArg (fun l => (G.Sigma.rank l).2) hc.2.2.2.1).trans
          (G.lambda_rank_sort b))
  exact if msSameClass G R.val p.val.1 p.val.2 then R else
    ⟨msCongruenceClosure G step hs, (msCongruenceClosure_isCongruence G step hs).1⟩

/-- Definition 10.6.4 (companion): output inclusion required of recursive
propagation, expressed only as a specification of the noncomputable output. -/
@[blueprint "chap10__definition_10_6_4"]
noncomputable def msMergeRecursiveCall (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) (x y : G.Node) : Prop :=
  msCongruentPairs G R.val (msUnion G R.val p.val.1 p.val.2) p.val.1 p.val.2 x y →
    msSameClass G (msMerge G R p).val x y

/-- Definition 10.6.4 (companion): the printed initializer `Id`. -/
@[blueprint "chap10__definition_10_6_4"]
def msIdentity (G : MSLabeledGraph) : G.Node → G.Node → Prop :=
  fun u v => u = v

/-- Definition 10.6.4 (companion): the saturated identity used by the
mathematical fold specification below. This is not the printed `Id`
initializer. SQ45 leaves the choice of initialization for the effective
driver open; this specification does not resolve it. -/
@[blueprint "chap10__definition_10_6_4"]
def msClosureSeed (G : MSLabeledGraph) : MSSortedRelation G :=
  let hs : MSSortSupported G (msIdentity G) := fun _ _ h => congrArg G.nodeSort h
  ⟨msCongruenceClosure G (msIdentity G) hs,
    (msCongruenceClosure_isCongruence G (msIdentity G) hs).1⟩

/-- Definition 10.6.4 (companion): a fold of the noncomputable MERGE
specification over same-sort input pairs, starting at the saturated seed.
No computable realization: deferred (OD-A17). The printed driver and
its SQ45 initialization remain separate obligations. -/
@[blueprint "chap10__definition_10_6_4"]
noncomputable def msClosureProgram (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) : MSSortedRelation G :=
  pairs.foldl (msMerge G) (msClosureSeed G)

/-- Definition 10.6.4 (companion): the state after the first `k` steps
of the mathematical fold specification. -/
@[blueprint "chap10__definition_10_6_4"]
noncomputable def msGlobalRelation (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) (k : Nat) : MSSortedRelation G :=
  (pairs.take k).foldl (msMerge G) (msClosureSeed G)

/-- Definition 10.6.4 (companion): the individual steps of that fold
specification, with the state unchanged once the input list is exhausted. -/
@[blueprint "chap10__definition_10_6_4"]
noncomputable def msClosureIteration (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) : Nat → MSSortedRelation G
  | 0 => msClosureSeed G
  | k + 1 =>
    match pairs[k]? with
    | some p => msMerge G (msClosureIteration G pairs k) p
    | none => msClosureIteration G pairs k

/-- Definition 10.6.4 (companion): the relation presented by a list of
same-sort generating pairs. No symmetry is imposed on the input list. -/
@[blueprint "chap10__lemma_10_6_5"]
def msRelationOfPairs (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) : MSSortedRelation G :=
  ⟨fun a b => ∃ p ∈ pairs, p.val.1 = a ∧ p.val.2 = b, by
    rintro a b ⟨p, _, rfl, rfl⟩
    exact p.property⟩

/-- Definition 10.6.4 (companion): a handle for the noncomputable output
specification on a relation presented exactly by the sorted input list.
No computable realization: deferred (OD-A17). -/
@[blueprint "chap10__definition_10_6_4"]
noncomputable def msCongruenceClosureAlgorithm (G : MSLabeledGraph)
    (R : MSSortedRelation G) (pairs : List (MSSortedNodePair G))
    (_hPairs : ∀ a b, R.val a b ↔ (msRelationOfPairs G pairs).val a b) :
    MSSortedRelation G :=
  msClosureProgram G pairs

/-- Lemma 10.6.5 (companion): `R₁`, the ordinary equivalence union of
the two selected blocks. Its leastness assumes that `R` is an equivalence. -/
@[blueprint "chap10__lemma_10_6_5"]
def msLeastEquivalenceR1 (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) : MSSortedRelation G :=
  msUnionState G R p

/-- Lemma 10.6.5 (companion): predecessors of `[u]` modulo `R₁`,
computed after UNION. The program's snapshot uses the original `R`. -/
@[blueprint "chap10__lemma_10_6_5"]
def msPredecessorXmodR1 (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) : Set G.Node :=
  msPredecessorUnionX G (msLeastEquivalenceR1 G R p).val p.val.1

/-- Lemma 10.6.5 (companion): predecessors of `[v]` modulo `R₁`. -/
@[blueprint "chap10__lemma_10_6_5"]
def msPredecessorYmodR1 (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) : Set G.Node :=
  msPredecessorUnionY G (msLeastEquivalenceR1 G R p).val p.val.2

/-- Lemma 10.6.5 (companion): compatible pairs in `X × Y`, where
both predecessor sets and compatibility are taken modulo `R₁`. -/
@[blueprint "chap10__lemma_10_6_5"]
def msNewlyCongruentR2 (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) : G.Node → G.Node → Prop :=
  fun x y => msPredecessorXmodR1 G R p x ∧ msPredecessorYmodR1 G R p y ∧
    msCongruent G (msLeastEquivalenceR1 G R p).val x y

/-- Lemma 10.6.5 (companion): `R₃`, the least sorted congruence
containing `R₁ ∪ R₂`. This is an extensional relation specification. -/
@[blueprint "chap10__lemma_10_6_5"]
def msMergedClosureR3 (G : MSLabeledGraph)
    (R : MSSortedRelation G) (p : MSSortedNodePair G) : G.Node → G.Node → Prop :=
  msCongruenceClosure G
    (fun a b => (msLeastEquivalenceR1 G R p).val a b ∨ msNewlyCongruentR2 G R p a b)
    (by
      intro a b hab
      rcases hab with h1 | h2
      · exact (msLeastEquivalenceR1 G R p).property a b h1
      · exact (G.lambda_rank_sort a).symm.trans
          ((congrArg (fun l => (G.Sigma.rank l).2) h2.2.2.1).trans
            (G.lambda_rank_sort b)))

/-- Lemma 10.6.5 (companion): inequivalent ordered pairs, the set that
shrinks under a UNION of distinct blocks. -/
@[blueprint "chap10__lemma_10_6_5"]
def msInequivalentPairs (G : MSLabeledGraph) (R : G.Node → G.Node → Prop) :
    Set (G.Node × G.Node) := fun p => ¬ msSameClass G R p.1 p.2

/-- The sorted seed `R ∪ {(u,v),(v,u)}` used in specification identities.
The reverse pair does not change its least congruence. -/
@[blueprint "chap10__lemma_10_6_5"]
def msMergeSeed (G : MSLabeledGraph) (R : MSSortedRelation G)
    (p : MSSortedNodePair G) : MSSortedRelation G :=
  ⟨fun a b => R.val a b ∨ (a = p.val.1 ∧ b = p.val.2) ∨
      (a = p.val.2 ∧ b = p.val.1), by
    rintro a b (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact R.property a b h
    · exact p.property
    · exact p.property.symm⟩

/-- Lemma 10.6.5 (soundness): `R₃` is a sorted congruence containing
`R` and the selected same-sort pair. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msMerge_sound (G : MSLabeledGraph) (R : MSSortedRelation G)
    (hR : MSGCongruence G R.val) (p : MSSortedNodePair G) :
    MSGCongruence G (msMergedClosureR3 G R p) ∧
      (∀ a b, R.val a b → msMergedClosureR3 G R p a b) ∧
      msMergedClosureR3 G R p p.val.1 p.val.2

/-- Lemma 10.6.5 (minimality): every sorted congruence containing
`R` and the selected pair contains `R₃`. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msMerge_minimal (G : MSLabeledGraph) (R : MSSortedRelation G)
    (p : MSSortedNodePair G) :
    ∀ R', MSGCongruence G R' → (∀ a b, R.val a b → R' a b) → R' p.val.1 p.val.2 →
      ∀ a b, msMergedClosureR3 G R p a b → R' a b

/-- A non-main identity for the noncomputable MERGE specification.
Its effective realization remains deferred (OD-A17). -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msMerge_correct (G : MSLabeledGraph) (R : MSSortedRelation G)
    (hR : MSGCongruence G R.val) (p : MSSortedNodePair G) :
    ∀ a b, (msMerge G R p).val a b ↔
      msCongruenceClosure G (msMergeSeed G R p).val (msMergeSeed G R p).property a b

/-- The strict decrease used in the printed termination argument:
ordinary UNION removes an inequivalent pair and adds none. A recursive
MERGE implementation and its termination proof remain deferred (OD-A17). -/
@[blueprint "chap10__lemma_10_6_5"]
theorem msMerge_terminates (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (hR : Equivalence R) (u v : G.Node) (h : ¬ msSameClass G R u v) :
    msInequivalentPairs G (msUnion G R u v) ⊆ msInequivalentPairs G R ∧
      ∃ p, msInequivalentPairs G R p ∧ ¬ msInequivalentPairs G (msUnion G R u v) p

/-- Transport between the successor indices in the two compatibility notations. -/
theorem msSuccessorIndex_eq (G : MSLabeledGraph) (a b : G.Node)
    (hlab : G.Lambda a = G.Lambda b)
    (hh : (G.Sigma.rank (G.Lambda a)).1.length = (G.Sigma.rank (G.Lambda b)).1.length)
    (i : Fin (G.Sigma.rank (G.Lambda a)).1.length) :
    G.delta b (hlab ▸ i) = G.delta b (Fin.cast hh i) := by
  congr 1
  apply Fin.ext
  rw [Fin.val_cast]
  revert i hh
  generalize G.Lambda a = la at hlab ⊢
  generalize G.Lambda b = lb at hlab ⊢
  intro hh i
  subst hlab
  rfl

/-- Two sorted seeds with mutually contained closures generate the same closure. -/
theorem msClosure_congr (G : MSLabeledGraph) (S₁ S₂ : MSSortedRelation G)
    (h12 : ∀ a b, S₁.val a b → msCongruenceClosure G S₂.val S₂.property a b)
    (h21 : ∀ a b, S₂.val a b → msCongruenceClosure G S₁.val S₁.property a b) :
    ∀ a b, msCongruenceClosure G S₁.val S₁.property a b ↔
      msCongruenceClosure G S₂.val S₂.property a b := by
  intro a b
  constructor
  · exact msCongruenceClosure_smallest G S₁.val S₁.property _
      (msCongruenceClosure_isCongruence G S₂.val S₂.property) h12 a b
  · exact msCongruenceClosure_smallest G S₂.val S₂.property _
      (msCongruenceClosure_isCongruence G S₁.val S₁.property) h21 a b

/-- Congruence closure absorbs a nested sorted closure in the left disjunct. -/
theorem msClosure_absorb_left (G : MSLabeledGraph) (A B : MSSortedRelation G) :
    ∀ a b,
      msCongruenceClosure G
        (fun x y => msCongruenceClosure G A.val A.property x y ∨ B.val x y)
        (fun x y h => h.elim
          ((msCongruenceClosure_isCongruence G A.val A.property).1 x y)
          (B.property x y)) a b ↔
      msCongruenceClosure G (fun x y => A.val x y ∨ B.val x y)
        (fun x y h => h.elim (A.property x y) (B.property x y)) a b := by
  -- REPAIR(T10-20): proof pending — transport closure absorption to sorted seeds
  sorry

/-- Folding the noncomputable specification from any sorted congruence
seed gives the least congruence containing the seed and input pairs. -/
theorem msClosureFold_eq (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) (R₀ : MSSortedRelation G)
    (hR₀ : MSGCongruence G R₀.val) :
    MSGCongruence G (pairs.foldl (msMerge G) R₀).val ∧
      ∀ a b, (pairs.foldl (msMerge G) R₀).val a b ↔
        msCongruenceClosure G
          (fun x y => R₀.val x y ∨ (msRelationOfPairs G pairs).val x y)
          (fun x y h => h.elim (R₀.property x y) ((msRelationOfPairs G pairs).property x y)) a b := by
  -- REPAIR(T10-20): proof pending — migrate the fold invariant to sorted states and pairs
  sorry

/-- A non-main correctness identity for the saturated-seed mathematical
fold. This does not choose an SQ45 reading or realize the printed driver.
No computable realization: deferred (OD-A17). -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msClosureProgram_correct (G : MSLabeledGraph)
    (pairs : List (MSSortedNodePair G)) :
    ∀ a b, (msClosureProgram G pairs).val a b ↔
      msCongruenceClosure G (msRelationOfPairs G pairs).val
        (msRelationOfPairs G pairs).property a b

/-- Lemma 10.6.5: on a finite graph, for a sorted congruence `R` and
same-sort `u,v`, the relation `R₃` is the least sorted congruence containing
`R ∪ {(u,v)}`. Here `R₁` is ordinary equivalence union, and `R₂` uses
compatible predecessor pairs modulo `R₁`. -/
@[blueprint "chap10__lemma_10_6_5" (main := true)]
theorem msMerge_computes_congruenceClosure (G : MSLabeledGraph)
    (R : MSSortedRelation G) (hR : MSGCongruence G R.val) (p : MSSortedNodePair G) :
    (MSGCongruence G (msMergedClosureR3 G R p) ∧
      (∀ a b, R.val a b → msMergedClosureR3 G R p a b) ∧
      msMergedClosureR3 G R p p.val.1 p.val.2) ∧
    (∀ R', MSGCongruence G R' → (∀ a b, R.val a b → R' a b) → R' p.val.1 p.val.2 →
      ∀ a b, msMergedClosureR3 G R p a b → R' a b)

-- Concrete witness of the two printed predecessor-snapshot configurations.

/-- Four nodes for leaves `a,b` and unary parents `f(a),f(b)`. -/
@[blueprint "chap10__definition_10_6_4"]
inductive SnapshotNode where
  | a | b | fa | fb
  deriving DecidableEq

/-- The two leaf labels and their shared unary parent label. -/
@[blueprint "chap10__definition_10_6_4"]
inductive SnapshotLabel where
  | a | b | f
  deriving DecidableEq

/-- A one-sort alphabet with two distinct constants and a unary symbol. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotAlphabet : MSRankedAlphabet where
  SortType := Unit
  symbols := SnapshotLabel
  rank
    | .a | .b => ([], ())
    | .f => ([()], ())

/-- The labels of the four snapshot nodes. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotLabel : SnapshotNode → SnapshotLabel
  | .a => .a
  | .b => .b
  | .fa | .fb => .f

/-- The concrete finite graph `a,b,f(a),f(b)` with the two displayed edges. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotGraph : MSLabeledGraph where
  Sigma := msSnapshotAlphabet
  Node := SnapshotNode
  nodeSort := fun _ => ()
  nodeFinite := ⟨[.a, .b, .fa, .fb], by intro v; cases v <;> simp⟩
  Lambda := msSnapshotLabel
  delta
    | .a, i => Fin.elim0 i
    | .b, i => Fin.elim0 i
    | .fa, _ => .a
    | .fb, _ => .b
  lambda_rank_sort := by intro v; cases v <;> rfl
  delta_succ_sort := by intros; exact Subsingleton.elim (α := Unit) _ _

/-- The identity partition before joining `a` and `b`. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotState : MSSortedRelation msSnapshotGraph :=
  ⟨msIdentity msSnapshotGraph, fun _ _ _ => rfl⟩

/-- The selected same-sort leaf pair `(a,b)`. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotPair : MSSortedNodePair msSnapshotGraph := ⟨(.a, .b), rfl⟩

/-- The program saves `X = {f(a)}` before UNION. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotProgramX : List SnapshotNode := [.fa]

/-- The program saves `Y = {f(b)}` before UNION. -/
@[blueprint "chap10__definition_10_6_4"]
def msSnapshotProgramY : List SnapshotNode := [.fb]

/-- Modulo `R₁`, the lemma's `X` contains both parents. -/
@[blueprint "chap10__lemma_10_6_5"]
def msSnapshotLemmaX : List SnapshotNode := [.fa, .fb]

/-- Modulo `R₁`, the lemma's `Y` also contains both parents. -/
@[blueprint "chap10__lemma_10_6_5"]
def msSnapshotLemmaY : List SnapshotNode := [.fa, .fb]

/-- The four-node witness separates the saved program snapshots from the
lemma snapshots. Ordinary UNION leaves the parents in distinct blocks;
they are nevertheless compatible modulo `R₁`. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msPredecessorSnapshots :
    MSGCongruence msSnapshotGraph msSnapshotState.val ∧
    (∀ x, msPredecessorUnionX msSnapshotGraph msSnapshotState.val .a x ↔
      x ∈ msSnapshotProgramX) ∧
    (∀ y, msPredecessorUnionY msSnapshotGraph msSnapshotState.val .b y ↔
      y ∈ msSnapshotProgramY) ∧
    (∀ x, msPredecessorXmodR1 msSnapshotGraph msSnapshotState msSnapshotPair x ↔
      x ∈ msSnapshotLemmaX) ∧
    (∀ y, msPredecessorYmodR1 msSnapshotGraph msSnapshotState msSnapshotPair y ↔
      y ∈ msSnapshotLemmaY) ∧
    ¬ (msLeastEquivalenceR1 msSnapshotGraph msSnapshotState msSnapshotPair).val .fa .fb ∧
    msNewlyCongruentR2 msSnapshotGraph msSnapshotState msSnapshotPair .fa .fb

end LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm
