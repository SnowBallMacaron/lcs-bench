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

end LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm
