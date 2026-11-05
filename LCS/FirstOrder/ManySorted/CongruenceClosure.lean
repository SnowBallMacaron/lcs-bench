import LCS.Item
import LCS.Util
import LCS.FirstOrder.Syntax.RankedAlphabet
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.ProofsStamp

/-! # FirstOrder.ManySorted.CongruenceClosure
    Formalization of Chapter 10, Subsections 10.6.2 and 10.6.4
    (Congruence Closure on a Graph; Existence of the Congruence Closure).

    Finite labeled graphs over a many-sorted ranked alphabet
    (Def 10.6.1), the notion of a G-congruence as a backward-closed
    equivalence (Def 10.6.2), a first worked graph (Example 10.6.1), and
    the existence of a least congruence containing a relation —
    the congruence closure (Lemma 10.6.3).

    Builds on §10.5 (LCS.FirstOrder.ManySorted.Equality) for the
    equality semantics the decision procedure decides.

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure

-- ===================================================================
-- Definition 10.6.1: Finite labeled graph
-- ===================================================================

/-- Definition 10.6.1: A finite labeled graph `G = (V, Σ, Λ, δ)`.

* `V` is the S-indexed family of finite vertex sets `(V_s)`, encoded as
  a single node type `Node` together with `nodeSort : Node → S` (so
  `V_s = {v | nodeSort v = s}`) and a finiteness witness `nodeFinite`.
* `Σ` is an S-sorted ranked alphabet `MSRankedAlphabet` whose symbols
  label the nodes.
* `Λ : V → Σ` (`Lambda`) is the labeling function.
* `δ` (`delta`) is the successor function. It is encoded as a TOTAL
  dependent function over valid edges
  `(v : Node) → Fin (Σ.rank (Λ v)).1.length → Node`: for a node `v`
  whose label has rank `(u_1…u_n, s)`, `δ v i = v[i]` is the `i`-th
  successor. For a terminal node the arity length is `0`, so `Fin 0` is
  empty and `δ` is genuinely undefined there — faithful to "for a node
  with rank `(e, s)`, `δ` is not defined".

Two well-formedness conditions on `Λ` and `δ`:
* `lambda_rank_sort`: for `v ∈ V_s`, the rank `r(Λ(v)) = (u_1…u_n, s)`
  has result sort equal to the node's sort.
* `delta_succ_sort`: the sort of the `i`-th successor `δ(v, i)` equals
  the `i`-th argument sort `u_i`.

This is the reusable type the Decision/Predicates/Algorithm sibling
modules import as `G(C)`. -/
@[blueprint "chap10__definition_10_6_1" (main := true)]
structure MSLabeledGraph : Type 1 where
  /-- The S-sorted ranked alphabet Σ of the graph. -/
  Sigma : MSRankedAlphabet
  /-- The vertex carrier; `V = ⋃_s V_s` as a single node type. -/
  Node : Type
  /-- `nodeSort v = s` picks out the family component `V_s ∋ v`. -/
  nodeSort : Node → Sigma.SortType
  /-- The graph is finite: the vertex set `V` is finite. -/
  nodeFinite : Set.Finite (fun (_ : Node) => True)
  /-- The labeling function `Λ : V → Σ`. -/
  Lambda : Node → Sigma.symbols
  /-- The successor function `δ`, total on valid edges `(v, i)`. -/
  delta : (v : Node) → Fin (Sigma.rank (Lambda v)).1.length → Node
  /-- For `v ∈ V_s`, `r(Λ(v)) = (u_1…u_n, s)`: the result sort matches. -/
  lambda_rank_sort : ∀ v : Node, (Sigma.rank (Lambda v)).2 = nodeSort v
  /-- The sort of `δ(v, i)` equals the `i`-th argument sort `u_i`. -/
  delta_succ_sort : ∀ (v : Node) (i : Fin (Sigma.rank (Lambda v)).1.length),
    nodeSort (delta v i) = (Sigma.rank (Lambda v)).1.get i

namespace MSLabeledGraph

/-- Definition 10.6.1 (companion): The `i`-th successor `v[i] = δ(v, i)`
of a node `v`, defined exactly on edges `(v, i)` with
`1 ≤ i ≤ n` where `r(Λ(v)) = (u_1…u_n, s)`. -/
@[blueprint "chap10__definition_10_6_1"]
def successor (G : MSLabeledGraph) (v : G.Node)
    (i : Fin (G.Sigma.rank (G.Lambda v)).1.length) : G.Node :=
  G.delta v i

/-- Definition 10.6.1 (companion): An edge `(v, i)` in the domain of `δ`:
a node together with a successor index in range for its label's arity. -/
@[blueprint "chap10__definition_10_6_1"]
def Edge (G : MSLabeledGraph) : Type :=
  Σ' v : G.Node, Fin (G.Sigma.rank (G.Lambda v)).1.length

/-- Definition 10.6.1 (companion): A node `v` is terminal (a leaf) when
its label has empty arity, `r(Λ(v)) = (e, s)`; then `Fin 0` is empty so
`δ` is undefined at `v`. -/
@[blueprint "chap10__definition_10_6_1"]
def isTerminal (G : MSLabeledGraph) (v : G.Node) : Prop :=
  (G.Sigma.rank (G.Lambda v)).1 = []

/-- Definition 10.6.1 (companion): The set `P_u` of predecessors of a
node `u`: all `v` having `u` as some successor, `P_u = {v | ∃ i, δ(v,i) = u}`. -/
@[blueprint "chap10__definition_10_6_1"]
def predecessors (G : MSLabeledGraph) (u : G.Node) : Set G.Node :=
  fun v => ∃ i, G.delta v i = u

/-- Definition 10.6.1 (companion): A node `u` is initial (a root) when its
predecessor set is empty, `P_u = ∅`. -/
@[blueprint "chap10__definition_10_6_1"]
def isInitial (G : MSLabeledGraph) (u : G.Node) : Prop :=
  ∀ v, ¬ (G.predecessors u v)

end MSLabeledGraph

-- ===================================================================
-- Definition 10.6.2: G-congruence
-- ===================================================================

/-- A node relation represents a sorted family when every related pair
belongs to a single sort fiber. -/
@[blueprint "chap10__definition_10_6_2"]
def MSSortSupported (G : MSLabeledGraph) (R : G.Node → G.Node → Prop) : Prop :=
  ∀ u v, R u v → G.nodeSort u = G.nodeSort v

/-- Definition 10.6.2 (companion): The component `R_s` of the S-indexed
family `R = (R_s)`, recovered from a single binary relation `R` on
nodes by restricting to pairs whose `nodeSort` is `s`:
`R_s u v ↔ nodeSort u = s ∧ nodeSort v = s ∧ R u v`. -/
@[blueprint "chap10__definition_10_6_2"]
def restrictToSort (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (s : G.Sigma.SortType) (u v : G.Node) : Prop :=
  G.nodeSort u = s ∧ G.nodeSort v = s ∧ R u v

/-- Definition 10.6.2 (companion): The standalone backward-closure
property — the characteristic "kind of backward closure" of a
congruence. It is the conjunction of the two sub-clauses of condition
(2): the leaf base case (equal empty-arity labels are congruent) and
the successor step (equal labels with componentwise-congruent
successors are congruent). When `h : Λ(u) = Λ(v)`, the rank lengths of
the two labels agree, so the `i`-th successor index `i` of `u` is
transported to `v`'s domain by `h ▸ i`. -/
@[blueprint "chap10__definition_10_6_2"]
def IsBackwardClosed (G : MSLabeledGraph) (R : G.Node → G.Node → Prop) : Prop :=
  -- (2a) leaf base case: equal empty-arity (e, s) labels ⇒ congruent.
  (∀ u v, G.Lambda u = G.Lambda v →
      (G.Sigma.rank (G.Lambda u)).1 = [] → R u v) ∧
  -- (2b) successor step: equal labels of arity (s_1…s_n, s) with all
  -- successors componentwise congruent ⇒ congruent.
  (∀ u v, (h : G.Lambda u = G.Lambda v) →
      (∀ i : Fin (G.Sigma.rank (G.Lambda u)).1.length,
        R (G.delta u i) (G.delta v (h ▸ i))) → R u v)

/-- Definition 10.6.2: An (S-indexed) relation `R` on the nodes of a
finite graph `G` is a **G-congruence** (for short, a congruence) iff it
is sort-supported and satisfies:

(1) each `R_s` is an equivalence relation on the fiber `V_s`; and

(2) backward closure (`IsBackwardClosed`):
    (2a) if `Λ(u) = Λ(v)` and `r(Λ(u)) = (e, s)` then `u R_s v` — any
         two terminal nodes labeled with the same empty-arity symbol are
         congruent; and
    (2b) if `Λ(u) = Λ(v)`, `r(Λ(u)) = (s_1…s_n, s)`, and `u[i] R_{s_i}
         v[i]` for every `i`, then `u R_s v`.

`MSGCongruence G R` is the `Prop` asserting `R` is a G-congruence; this
is the "g-congruence" keyword realized as a predicate (Pattern 5). -/
@[blueprint "chap10__definition_10_6_2" (main := true)]
def MSGCongruence (G : MSLabeledGraph) (R : G.Node → G.Node → Prop) : Prop :=
  MSSortSupported G R ∧
  -- (1) Equivalence is required separately on each fiber V_s.
  (∀ s, Equivalence (fun u v : {u : G.Node // G.nodeSort u = s} => R u.val v.val)) ∧
  -- (2) R is backward-closed.
  IsBackwardClosed G R

-- ===================================================================
-- Lemma 10.6.3: Existence of the congruence closure — construction
-- ===================================================================

/-- Lemma 10.6.3 (companion): The reflexive seed (diagonal)
`{(u, u) | u ∈ V}` added at stage 0 to force reflexivity. -/
@[blueprint "chap10__lemma_10_6_3"]
def msReflexiveSeed (G : MSLabeledGraph) (u v : G.Node) : Prop :=
  u = v

/-- Lemma 10.6.3 (companion): The leaf-pair seed
`{(u, v) | Λ(u) = Λ(v), r(Λ(u)) = (e, s)}` of equal-labeled terminal
nodes added at stage 0 (the congruence base case as a seed). -/
@[blueprint "chap10__lemma_10_6_3"]
def msLeafPairSeed (G : MSLabeledGraph) (u v : G.Node) : Prop :=
  G.Lambda u = G.Lambda v ∧ (G.Sigma.rank (G.Lambda u)).1 = []

/-- Lemma 10.6.3 (companion): The base iterate `R^0`,
`R^0 = R ∪ {leaf-pairs} ∪ {diagonal}` for a sort-supported seed:
`R_s^0 = R_s ∪ {(u,v) | Λu=Λv, r(Λu)=(e,s)} ∪ {(u,u) | u ∈ V}`. -/
@[blueprint "chap10__lemma_10_6_3"]
def msCongruenceIterateBase (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (_hR : MSSortSupported G R)
    (u v : G.Node) : Prop :=
  R u v ∨ msLeafPairSeed G u v ∨ msReflexiveSeed G u v

/-- Lemma 10.6.3 (companion): The symmetric closure step, adding
`{(v, u) | (u, v) ∈ R^i}`. -/
@[blueprint "chap10__lemma_10_6_3"]
def msSymmetricStep (G : MSLabeledGraph) (Ri : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  Ri v u

/-- Lemma 10.6.3 (companion): The transitive closure step, adding
`{(u, w) | ∃ v ∈ V_s, (u, v) ∈ R_s^i and (v, w) ∈ R_s^i}`.
All three nodes belong to the same sort fiber. -/
@[blueprint "chap10__lemma_10_6_3"]
def msTransitiveStep (G : MSLabeledGraph) (Ri : G.Node → G.Node → Prop)
    (u w : G.Node) : Prop :=
  ∃ v, G.nodeSort u = G.nodeSort v ∧ G.nodeSort v = G.nodeSort w ∧
    Ri u v ∧ Ri v w

/-- Lemma 10.6.3 (companion): The congruence closure step, adding
`{(u, v) | Λu = Λv, r(Λu) = (s_1…s_n, s), and u[j] R^i v[j] ∀ j}`. When
`h : Λ(u) = Λ(v)`, the rank lengths agree, so the `j`-th successor index
`j` of `u` is transported to `v`'s domain by `h ▸ j`. -/
@[blueprint "chap10__lemma_10_6_3"]
def msSuccessorCongruenceStep (G : MSLabeledGraph) (Ri : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  ∃ h : G.Lambda u = G.Lambda v,
    ∀ j : Fin (G.Sigma.rank (G.Lambda u)).1.length,
      Ri (G.delta u j) (G.delta v (h ▸ j))

/-- Lemma 10.6.3 (companion): The one-step operator producing `R^{i+1}`
from `R^i`:
`R^{i+1} = R^i ∪ symmetric(R^i) ∪ transitive(R^i) ∪ successorCongruence(R^i)`. -/
@[blueprint "chap10__lemma_10_6_3"]
def msCongruenceIterateStep (G : MSLabeledGraph) (Ri : G.Node → G.Node → Prop)
    (u v : G.Node) : Prop :=
  Ri u v ∨ msSymmetricStep G Ri u v ∨ msTransitiveStep G Ri u v ∨
    msSuccessorCongruenceStep G Ri u v

/-- Lemma 10.6.3 (required): The inductively defined sequence `R^i` of
S-indexed families of relations from a sort-supported seed. `R^0` is the
base iterate; `R^{i+1}` is obtained from `R^i` by the one-step operator (symmetric, transitive, and
successor-congruence completions). This is the genuine iteration whose
union is the congruence closure. -/
@[blueprint "chap10__lemma_10_6_3"]
def msCongruenceIterate (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (hR : MSSortSupported G R) :
    Nat → G.Node → G.Node → Prop
  | 0 => msCongruenceIterateBase G R hR
  | i + 1 => msCongruenceIterateStep G (msCongruenceIterate G R hR i)

/-- Lemma 10.6.3 (required): The congruence closure
`(R*)_s = ⋃_i R_s^i` of a sort-supported seed,
i.e. `R* u v ↔ ∃ i, R^i u v`. -/
@[blueprint "chap10__lemma_10_6_3"]
def msCongruenceClosure (G : MSLabeledGraph) (R : G.Node → G.Node → Prop)
    (hR : MSSortSupported G R)
    (u v : G.Node) : Prop :=
  ∃ i, msCongruenceIterate G R hR i u v

-- ===================================================================
-- Example 10.6.1: A worked two-sort alphabet and conjunction
-- ===================================================================

/-- Example 10.6.1 (companion): The two sorts `S = {i, s}` of the
example alphabet. -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleSort : Type where
  | i : ExampleSort
  | s : ExampleSort

/-- Example 10.6.1 (companion): Decidable equality of the example sorts,
needed to type concrete terms and the conjunction. -/
@[blueprint "chap10__example_10_6_1"]
instance : DecidableEq ExampleSort := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- Example 10.6.1 (companion): The symbols `Σ = {f, g, a, b, c}` of the
example ranked alphabet (all five symbols as one carrier). -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleSym : Type where
  | f : ExampleSym
  | g : ExampleSym
  | a : ExampleSym
  | b : ExampleSym
  | c : ExampleSym

/-- Example 10.6.1: The concrete S-sorted ranked alphabet with
`S = {i, s}`, `Σ = {f, g, a, b, c}` and ranks
`r(f) = ([i,s], s)`, `r(g) = ([s,i], s)`, `r(a) = ([], i)`,
`r(b) = ([], s)`, `r(c) = ([], s)`. The leaves `a, b, c` have empty
arity; `f, g` are binary. Instantiates `MSRankedAlphabet`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleAlphabet : MSRankedAlphabet where
  SortType := ExampleSort
  symbols := ExampleSym
  rank
    | .f => ([ExampleSort.i, ExampleSort.s], ExampleSort.s)
    | .g => ([ExampleSort.s, ExampleSort.i], ExampleSort.s)
    | .a => ([], ExampleSort.i)
    | .b => ([], ExampleSort.s)
    | .c => ([], ExampleSort.s)

/-- Example 10.6.1 (companion): Constants of sort `i` — just `a`
(`CS_i = {a}`). -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleConstI : Type where
  | a : ExampleConstI

/-- Example 10.6.1 (companion): Constants of sort `s` — `b` and `c`
(`CS_s = {b, c}`). -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleConstS : Type where
  | b : ExampleConstS
  | c : ExampleConstS

/-- Example 10.6.1 (companion): Function symbols `FS = {f, g}` of the
matching §10.2 many-sorted language (the leaves `a, b, c` are constants,
so they live in `CS`, not `FS`). -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleFunc : Type where
  | f : ExampleFunc
  | g : ExampleFunc

/-- Example 10.6.1 (companion): The empty predicate-symbol type — the
example language has no predicate symbols (only equality is used). -/
@[blueprint "chap10__example_10_6_1"]
inductive ExamplePred : Type where

/-- Example 10.6.1 (companion): The §10.2 many-sorted language matching
`exampleAlphabet`: `S = {i, s}`, `CS_i = {a}`, `CS_s = {b, c}`,
`FS = {f, g}` with `funRank f = ([i,s], s)`, `funRank g = ([s,i], s)`,
no predicate symbols. Used to type the concrete example terms below. -/
@[blueprint "chap10__example_10_6_1"]
def exampleLanguage : MSLanguage where
  SortType := ExampleSort
  someSort := ExampleSort.i
  funSymbols := ExampleFunc
  funRank
    | .f => ([ExampleSort.i, ExampleSort.s], ExampleSort.s)
    | .g => ([ExampleSort.s, ExampleSort.i], ExampleSort.s)
  funRank_nonempty := fun fn => by cases fn <;> decide
  constSymbols
    | .i => ExampleConstI
    | .s => ExampleConstS
  predSymbols := ExamplePred
  predArity := fun p => nomatch p

/-- Example 10.6.1 (companion): Argument vector for the binary function
`f`, whose arity is `[i, s]`: first argument of sort `i`, second of
sort `s`. -/
@[blueprint "chap10__example_10_6_1"]
def exampleFArgs (x : MSTerm exampleLanguage ExampleSort.i)
    (y : MSTerm exampleLanguage ExampleSort.s) :
    (i : Fin (exampleLanguage.funRank ExampleFunc.f).1.length) →
      MSTerm exampleLanguage ((exampleLanguage.funRank ExampleFunc.f).1.get i)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- Example 10.6.1 (companion): Argument vector for the binary function
`g`, whose arity is `[s, i]`: first argument of sort `s`, second of
sort `i`. -/
@[blueprint "chap10__example_10_6_1"]
def exampleGArgs (x : MSTerm exampleLanguage ExampleSort.s)
    (y : MSTerm exampleLanguage ExampleSort.i) :
    (i : Fin (exampleLanguage.funRank ExampleFunc.g).1.length) →
      MSTerm exampleLanguage ((exampleLanguage.funRank ExampleFunc.g).1.get i)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- Example 10.6.1: The sort-`i` constant `a`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_a : MSTerm exampleLanguage ExampleSort.i :=
  MSTerm.const (L := exampleLanguage) ExampleSort.i ExampleConstI.a

/-- Example 10.6.1: The sort-`s` constant `b`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_b : MSTerm exampleLanguage ExampleSort.s :=
  MSTerm.const (L := exampleLanguage) ExampleSort.s ExampleConstS.b

/-- Example 10.6.1: The sort-`s` constant `c`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_c : MSTerm exampleLanguage ExampleSort.s :=
  MSTerm.const (L := exampleLanguage) ExampleSort.s ExampleConstS.c

/-- Example 10.6.1: The term `f(a, b)` of sort `s`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_fab : MSTerm exampleLanguage ExampleSort.s :=
  MSTerm.func (L := exampleLanguage) ExampleFunc.f
    (exampleFArgs exampleTerm_a exampleTerm_b)

/-- Example 10.6.1: The term `g(c, a)` of sort `s`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_gca : MSTerm exampleLanguage ExampleSort.s :=
  MSTerm.func (L := exampleLanguage) ExampleFunc.g
    (exampleGArgs exampleTerm_c exampleTerm_a)

/-- Example 10.6.1: The term `g(f(a, b), a)` of sort `s`. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleTerm_gfaba : MSTerm exampleLanguage ExampleSort.s :=
  MSTerm.func (L := exampleLanguage) ExampleFunc.g
    (exampleGArgs exampleTerm_fab exampleTerm_a)

/-- Example 10.6.1: The concrete conjunction
`C = (f(a,b) =̇_s c) ∧ ¬ (g(f(a,b),a) =̇_s g(c,a))` — one positive and
one negated equation, the literals decided by the procedure. -/
@[blueprint "chap10__example_10_6_1" (main := true)]
def exampleConjunction : MSFormula exampleLanguage :=
  MSFormula.conj
    (MSFormula.eq_ (L := exampleLanguage) rfl ExampleSort.s
      exampleTerm_fab exampleTerm_c)
    (MSFormula.neg
      (MSFormula.eq_ (L := exampleLanguage) rfl ExampleSort.s
        exampleTerm_gfaba exampleTerm_gca))

-- ===================================================================
-- Lemma 10.6.3: Existence of the congruence closure — theorems
-- ===================================================================

/-- Lemma 10.6.3 (companion): The closure is the union of the iterates,
`(R*)_s = ⋃_i R^i_s`: `R* u v ↔ ∃ i, R^i u v`. Holds by definition of
`msCongruenceClosure`. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_eq_iUnion (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) (u v : G.Node) :
    msCongruenceClosure G R hR u v ↔ ∃ i, msCongruenceIterate G R hR i u v

/-- Lemma 10.6.3 (companion): The closure `R*` contains `R`: every pair
related by `R` is already related at stage 0. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_contains (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    ∀ u v, R u v → msCongruenceClosure G R hR u v

/-- Lemma 10.6.3 (companion): One-step monotonicity of the iterates —
`R^i ⊆ R^{i+1}`, since the one-step operator keeps `R^i` as its first
disjunct. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_succ_mono (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) (i : Nat) (u v : G.Node)
    (h : msCongruenceIterate G R hR i u v) :
    msCongruenceIterate G R hR (i + 1) u v

/-- Lemma 10.6.3 (companion): Monotonicity of the iterates in the stage
index — `i ≤ j → R^i ⊆ R^j`. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_mono (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) {i j : Nat} (hij : i ≤ j)
    {u v : G.Node} (h : msCongruenceIterate G R hR i u v) :
    msCongruenceIterate G R hR j u v

/-- Lemma 10.6.3 (companion): An upper bound for a `Fin n`-indexed family
of stage indices: there is an `N` dominating every `g j`. Used to find a
common stage at which all successor pairs of a node are already related,
for the backward-closure step. -/
@[blueprint "chap10__lemma_10_6_3"]
def finBound : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, g => max (g ⟨n, Nat.lt_succ_self n⟩) (finBound n (fun j => g j.castSucc))

@[blueprint "chap10__lemma_10_6_3"]
theorem finBound_le : (n : Nat) → (g : Fin n → Nat) → (j : Fin n) →
    g j ≤ finBound n g


/-- Lemma 10.6.3 (companion): The union `R*` is itself a G-congruence on
`G` (part (1) of the lemma). Proved by induction on the iterates:
reflexivity, symmetry, transitivity, and backward closure are each
introduced as an iterate step and absorbed at the next stage. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_isCongruence (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    MSGCongruence G (msCongruenceClosure G R hR)

/-- Lemma 10.6.3 (companion, induction step): Every G-congruence `R'`
containing `R` contains each iterate `R^i`. Hence it contains
`R* = ⋃_i R^i`. Proved by induction on `i`, using that `R'` is an
equivalence relation (for the symmetric/transitive steps) and is
backward-closed (for the successor-congruence step). -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_subset_of_congruence (G : MSLabeledGraph)
    (R R' : G.Node → G.Node → Prop) (hR : MSSortSupported G R) (hR' : MSGCongruence G R')
    (hContains : ∀ u v, R u v → R' u v) :
    ∀ i u v, msCongruenceIterate G R hR i u v → R' u v

/-- Lemma 10.6.3 (companion): `R*` is the smallest congruence on `G`
containing `R` (part (3)): every G-congruence `R'` containing `R`
contains `R*`. Follows from `msCongruenceIterate_subset_of_congruence`. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_smallest (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    ∀ R', MSGCongruence G R' → (∀ u v, R u v → R' u v) →
      ∀ u v, msCongruenceClosure G R hR u v → R' u v

/-- Lemma 10.6.3 (companion): The bare existence statement — for any
finite graph `G` and sort-supported relation `R` on `V`, a smallest G-congruence
containing `R` exists (witnessed by `msCongruenceClosure G R hR`). -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_exists_least (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    ∃ Rstar, MSGCongruence G Rstar ∧ (∀ u v, R u v → Rstar u v) ∧
      (∀ R', MSGCongruence G R' → (∀ u v, R u v → R' u v) →
        ∀ u v, Rstar u v → R' u v)

/-- Lemma 10.6.3 (companion): The one-step operator is a congruence for
pointwise equivalence — if `R^i` and `R'` relate the same pairs, so do
their one-step completions. Used to propagate a one-step fixpoint
forward. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterateStep_congr (G : MSLabeledGraph)
    (Ri Ri' : G.Node → G.Node → Prop) (h : ∀ a b, Ri a b ↔ Ri' a b)
    (u v : G.Node) :
    msCongruenceIterateStep G Ri u v ↔ msCongruenceIterateStep G Ri' u v

/-- Lemma 10.6.3 (companion): A one-step fixpoint at stage `i` makes every
later one-step a fixpoint too: `R^{i+k} = R^{i+k+1}` for all `k`. Proved
by induction on `k`, propagating the fixpoint through the (pointwise)
one-step congruence. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_fixpoint_step (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) (i : Nat)
    (hfix : ∀ u v, msCongruenceIterate G R hR i u v ↔
      msCongruenceIterate G R hR (i + 1) u v) :
    ∀ k u v, msCongruenceIterate G R hR (i + k) u v ↔
      msCongruenceIterate G R hR (i + k + 1) u v

/-- Lemma 10.6.3 (companion): A one-step fixpoint at stage `i` is a
fixpoint forever — every later iterate `R^{i+k}` equals `R^i`. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_fixpoint_add (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) (i : Nat)
    (hfix : ∀ u v, msCongruenceIterate G R hR i u v ↔
      msCongruenceIterate G R hR (i + 1) u v) :
    ∀ k u v, msCongruenceIterate G R hR i u v ↔ msCongruenceIterate G R hR (i + k) u v

/-- Lemma 10.6.3 (companion): A non-decreasing `ℕ`-sequence bounded above
must repeat a value at two consecutive stages. The combinatorial core of
finite stabilization. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem nat_seq_stabilizes (f : Nat → Nat) (N : Nat)
    (hmono : ∀ i, f i ≤ f (i + 1)) (hbound : ∀ i, f i ≤ N) :
    ∃ j, f j = f (j + 1)

/-- Lemma 10.6.3 (companion): If a predicate `p` implies `q` everywhere on
a list and they have equal count there, then `q` implies `p` on the list
too — equal counts force the implication to be an equivalence. -/
@[blueprint "chap10__lemma_10_6_3"]
theorem countP_eq_imp_rev {α : Type u} (p q : α → Bool) (l : List α)
    (himp : ∀ x ∈ l, p x → q x) (heq : l.countP p = l.countP q) :
    ∀ x ∈ l, q x → p x

/-- Lemma 10.6.3 (companion): Because `G` is finite, the iteration
stabilizes — there is some `i` with `R^i = R^{i+1}` (a fixpoint). -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceIterate_stabilizes (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    ∃ i, ∀ u v, msCongruenceIterate G R hR i u v ↔
      msCongruenceIterate G R hR (i + 1) u v

/-- Lemma 10.6.3 (companion): There exists a stage at which the supported
congruence closure equals the iterate, `R* = R^i`. This is an existence
statement about finite stabilization. Effective saturation has
no computable realization: deferred (OD-A17). -/
@[blueprint "chap10__lemma_10_6_3"]
theorem msCongruenceClosure_computable (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    ∃ i, ∀ u v, msCongruenceClosure G R hR u v ↔ msCongruenceIterate G R hR i u v

/-- Lemma 10.6.3 (Existence of the congruence closure): For a finite
graph `G` and a sort-supported relation `R` on its nodes, the iterated closure
`R* := msCongruenceClosure G R hR` is the SMALLEST G-congruence containing
`R`. Stated as the conjunction (∧) of three genuine parts:
(1) `R*` is itself a G-congruence;
(2) `R*` contains `R`;
(3) every G-congruence `R'` containing `R` contains `R*` (least under
    inclusion). -/
@[blueprint "chap10__lemma_10_6_3" (main := true)]
theorem msCongruenceClosure_least (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (hR : MSSortSupported G R) :
    MSGCongruence G (msCongruenceClosure G R hR) ∧
    (∀ u v, R u v → msCongruenceClosure G R hR u v) ∧
    (∀ R', MSGCongruence G R' → (∀ u v, R u v → R' u v) →
      ∀ u v, msCongruenceClosure G R hR u v → R' u v)

end LCS.FirstOrder.ManySorted.CongruenceClosure
