import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.DisjunctiveNormalForm
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.GraphOfConjunction.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

-- ===================================================================
-- Definition 10.6.3: TERM(C), S(C), and the graph G(C)
-- ===================================================================

/-- Definition 10.6.3 (companion): A sorted term `⟨s, t⟩` — a term `t`
together with its sort `s`. The vertex universe of `G(C)` is carved out
of `MSTermSig L` by the `TERM(C)` membership predicate. -/
@[blueprint "chap10__definition_10_6_3"]
abbrev MSTermSig (L : MSLanguage) : Type := Σ s : L.SortType, MSTerm L s

/-- Definition 10.6.3 (companion): The set of all subterms of a term
INCLUDING the term itself, packaged as sorted terms `⟨sort, term⟩` — the
many-sorted analogue of §5.2 `Term.subterms`. -/
@[blueprint "chap10__definition_10_6_3"]
def msTermSubterms {L : MSLanguage} :
    {s : L.SortType} → MSTerm L s → Set (MSTermSig L)
  | s, .var _ i   => fun p => p = ⟨s, MSTerm.var s i⟩
  | s, .const _ c => fun p => p = ⟨s, MSTerm.const s c⟩
  | _, .func f ts =>
    (fun p => p = ⟨_, MSTerm.func f ts⟩) ∪
      Set.iUnion (fun i => msTermSubterms (ts i))

/-- Definition 10.6.3 (companion): The list of all subterms of a term
(including itself) — the computable enumeration matching `msTermSubterms`.
Used to establish finiteness of `TERM(C)`. -/
@[blueprint "chap10__definition_10_6_3"]
def msTermSubtermsList {L : MSLanguage} :
    {s : L.SortType} → MSTerm L s → List (MSTermSig L)
  | s, .var _ i   => [⟨s, MSTerm.var s i⟩]
  | s, .const _ c => [⟨s, MSTerm.const s c⟩]
  | _, .func f ts =>
    ⟨_, MSTerm.func f ts⟩ ::
      (List.finRange (L.funRank f).1.length).flatMap
        (fun i => msTermSubtermsList (ts i))

/-- Definition 10.6.3 (companion): The subterm set is exactly the set of
members of the subterm list. By induction on the term. -/
@[blueprint "chap10__definition_10_6_3"]
theorem msTermSubterms_iff_mem {L : MSLanguage} :
    ∀ {s : L.SortType} (t : MSTerm L s) (p : MSTermSig L),
      msTermSubterms t p ↔ p ∈ msTermSubtermsList t 

/-- Definition 10.6.3 (companion): `TERM(C)` — the set of all subterms of
terms occurring in `C` (the union, over every equality literal
`t =̇_s u`, positive or negated, of `msTermSubterms t ∪ msTermSubterms
u`), including `t_i, u_i, r_j, v_j` themselves; the vertex set of
`G(C)`. -/
@[blueprint "chap10__definition_10_6_3"]
def termSetOfConjunction {L : MSLanguage} (C : MSFormula L) :
    Set (MSTermSig L) :=
  fun p => ∃ (hL : L.hasEquality = true) (s : L.SortType) (t u : MSTerm L s),
    (msConjunctContains C (MSFormula.eq_ hL s t u) ∨
      msConjunctContains C (MSFormula.neg (MSFormula.eq_ hL s t u))) ∧
    (msTermSubterms t p ∨ msTermSubterms u p)

/-- Definition 10.6.3 (companion): A computable list over-approximating
`TERM(C)` — for every equality literal `t =̇_s u` (positive or its
negation) in `C`, collect the subterms of `t` and `u`. By recursion on
the formula tree of `C`. -/
@[blueprint "chap10__definition_10_6_3"]
def conjTermsList {L : MSLanguage} : MSFormula L → List (MSTermSig L)
  | MSFormula.eq_ _ _ t u => msTermSubtermsList t ++ msTermSubtermsList u
  | MSFormula.neg A => conjTermsList A
  | MSFormula.conj A B => conjTermsList A ++ conjTermsList B
  | MSFormula.disj A B => conjTermsList A ++ conjTermsList B
  | MSFormula.impl A B => conjTermsList A ++ conjTermsList B
  | MSFormula.equiv_ A B => conjTermsList A ++ conjTermsList B
  | _ => []

/-- Definition 10.6.3 (companion): If a literal `X` is a conjunct of `C`,
then the subterm list of `X` is contained in `conjTermsList C`. By
induction on the conjunction structure (`msConjunctContains`). -/
@[blueprint "chap10__definition_10_6_3"]
theorem conjTermsList_of_contains {L : MSLanguage} :
    ∀ (C X : MSFormula L), msConjunctContains C X →
      ∀ p ∈ conjTermsList X, p ∈ conjTermsList C 

/-- Definition 10.6.3 (companion): `TERM(C) ⊆ conjTermsList C` — every
node of `G(C)` appears in the (finite) collected term list. -/
@[blueprint "chap10__definition_10_6_3"]
theorem termSetOfConjunction_mem_list {L : MSLanguage} (C : MSFormula L)
    (p : MSTermSig L) (hp : termSetOfConjunction C p) :
    p ∈ conjTermsList C 

/-- Definition 10.6.3 (companion): `S(C)` — the set of sorts `s` such
that some term of sort `s` lies in `TERM(C)`. -/
@[blueprint "chap10__definition_10_6_3"]
def sortSetOfConjunction {L : MSLanguage} (C : MSFormula L) :
    Set L.SortType :=
  fun s => ∃ t : MSTerm L s, termSetOfConjunction C ⟨s, t⟩

/-- Definition 10.6.3 (companion): `TERM(C)_s` — the set of all terms of
sort `s` in `TERM(C)`; the `s`-indexed component of the vertex family
`V_s`. -/
@[blueprint "chap10__definition_10_6_3"]
def termSetOfSort {L : MSLanguage} (C : MSFormula L) (s : L.SortType) :
    Set (MSTerm L s) :=
  fun t => termSetOfConjunction C ⟨s, t⟩

/-- Definition 10.6.3 (companion): The carrier type of sort `s` of the
term algebra — the subtype `{ t : MSTerm L s // termSetOfSort C s t }` of
sort-`s` terms in `TERM(C)_s`. Used as the carrier of `termAlgebra` and
the base of the quotient model. -/
@[blueprint "chap10__definition_10_6_3"]
abbrev TermCarrier {L : MSLanguage} (C : MSFormula L) (s : L.SortType) :
    Type :=
  { t : MSTerm L s // termSetOfSort C s t }

/-- Definition 10.6.3 (companion): Every term is a subterm of itself —
`⟨s, t⟩ ∈ msTermSubterms t`. By cases on `t`: the variable and constant
cases are immediate (`msTermSubterms` is the singleton), and the function
case is the left disjunct of the union. -/
@[blueprint "chap10__definition_10_6_3"]
theorem msTermSubterms_self {L : MSLanguage} {s : L.SortType}
    (t : MSTerm L s) : msTermSubterms t ⟨s, t⟩ 

/-- Definition 10.6.3 (companion): `msTermSubterms` is closed under taking
immediate subterms: if `⟨_, f y_1…y_k⟩ ∈ msTermSubterms t`, then each
argument `y_i ∈ msTermSubterms t`. Proved by induction on `t`. The
function case branches on whether the witnessed function node is `t`
itself (then its arguments are the immediate subterms collected in the
`iUnion`) or lies in an argument's subterms (then the IH applies). -/
@[blueprint "chap10__definition_10_6_3"]
theorem msTermSubterms_subterm_closed {L : MSLanguage} :
    ∀ {s : L.SortType} (t : MSTerm L s) (f : L.funSymbols)
      (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i))
      (i : Fin (L.funRank f).1.length),
      msTermSubterms t ⟨(L.funRank f).2, MSTerm.func f ts⟩ →
        msTermSubterms t ⟨(L.funRank f).1.get i, ts i⟩ 

/-- Immediate argument subterms remain in TERM(C). -/
@[attach_debt, blueprint "chap10__definition_10_6_3"]
theorem termSetOfConjunction_arg {L : MSLanguage} (C : MSFormula L)
    (f : L.funSymbols)
    (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i))
    (h : termSetOfConjunction C ⟨_, MSTerm.func f ts⟩)
    (i : Fin (L.funRank f).1.length) :
    termSetOfConjunction C ⟨_, ts i⟩

/-- The occurring sorts S(C), each witnessed by a term of TERM(C). -/
@[blueprint "chap10__definition_10_6_3"]
abbrev ConjSort {L : MSLanguage} (C : MSFormula L) :=
  { s : L.SortType // sortSetOfConjunction C s }

/-- Definition 10.6.3 (companion): The symbols of the `S(C)`-ranked
alphabet `Σ` of `G(C)`: the constants, function symbols, and variables
occurring in `TERM(C)`. A constant/variable carries its sort; a function
symbol carries `f`. -/
@[blueprint "chap10__definition_10_6_3"]
inductive ConjSymbol (L : MSLanguage) (C : MSFormula L) : Type where
  | var (s : L.SortType) (i : Nat)
      (occurs : termSetOfConjunction C ⟨s, MSTerm.var s i⟩) : ConjSymbol L C
  | const (s : L.SortType) (c : L.constSymbols s)
      (occurs : termSetOfConjunction C ⟨s, MSTerm.const s c⟩) : ConjSymbol L C
  | func (f : L.funSymbols)
      (occurs : ∃ ts, termSetOfConjunction C ⟨_, MSTerm.func f ts⟩) : ConjSymbol L C

/-- Definition 10.6.3 (companion): The rank function of `Σ`: a function
symbol `f` keeps its §10.2 `funRank` `(u_1…u_n, s)`; a constant/variable
of sort `s` has empty arity `([], s)`. -/
@[blueprint "chap10__definition_10_6_3"]
def conjSymbolRank {L : MSLanguage} {C : MSFormula L} :
    ConjSymbol L C → (List (ConjSort C)) × ConjSort C
  | .var s i h => ([], ⟨s, ⟨MSTerm.var s i, h⟩⟩)
  | .const s c h => ([], ⟨s, ⟨MSTerm.const s c, h⟩⟩)
  | .func f h =>
      (List.ofFn (fun i : Fin (L.funRank f).1.length =>
        ⟨(L.funRank f).1.get i, by
          obtain ⟨ts, ht⟩ := h
          exact ⟨ts i, termSetOfConjunction_arg C f ts ht i⟩⟩),
       ⟨(L.funRank f).2, by
          obtain ⟨ts, ht⟩ := h
          exact ⟨MSTerm.func f ts, ht⟩⟩)

/-- Definition 10.6.3 (companion): The `S(C)`-ranked alphabet `Σ` of
`G(C)` as a concrete `MSRankedAlphabet`. -/
@[blueprint "chap10__definition_10_6_3"]
def rankedAlphabetOfConjunction {L : MSLanguage} (C : MSFormula L) :
    MSRankedAlphabet where
  SortType := ConjSort C
  symbols := ConjSymbol L C
  rank := conjSymbolRank

/-- Definition 10.6.3 (companion): The labeling `Λ` as a standalone def:
a variable/constant node is labeled by itself; a node `f y_1 … y_k` is
labeled by the function symbol `f`. This IS the `Lambda` field of
`graphOfConjunction`. -/
@[blueprint "chap10__definition_10_6_3"]
def labelOfNode {L : MSLanguage} (C : MSFormula L) :
    (p : MSTermSig L) → termSetOfConjunction C p →
      (rankedAlphabetOfConjunction C).symbols
  | ⟨s, MSTerm.var _ i⟩, h => ConjSymbol.var s i h
  | ⟨s, MSTerm.const _ c⟩, h => ConjSymbol.const s c h
  | ⟨_, MSTerm.func f ts⟩, h => ConjSymbol.func f ⟨ts, h⟩

/-- Definition 10.6.3 (companion): The successor function `δ` as a
standalone def: for a function node `f y_1 … y_k`, the `i`-th successor
is the `i`-th argument subterm `y_i = ts i`, repackaged as a sorted term.
For a leaf the index type `Fin 0` is empty so there is nothing to define.
This IS the `delta` field of `graphOfConjunction`. -/
@[blueprint "chap10__definition_10_6_3"]
def successorOfNode {L : MSLanguage} (C : MSFormula L) :
    (p : MSTermSig L) → (hp : termSetOfConjunction C p) →
      Fin (conjSymbolRank (labelOfNode C p hp)).1.length → MSTermSig L
  | ⟨_, MSTerm.var _ _⟩, _, i => i.elim0
  | ⟨_, MSTerm.const _ _⟩, _, i => i.elim0
  | ⟨_, MSTerm.func f ts⟩, _, i =>
      ⟨_, ts ⟨i.val, by simpa [labelOfNode, conjSymbolRank] using i.isLt⟩⟩

/-- Definition 10.6.3 (companion): `Λ`'s rank result sort matches the
node sort — `(conjSymbolRank (labelOfNode C ⟨s, t⟩ ht)).2 = s` for every
sorted term. By cases on `t`: a leaf is labeled by itself with rank
`([], s)`, and a function node `f y_1…y_k` of sort `(L.funRank f).2` is
labeled by `f` with rank `L.funRank f` whose result sort is exactly
`(L.funRank f).2`. -/
@[blueprint "chap10__definition_10_6_3"]
theorem labelOfNode_rank_sort {L : MSLanguage} (C : MSFormula L)
    (p : MSTermSig L) (hp : termSetOfConjunction C p) :
    (conjSymbolRank (labelOfNode C p hp)).2 = ⟨p.1, ⟨p.2, hp⟩⟩

/-- Definition 10.6.3 (companion): The sort of the `i`-th successor of a
function node equals the `i`-th argument sort of its label. Leaves have
empty arity (`Fin 0`), so the only content is the function case
`⟨_, f y_1…y_k⟩`, whose `i`-th successor `y_i = ts i` has sort
`(L.funRank f).1.get i = (conjSymbolRank (labelOfNode …)).1.get i`. -/
@[attach_debt, blueprint "chap10__definition_10_6_3"]
theorem successorOfNode_sort {L : MSLanguage} (C : MSFormula L)
    (p : MSTermSig L) (hp : termSetOfConjunction C p)
    (i : Fin (conjSymbolRank (labelOfNode C p hp)).1.length) :
    (successorOfNode C p hp i).1 = ((conjSymbolRank (labelOfNode C p hp)).1.get i).val

/-- Definition 10.6.3 (companion): The vertex subtype of `G(C)` is finite —
`TERM(C)` is finite because `C` is a finite formula. Witnessed by the
list obtained from `conjTermsList C` by attaching `TERM(C)`-membership
proofs (classically filtering out any over-collected terms); every node
appears in it by `termSetOfConjunction_mem_list`. -/
@[blueprint "chap10__definition_10_6_3"]
theorem termSetOfConjunction_node_finite {L : MSLanguage} (C : MSFormula L) :
    Set.Finite (fun (_ : { p : MSTermSig L // termSetOfConjunction C p }) =>
      True) 

/-- Every indexed successor of a node belongs to TERM(C). -/
@[attach_debt, blueprint "chap10__definition_10_6_3"]
theorem successorOfNode_mem {L : MSLanguage} (C : MSFormula L)
    (p : MSTermSig L) (hp : termSetOfConjunction C p)
    (i : Fin (conjSymbolRank (labelOfNode C p hp)).1.length) :
    termSetOfConjunction C (successorOfNode C p hp i)

/-- Definition 10.6.3: The finite labeled graph
`G(C) = (TERM(C), Σ, Λ, δ)` induced by the conjunction `C`, on which the
congruence closure of `E` is computed — a concrete instance of the
reusable `MSLabeledGraph` (Definition 10.6.1).

* `Sigma = rankedAlphabetOfConjunction C` is the `S(C)`-ranked alphabet.
* `Node = { p : MSTermSig L // termSetOfConjunction C p }` is the
  subtype of sorted terms carved out by `TERM(C)`, so `V_s = TERM(C)_s`
  is recovered by `nodeSort p = s`.
* `Lambda = labelOfNode C` labels variable/constant nodes by themselves
  and a node `f y_1 … y_k` by `f`.
* `delta = successorOfNode C` sends `(f y_1 … y_k, i)` to `y_i`.

`TERM(C)` is genuinely computed from `C` by subterm extraction (Pattern
1/3). The well-formedness fields (`lambda_rank_sort`, `delta_succ_sort`,
delta-membership) are discharged by the structural lemmas above; the
finiteness field `nodeFinite` uses the finite subterm enumeration. -/
@[blueprint "chap10__definition_10_6_3" (main := true)]
noncomputable def graphOfConjunction {L : MSLanguage} (C : MSFormula L) :
    MSLabeledGraph where
  Sigma := rankedAlphabetOfConjunction C
  Node := { p : MSTermSig L // termSetOfConjunction C p }
  nodeSort := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  nodeFinite := termSetOfConjunction_node_finite C
  Lambda := fun p => labelOfNode C p.1 p.2
  delta := fun p i => ⟨successorOfNode C p.1 p.2 i, successorOfNode_mem C p.1 p.2 i⟩
  lambda_rank_sort := fun p => labelOfNode_rank_sort C p.1 p.2
  delta_succ_sort := fun p i => Subtype.ext (successorOfNode_sort C p.1 p.2 i)

/-- Definition 10.6.3 (companion): `E = {(t_1,u_1),…,(t_m,u_m)}` — the set
of pairs `(t_i, u_i)` occurring in the positive (nonnegated) equations of
`C`; the relation whose congruence closure on `G(C)` is computed (the `R`
argument fed to `msCongruenceClosure`). A relation on the nodes of
`G(C)` (the `TERM(C)` subtype), so it plugs directly into
`msCongruenceClosure (graphOfConjunction C)`. The pair `(t, u)` of a
positive equation `t =̇_s u` of `C` relates the nodes `⟨s, t⟩` and
`⟨s, u⟩`. -/
@[blueprint "chap10__definition_10_6_3"]
def positiveEquationRelation {L : MSLanguage} (C : MSFormula L)
    (p q : (graphOfConjunction C).Node) : Prop :=
  ∃ (hL : L.hasEquality = true) (s : L.SortType) (t u : MSTerm L s),
    msConjunctContains C (MSFormula.eq_ hL s t u) ∧
      p.1 = ⟨s, t⟩ ∧ q.1 = ⟨s, u⟩

/-- Every positive equation relates nodes of the same occurring sort. -/
@[attach_debt, blueprint "chap10__definition_10_6_3"]
theorem positiveEquationRelation_sortSupported {L : MSLanguage} (C : MSFormula L) :
    MSSortSupported (graphOfConjunction C) (positiveEquationRelation C)

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
