import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Examples.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

-- ===================================================================
-- Example 10.6.2: deciding C = (f(a,b) =̇ c) ∧ ¬(g(f(a,b),a) =̇ g(c,a))
-- ===================================================================

/-- Example 10.6.2 (companion): `TERM(C)_i` for the example conjunction
`C = (f(a,b) =̇_s c) ∧ ¬(g(f(a,b),a) =̇_s g(c,a))` — the sort-`i`
subterm set, which equals `{a}` (only the integer-sort term `a`
occurs). Reuses `exampleConjunction` from the sibling core module. -/
@[blueprint "chap10__example_10_6_2"]
def exampleTermSetI : Set (MSTerm exampleLanguage ExampleSort.i) :=
  termSetOfSort exampleConjunction ExampleSort.i

/-- Example 10.6.2 (companion): `TERM(C)_s` for the example conjunction —
the sort-`s` subterm set `{b, c, f(a,b), g(c,a), g(f(a,b),a)}`. -/
@[blueprint "chap10__example_10_6_2"]
def exampleTermSetS : Set (MSTerm exampleLanguage ExampleSort.s) :=
  termSetOfSort exampleConjunction ExampleSort.s

/-- Example 10.6.2 (companion): The seed relation `E = {(f(a,b), c)}`
(the single positive equation), fed to `msCongruenceClosure` on `G(C)` —
the example instance of `positiveEquationRelation`. -/
@[blueprint "chap10__example_10_6_2"]
def exampleE :
    (graphOfConjunction exampleConjunction).Node →
      (graphOfConjunction exampleConjunction).Node → Prop :=
  positiveEquationRelation exampleConjunction

/-- Lemma 10.6.2 (companion): Two graph nodes with equal underlying sorted
terms are equal (the membership proof is a `Prop`, so irrelevant). -/
@[blueprint "chap10__lemma_10_6_2"]
theorem node_eq_of_val_eq {L : MSLanguage} {C : MSFormula L}
    {p q : (graphOfConjunction C).Node} (h : p.1 = q.1) : p = q 

/-- The six shared nodes of the graph in Example 10.6.1. -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleNode where
  | a | b | c | fab | gca | gfaba
  deriving DecidableEq

/-- The sorted term named by each node. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodeTerm : ExampleNode → MSTermSig exampleLanguage
  | .a => ⟨ExampleSort.i, exampleTerm_a⟩
  | .b => ⟨ExampleSort.s, exampleTerm_b⟩
  | .c => ⟨ExampleSort.s, exampleTerm_c⟩
  | .fab => ⟨ExampleSort.s, exampleTerm_fab⟩
  | .gca => ⟨ExampleSort.s, exampleTerm_gca⟩
  | .gfaba => ⟨ExampleSort.s, exampleTerm_gfaba⟩

/-- The labels of the six nodes use exactly the five printed symbols. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodeLabel : ExampleNode → ExampleSym
  | .a => .a
  | .b => .b
  | .c => .c
  | .fab => .f
  | .gca | .gfaba => .g

/-- Ordered ports, with repeated occurrences sharing the same node. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodePorts : ExampleNode → List ExampleNode
  | .a | .b | .c => []
  | .fab => [.a, .b]
  | .gca => [.c, .a]
  | .gfaba => [.fab, .a]

/-- Every displayed node belongs to TERM(C). -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleNode_mem (n : ExampleNode) :
    termSetOfConjunction exampleConjunction (exampleNodeTerm n)

/-- The displayed node as an actual vertex of G(C). -/
@[blueprint "chap10__example_10_6_1"]
def exampleGraphNode (n : ExampleNode) : (graphOfConjunction exampleConjunction).Node :=
  ⟨exampleNodeTerm n, exampleNode_mem n⟩

/-- Exactly six distinct vertices: each vertex has one displayed name. -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleGraphNodes_exact (p : (graphOfConjunction exampleConjunction).Node) :
    ∃ n, exampleGraphNode n = p ∧ ∀ m, exampleGraphNode m = p → m = n

/-- The two fibers are exactly the printed singleton and five-element set. -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleTermFibers_exact :
    (∀ t, exampleTermSetI t ↔ t = exampleTerm_a) ∧
    (∀ t, exampleTermSetS t ↔ t = exampleTerm_b ∨ t = exampleTerm_c ∨
      t = exampleTerm_fab ∨ t = exampleTerm_gca ∨ t = exampleTerm_gfaba)

/-- The five symbols, regarded as occurring symbols of G(C). -/
@[blueprint "chap10__example_10_6_1"]
def exampleGraphSymbol : ExampleSym → (graphOfConjunction exampleConjunction).Sigma.symbols
  | .a => .const ExampleSort.i .a (exampleNode_mem .a)
  | .b => .const ExampleSort.s .b (exampleNode_mem .b)
  | .c => .const ExampleSort.s .c (exampleNode_mem .c)
  | .f => .func .f ⟨exampleFArgs exampleTerm_a exampleTerm_b, exampleNode_mem .fab⟩
  | .g => .func .g ⟨exampleGArgs exampleTerm_c exampleTerm_a, exampleNode_mem .gca⟩

/-- The actual graph labels agree with the six-node diagram. -/
@[blueprint "chap10__example_10_6_1"]
theorem exampleGraphLabels (n : ExampleNode) :
    (graphOfConjunction exampleConjunction).Lambda (exampleGraphNode n) =
      exampleGraphSymbol (exampleNodeLabel n)

/-- The entire ordered successor list agrees with the diagram at every node. -/
@[blueprint "chap10__example_10_6_1"]
theorem exampleGraphPorts (n : ExampleNode) :
    List.ofFn ((graphOfConjunction exampleConjunction).delta (exampleGraphNode n)) =
      (exampleNodePorts n).map exampleGraphNode

/-- The only seed pair is the oriented positive equation (f(a,b),c). -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleE_exact (p q : (graphOfConjunction exampleConjunction).Node) :
    exampleE p q ↔ p = exampleGraphNode .fab ∧ q = exampleGraphNode .c

/-- The four blocks, including both singleton classes. -/
@[blueprint "chap10__example_10_6_2"]
def exampleClass : ExampleNode → Fin 4
  | .a => 0
  | .b => 1
  | .fab | .c => 2
  | .gfaba | .gca => 3

/-- The closure on all vertices is exactly the four displayed blocks. -/
@[attach_debt, blueprint "chap10__example_10_6_2"]
theorem exampleClosureClasses (p q : (graphOfConjunction exampleConjunction).Node) :
    msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE
      (positiveEquationRelation_sortSupported exampleConjunction) p q ↔
    ∃ m n : ExampleNode, p = exampleGraphNode m ∧ q = exampleGraphNode n ∧
      exampleClass m = exampleClass n

/-- The two nontrivial identifications in the displayed partition. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleClosurePairs
    (pfab pc pgfaba pgca : (graphOfConjunction exampleConjunction).Node)
    (hpfab : pfab.1 = ⟨ExampleSort.s, exampleTerm_fab⟩)
    (hpc : pc.1 = ⟨ExampleSort.s, exampleTerm_c⟩)
    (hpgfaba : pgfaba.1 = ⟨ExampleSort.s, exampleTerm_gfaba⟩)
    (hpgca : pgca.1 = ⟨ExampleSort.s, exampleTerm_gca⟩) :
    msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE (positiveEquationRelation_sortSupported exampleConjunction)
        pfab pc ∧
      msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE (positiveEquationRelation_sortSupported exampleConjunction)
        pgfaba pgca 

/-- The five sort-s elements of the printed candidate algebra, before quotienting. -/
@[blueprint "chap10__example_10_6_2"]
inductive ExampleValueS where
  | b | c | fab | gca | gfaba
  deriving DecidableEq

/-- The candidate has one element of sort i and five of sort s. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCarrier : ExampleSort → Type
  | .i => ExampleConstI
  | .s => ExampleValueS

/-- The printed f-table: f(a,b) is its node; the other four results are b. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateF (_ : ExampleConstI) : ExampleValueS → ExampleValueS
  | .b => .fab
  | .c | .fab | .gca | .gfaba => .b

/-- The printed g-table: two occurring applications and three default values b. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateG : ExampleValueS → ExampleConstI → ExampleValueS
  | .c, .a => .gca
  | .fab, .a => .gfaba
  | .b, .a | .gca, .a | .gfaba, .a => .b

/-- The six-node pre-quotient candidate algebra of Example 10.6.2. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateAlgebra : MSStructure exampleLanguage where
  carrier := exampleCarrier
  carrierNonempty := fun s => by cases s; exact ⟨.a⟩; exact ⟨.b⟩
  interpConst := fun s => match s with
    | .i => fun _ => .a
    | .s => fun c => match c with | .b => .b | .c => .c
  interpFunc := fun f => match f with
    | .f => fun xs => exampleCandidateF (xs ⟨0, by decide⟩) (xs ⟨1, by decide⟩)
    | .g => fun xs => exampleCandidateG (xs ⟨0, by decide⟩) (xs ⟨1, by decide⟩)
  interpPred := fun p => nomatch p

/-- Well-sorted arguments for f in the candidate algebra. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateFArgs (x : ExampleConstI) (y : ExampleValueS) :
    (j : Fin (exampleLanguage.funRank ExampleFunc.f).1.length) →
      exampleCandidateAlgebra.carrier ((exampleLanguage.funRank ExampleFunc.f).1.get j)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- Well-sorted arguments for g in the candidate algebra. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateGArgs (x : ExampleValueS) (y : ExampleConstI) :
    (j : Fin (exampleLanguage.funRank ExampleFunc.g).1.length) →
      exampleCandidateAlgebra.carrier ((exampleLanguage.funRank ExampleFunc.g).1.get j)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- All ten entries of the printed table, checked against the structure operations. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleCandidateTable :
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .b) = .fab ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .b .a) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .c .a) = .gca ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .c) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .fab .a) = .gfaba ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .fab) = .b ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .gca) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .gca .a) = .b ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .gfaba) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .gfaba .a) = .b

/-- Example 10.6.2 (companion): The negated equation `¬(g(f(a,b),a) =̇_s
g(c,a))` is the right conjunct of the example conjunction. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleConjunction_contains_neg :
    msConjunctContains exampleConjunction
      (MSFormula.neg (MSFormula.eq_ (L := exampleLanguage) rfl ExampleSort.s
        exampleTerm_gfaba exampleTerm_gca)) 

/-- Example 10.6.2 (companion): `g(f(a,b),a)` and `g(c,a)` both lie in
`TERM(C)`, being the two terms of the negated equation of `C`. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_gfaba_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_gfaba⟩ 

@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_gca_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_gca⟩ 

/-- Example 10.6.2 (companion): `f(a,b)` and `c` both lie in `TERM(C)`,
being subterms of terms occurring in the conjunction. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_fab_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_fab⟩ 

@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_c_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_c⟩ 

/-- Example 10.6.2: The witness that `g(f(a,b),a)` and `g(c,a)` are
`R*`-congruent (the same class) — the collision of Lemma 10.6.2 for the
example. Packaged as the existence of the two `TERM(C)` nodes for
`g(f(a,b),a)` and `g(c,a)` together with the closure proof. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleCollision :
    ∃ (hL : exampleLanguage.hasEquality = true) (r v : MSTerm exampleLanguage ExampleSort.s)
      (p q : (graphOfConjunction exampleConjunction).Node),
      msConjunctContains exampleConjunction
        (MSFormula.neg (MSFormula.eq_ hL ExampleSort.s r v)) ∧
        p.1 = ⟨ExampleSort.s, r⟩ ∧ q.1 = ⟨ExampleSort.s, v⟩ ∧
        msCongruenceClosure (graphOfConjunction exampleConjunction)
          (positiveEquationRelation exampleConjunction) (positiveEquationRelation_sortSupported exampleConjunction) p q

/-- Example 10.6.2: The conclusion that the example conjunction `C` is
unsatisfiable, obtained from `msUnsatisfiable_iff_collision` (Lemma
10.6.2) applied to `exampleCollision`. A genuine proposition
(`msUnsatisfiable exampleConjunction`), NOT `True := trivial`. Proof body
`sorry` (it depends on the `msIsConjunctionOfEquations` hypothesis of
Lemma 10.6.2 for the example conjunction). -/
@[blueprint "chap10__example_10_6_2" (main := true)]
theorem exampleDecision : msUnsatisfiable exampleConjunction 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
