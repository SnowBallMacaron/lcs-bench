import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Example.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.Propositional.Semantics

/-- Example 10.6.3 (companion): the single sort `ι` of the one-sorted
example language. -/
@[blueprint "chap10__example_10_6_3"]
inductive ExamplePredSort : Type where
  | iota : ExamplePredSort

/-- Example 10.6.3 (companion): the function symbols `FS = {f}` — the
single unary function symbol `f` of rank `([ι], ι)`. -/
@[blueprint "chap10__example_10_6_3"]
inductive ExamplePredFunc : Type where
  | f : ExamplePredFunc

/-- Example 10.6.3 (companion): the constants of sort `ι` — just `a`
(`CS_ι = {a}`). -/
@[blueprint "chap10__example_10_6_3"]
inductive ExamplePredConst : Type where
  | a : ExamplePredConst

/-- Example 10.6.3 (companion): the predicate symbols `PS = {P}` — the
single unary predicate symbol `P` of arity `[ι]`. -/
@[blueprint "chap10__example_10_6_3"]
inductive ExamplePredPred : Type where
  | P : ExamplePredPred

/-- Example 10.6.3 (companion): the concrete one-sorted many-sorted
language with `S = {ι}`, `FS = {f}` and `funRank f = ([ι], ι)`,
`CS_ι = {a}`, `PS = {P}` with `predArity P = [ι]`, `hasEquality := true`.
The unary function symbol `f` and the unary predicate symbol `P` live
here. Realizes "unary function symbol `f`" and "unary predicate symbol
`P`". -/
@[blueprint "chap10__example_10_6_3"]
def examplePredLanguage : MSLanguage where
  SortType := ExamplePredSort
  someSort := ExamplePredSort.iota
  funSymbols := ExamplePredFunc
  funRank
    | .f => ([ExamplePredSort.iota], ExamplePredSort.iota)
  funRank_nonempty := fun fn => by cases fn <;> decide
  constSymbols
    | .iota => ExamplePredConst
  predSymbols := ExamplePredPred
  predArity
    | .P => [ExamplePredSort.iota]
  hasEquality := true

/-- Example 10.6.3 (companion): argument vector for the unary function
`f`, whose arity is `[ι]`: a single argument of sort `ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredFArg (t : MSTerm examplePredLanguage ExamplePredSort.iota) :
    (i : Fin (examplePredLanguage.funRank ExamplePredFunc.f).1.length) →
      MSTerm examplePredLanguage
        ((examplePredLanguage.funRank ExamplePredFunc.f).1.get i)
  | ⟨0, _⟩ => t

/-- Example 10.6.3 (companion): argument vector for the unary predicate
`P`, whose arity is `[ι]`: a single argument of sort `ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredPArg (t : MSTerm examplePredLanguage ExamplePredSort.iota) :
    (i : Fin (examplePredLanguage.predArity ExamplePredPred.P).length) →
      MSTerm examplePredLanguage
        ((examplePredLanguage.predArity ExamplePredPred.P).get i)
  | ⟨0, _⟩ => t

/-- Example 10.6.3 (companion): the constant `a` of sort `ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredTerm_a : MSTerm examplePredLanguage ExamplePredSort.iota :=
  MSTerm.const (L := examplePredLanguage) ExamplePredSort.iota ExamplePredConst.a

/-- Example 10.6.3 (companion): the term `f t` of sort `ι` (one
application of `f`). -/
@[blueprint "chap10__example_10_6_3"]
def examplePredApplyF (t : MSTerm examplePredLanguage ExamplePredSort.iota) :
    MSTerm examplePredLanguage ExamplePredSort.iota :=
  MSTerm.func (L := examplePredLanguage) ExamplePredFunc.f (examplePredFArg t)

/-- Example 10.6.3 (companion): the term `f(a)` of sort `ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredTerm_fa : MSTerm examplePredLanguage ExamplePredSort.iota :=
  examplePredApplyF examplePredTerm_a

/-- Example 10.6.3 (companion): the term `f³(a) = f(f(f(a)))` of sort
`ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredTerm_f3a : MSTerm examplePredLanguage ExamplePredSort.iota :=
  examplePredApplyF (examplePredApplyF examplePredTerm_fa)

/-- Example 10.6.3 (companion): the term `f⁵(a) = f(f(f(f(f(a)))))` of
sort `ι`. -/
@[blueprint "chap10__example_10_6_3"]
def examplePredTerm_f5a : MSTerm examplePredLanguage ExamplePredSort.iota :=
  examplePredApplyF (examplePredApplyF examplePredTerm_f3a)

/-- Example 10.6.3 (companion): the concrete conjunction of literals
`C = (f³(a) ≐_ι a) ∧ (f⁵(a) ≐_ι a) ∧ P(a) ∧ ¬ P(f(a))` — two equations,
one positive predicate atom `P(a)`, and one negated atom `¬P(f(a))`.
Realizes "example conjunction `C` with predicate". -/
@[blueprint "chap10__example_10_6_3"]
def examplePredConjunction : MSFormula examplePredLanguage :=
  MSFormula.conj
    (MSFormula.eq_ (L := examplePredLanguage) rfl ExamplePredSort.iota
      examplePredTerm_f3a examplePredTerm_a)
    (MSFormula.conj
      (MSFormula.eq_ (L := examplePredLanguage) rfl ExamplePredSort.iota
        examplePredTerm_f5a examplePredTerm_a)
      (MSFormula.conj
        (MSFormula.pred (L := examplePredLanguage) ExamplePredPred.P
          (examplePredPArg examplePredTerm_a))
        (MSFormula.neg
          (MSFormula.pred (L := examplePredLanguage) ExamplePredPred.P
            (examplePredPArg examplePredTerm_fa)))))

/-- Example 10.6.3 (companion): the converted conjunction
`C' = msEncodeConjunction examplePredLanguage examplePredConjunction`
over the bool-extended language — the two equations relabelled, the
positive atom `P(a)` replaced by `(P(a) ≐_bool ⊤)` and the negated atom
`¬P(f(a))` by `¬(P(f(a)) ≐_bool ⊤)`. Realizes "converted example
conjunction `C'`". A genuine application of the real encoder (NOT the
identity). -/
@[blueprint "chap10__example_10_6_3"]
def examplePredConjunctionEncoded :
    MSFormula (boolExtendedLanguage examplePredLanguage) :=
  msEncodeConjunction examplePredLanguage examplePredConjunction

/-- Example 10.6.3 (companion): the labeled graph `G(C')` whose nine nodes
`V1..V9` stand for the subterms `a, f(a), f²(a), f³(a), f⁴(a), f⁵(a)` and
the bool-sorted `⊤, P(a), P(f(a))`. Realizes "example graph `G(C)` with
bool node" (it includes the bool node `⊤` and the predicate-application
nodes). -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleGraphPred : MSLabeledGraph :=
  graphOfConjunction (L := boolExtendedLanguage examplePredLanguage)
    examplePredConjunctionEncoded

/-- The equation-derived seed, with the two data pairs directed as in C′. -/
@[blueprint "chap10__example_10_6_3"]
def exampleEquationSeedPred :
    exampleGraphPred.Node → exampleGraphPred.Node → Prop :=
  positiveEquationRelation (L := boolExtendedLanguage examplePredLanguage)
    examplePredConjunctionEncoded

/-- The printed seed {(V1,V4),(V1,V6),(V8,V7)}. Here V1 = a,
V4 = f³(a), V6 = f⁵(a), V8 = P(a), and V7 = top. -/
@[blueprint "chap10__example_10_6_3"]
def exampleSeedPred (p q : exampleGraphPred.Node) : Prop :=
  let a : MSTermSig (boolExtendedLanguage examplePredLanguage) :=
    ⟨some ExamplePredSort.iota, msLiftTerm examplePredLanguage examplePredTerm_a⟩
  let f3a : MSTermSig (boolExtendedLanguage examplePredLanguage) :=
    ⟨some ExamplePredSort.iota, msLiftTerm examplePredLanguage examplePredTerm_f3a⟩
  let f5a : MSTermSig (boolExtendedLanguage examplePredLanguage) :=
    ⟨some ExamplePredSort.iota, msLiftTerm examplePredLanguage examplePredTerm_f5a⟩
  let pa : MSTermSig (boolExtendedLanguage examplePredLanguage) :=
    ⟨MSBoolSort examplePredLanguage,
      msPredAsFuncTerm examplePredLanguage ExamplePredPred.P
        (fun ⟨0, _⟩ => msLiftTerm examplePredLanguage examplePredTerm_a)⟩
  let top : MSTermSig (boolExtendedLanguage examplePredLanguage) :=
    ⟨MSBoolSort examplePredLanguage, msTopConst examplePredLanguage⟩
  (p.val = a ∧ q.val = f3a) ∨
    (p.val = a ∧ q.val = f5a) ∨ (p.val = pa ∧ q.val = top)

/-- Each of the three printed seed pairs has one sort. -/
@[attach_debt, blueprint "chap10__example_10_6_3"]
theorem exampleSeedPred_sortSupported : MSSortSupported exampleGraphPred exampleSeedPred

/-- Example 10.6.3 (companion): the congruence closure `R'` of the seed
`R` on `G(C')`, under which `V1..V6` (`a, f(a), …, f⁵(a)`) all become
equivalent and, via the predicate/function congruence step, `P(f(a))`
becomes equivalent to `⊤`. Realizes "example congruence closure `R'`". -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleClosurePred :
    exampleGraphPred.Node → exampleGraphPred.Node → Prop :=
  msCongruenceClosure exampleGraphPred exampleSeedPred exampleSeedPred_sortSupported

/-- Reversing the two data seed pairs preserves their least congruence closure. -/
@[attach_debt, blueprint "chap10__example_10_6_3"]
theorem exampleClosurePred_eq_equationClosure :
    exampleClosurePred = msCongruenceClosure exampleGraphPred exampleEquationSeedPred
      (positiveEquationRelation_sortSupported examplePredConjunctionEncoded)

-- ===================================================================
-- Example 10.6.3 (companion): the f/P congruence-closure facts for
-- `exampleCollisionPfa` (mirroring Decision's `exampleClosureClasses`)
-- ===================================================================

/-- Example 10.6.3 (companion): the single-argument vector of the lifted
unary function symbol `Sum.inl f` of `L'` carrying one `some ι`-sorted
term. Lets the lifted terms `f^k(a)` over `L'` be written uniformly as
`MSTerm.func (Sum.inl f) (exampleLiftFArg t)`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftFArg
    (t : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota)) :
    (i : Fin ((boolExtendedLanguage examplePredLanguage).funRank
      (Sum.inl ExamplePredFunc.f)).1.length) →
      MSTerm (boolExtendedLanguage examplePredLanguage)
        (((boolExtendedLanguage examplePredLanguage).funRank
          (Sum.inl ExamplePredFunc.f)).1.get i)
  | ⟨0, _⟩ => t

/-- Example 10.6.3 (companion): `f` applied (over `L'`) to a `some ι`-term —
`f(t) = MSTerm.func (Sum.inl f) (exampleLiftFArg t)`. The bool-extended
analogue of `examplePredApplyF`, used to build the tower `a, f(a), …,
f⁵(a)` of `L'`-terms. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftTf
    (t : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota)) :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
    (Sum.inl ExamplePredFunc.f) (exampleLiftFArg t)

/-- Example 10.6.3 (companion): the lifted constant `a` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT0 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  msLiftTerm examplePredLanguage examplePredTerm_a

/-- Example 10.6.3 (companion): `f(a)` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT1 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  exampleLiftTf exampleLiftT0

/-- Example 10.6.3 (companion): `f²(a)` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT2 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  exampleLiftTf exampleLiftT1

/-- Example 10.6.3 (companion): `f³(a)` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT3 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  exampleLiftTf exampleLiftT2

/-- Example 10.6.3 (companion): `f⁴(a)` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT4 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  exampleLiftTf exampleLiftT3

/-- Example 10.6.3 (companion): `f⁵(a)` over `L'`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleLiftT5 :
    MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota) :=
  exampleLiftTf exampleLiftT4

/-- Example 10.6.3 (companion): `msLiftTerm` of `f(t)` over `L'` is
`exampleLiftTf (msLiftTerm t)` — the lift commutes with one `f`
application (the sort/index casts of `msLiftTerm` are `rfl` for the unary
`f`, leaving the single argument `msLiftTerm t`). -/
@[blueprint "chap10__example_10_6_3"]
theorem example_lift_applyF (t : MSTerm examplePredLanguage ExamplePredSort.iota) :
    msLiftTerm examplePredLanguage (examplePredApplyF t)
      = exampleLiftTf (msLiftTerm examplePredLanguage t) 

/-- Example 10.6.3 (companion): `msLiftTerm a = exampleLiftT0`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_lift_a :
    msLiftTerm examplePredLanguage examplePredTerm_a = exampleLiftT0 

/-- Example 10.6.3 (companion): `msLiftTerm (f a) = exampleLiftT1`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_lift_fa :
    msLiftTerm examplePredLanguage examplePredTerm_fa = exampleLiftT1 

/-- Example 10.6.3 (companion): `msLiftTerm (f³ a) = exampleLiftT3`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_lift_f3a :
    msLiftTerm examplePredLanguage examplePredTerm_f3a = exampleLiftT3 

/-- Example 10.6.3 (companion): `msLiftTerm (f⁵ a) = exampleLiftT5`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_lift_f5a :
    msLiftTerm examplePredLanguage examplePredTerm_f5a = exampleLiftT5 

/-- Example 10.6.3 (companion): the positive equation `f⁵(a) ≐ a` (second
conjunct of `C'`) — the seed pair `f⁵(a) ~ a`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_contains_f5a_eq_a :
    Decision.msConjunctContains examplePredConjunctionEncoded
      (MSFormula.eq_ (L := boolExtendedLanguage examplePredLanguage) rfl
        (some ExamplePredSort.iota) exampleLiftT5 exampleLiftT0) 

/-- Example 10.6.3 (companion): subterm-closure step over `L'` — if
`f(t)` is a subterm of `T`, then so is its argument `t`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_sub_step
    {T : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota)}
    (t : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota))
    (h : Decision.msTermSubterms T ⟨some ExamplePredSort.iota, exampleLiftTf t⟩) :
    Decision.msTermSubterms T ⟨some ExamplePredSort.iota, t⟩ 

/-- Example 10.6.3 (companion): `f⁵(a)` is a subterm of itself. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T5 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT5⟩ 

/-- Example 10.6.3 (companion): `f⁴(a)` is a subterm of `f⁵(a)`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T4 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT4⟩ 

/-- Example 10.6.3 (companion): `f³(a)` is a subterm of `f⁵(a)`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T3 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT3⟩ 

/-- Example 10.6.3 (companion): `f²(a)` is a subterm of `f⁵(a)`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T2 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT2⟩ 

/-- Example 10.6.3 (companion): `f(a)` is a subterm of `f⁵(a)`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T1 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT1⟩ 

/-- Example 10.6.3 (companion): `a` is a subterm of `f⁵(a)`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_subT5_T0 :
    Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, exampleLiftT0⟩ 

/-- Example 10.6.3 (companion): every subterm of `f⁵(a)` lies in
`TERM(C')` (it is a subterm of the term `f⁵(a)` of the positive equation
`f⁵(a) ≐ a`). -/
@[blueprint "chap10__example_10_6_3"]
theorem example_memTk
    (k : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota))
    (h : Decision.msTermSubterms exampleLiftT5 ⟨some ExamplePredSort.iota, k⟩) :
    Decision.termSetOfConjunction examplePredConjunctionEncoded
      ⟨some ExamplePredSort.iota, k⟩ 

/-- Example 10.6.3 (companion): the `G(C')`-node for `a`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleNodeT0 : exampleGraphPred.Node :=
  ⟨⟨some ExamplePredSort.iota, exampleLiftT0⟩, example_memTk exampleLiftT0 example_subT5_T0⟩

/-- Example 10.6.3 (companion): the `G(C')`-node for `f(a)`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleNodeT1 : exampleGraphPred.Node :=
  ⟨⟨some ExamplePredSort.iota, exampleLiftT1⟩, example_memTk exampleLiftT1 example_subT5_T1⟩

/-- Example 10.6.3: `f(a) ↔* a` in the closure. By repeated `f`-congruence
of the two seeds and transitivity, ALL of `a, f(a), …, f⁵(a)` collapse to
one class; in particular `f(a) ~ a`. Concretely: `f³a~a` and `f⁵a~a` ⇒
(f-cong) `f⁴a~fa`, `f⁵a~f²a` ⇒ `f²a~a` (trans through `f⁵a~a`) ⇒ (f-cong)
`f³a~fa` ⇒ `fa~a` (trans through `f³a~a`). -/
@[attach_debt, blueprint "chap10__example_10_6_3"]
theorem example_fa_eq_a : exampleClosurePred exampleNodeT1 exampleNodeT0 

-- ===================================================================
-- Example 10.6.3 (companion): the predicate-congruence step P(f(a)) ~ ⊤
-- ===================================================================

/-- Example 10.6.3 (companion): the single-argument vector of the
predicate-as-function symbol `Sum.inr P` of `L'` carrying one `some ι`-term
(the bool-output analogue of `exampleLiftFArg`). -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def examplePredArg
    (t : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota)) :
    (i : Fin ((boolExtendedLanguage examplePredLanguage).funRank
      (Sum.inr ⟨ExamplePredPred.P, by decide⟩)).1.length) →
      MSTerm (boolExtendedLanguage examplePredLanguage)
        (((boolExtendedLanguage examplePredLanguage).funRank
          (Sum.inr ⟨ExamplePredPred.P, by decide⟩)).1.get i)
  | ⟨0, _⟩ => by
      have hsort : (((boolExtendedLanguage examplePredLanguage).funRank
          (Sum.inr ⟨ExamplePredPred.P, by decide⟩)).1.get ⟨0, by decide⟩)
          = some ExamplePredSort.iota := rfl
      exact hsort ▸ t

/-- Example 10.6.3 (companion): the bool-sorted predicate-application term
`P(t)` over `L'`, `MSTerm.func (Sum.inr P) (examplePredArg t)`. The bool
nodes `P(a)`, `P(f(a))` of `G(C')` carry this term. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def examplePredTermP
    (t : MSTerm (boolExtendedLanguage examplePredLanguage) (some ExamplePredSort.iota)) :
    MSTerm (boolExtendedLanguage examplePredLanguage) (MSBoolSort examplePredLanguage) :=
  MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
    (Sum.inr ⟨ExamplePredPred.P, by decide⟩) (examplePredArg t)

/-- Example 10.6.3 (companion): the positive bool-equation `P(a) ≐_bool ⊤`
(third conjunct of `C'`) — the seed pair `P(a) ~ ⊤`. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_contains_Pa_eq_top :
    Decision.msConjunctContains examplePredConjunctionEncoded
      (MSFormula.eq_ (L := boolExtendedLanguage examplePredLanguage) rfl
        (MSBoolSort examplePredLanguage)
        (examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_a))
        (msTopConst examplePredLanguage)) 

/-- Example 10.6.3 (companion): the negated bool-equation
`¬(P(f(a)) ≐_bool ⊤)` (fourth conjunct of `C'`) — the negated equation of
the collision. -/
@[blueprint "chap10__example_10_6_3"]
theorem example_contains_neg_Pfa_eq_top :
    Decision.msConjunctContains examplePredConjunctionEncoded
      (MSFormula.neg (MSFormula.eq_ (L := boolExtendedLanguage examplePredLanguage) rfl
        (MSBoolSort examplePredLanguage)
        (examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa))
        (msTopConst examplePredLanguage))) 

/-- Example 10.6.3 (companion): the bool node `⊤` lies in `TERM(C')` (RHS
of the positive equation `P(a) ≐ ⊤`). -/
@[blueprint "chap10__example_10_6_3"]
theorem example_memTop :
    Decision.termSetOfConjunction examplePredConjunctionEncoded
      ⟨MSBoolSort examplePredLanguage, msTopConst examplePredLanguage⟩ 

/-- Example 10.6.3 (companion): the bool node `P(f(a))` lies in `TERM(C')`
(LHS of the negated equation `¬(P(f(a)) ≐ ⊤)`). -/
@[blueprint "chap10__example_10_6_3"]
theorem example_memPfa :
    Decision.termSetOfConjunction examplePredConjunctionEncoded
      ⟨MSBoolSort examplePredLanguage,
        examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa)⟩ 

/-- Example 10.6.3 (companion): the `G(C')`-node for `f(a)` carried by the
lifted term `msLiftTerm (f a)` (the `ι`-argument feeding the predicate
node), equal to `exampleNodeT1` up to the `example_lift_fa` rewrite. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleNodeFa : exampleGraphPred.Node :=
  ⟨⟨some ExamplePredSort.iota, msLiftTerm examplePredLanguage examplePredTerm_fa⟩,
    example_memTk _ (by rw [example_lift_fa]; exact example_subT5_T1)⟩

/-- Example 10.6.3 (companion): the `G(C')`-node for `a` carried by the
lifted term `msLiftTerm a`. -/
@[blueprint "chap10__example_10_6_3"]
noncomputable def exampleNodeA : exampleGraphPred.Node :=
  ⟨⟨some ExamplePredSort.iota, msLiftTerm examplePredLanguage examplePredTerm_a⟩,
    example_memTk _ (by rw [example_lift_a]; exact example_subT5_T0)⟩

/-- Example 10.6.3 (companion): `f(a) ↔* a` on the lifted-term nodes
`exampleNodeFa`/`exampleNodeA` (transport of `example_fa_eq_a` across the
`example_lift_fa`/`example_lift_a` term equalities). -/
@[blueprint "chap10__example_10_6_3"]
theorem example_fa_eq_a_lifted : exampleClosurePred exampleNodeFa exampleNodeA 

/-- Example 10.6.3: `P(f(a)) ↔* ⊤` in the closure. From `f(a) ~ a`
(`example_fa_eq_a_lifted`) the `P`-congruence step gives `P(f(a)) ~ P(a)`;
with the seed `P(a) ~ ⊤` and transitivity, `P(f(a)) ~ ⊤`. -/
@[attach_debt, blueprint "chap10__example_10_6_3"]
theorem example_Pfa_top :
    exampleClosurePred
      ⟨⟨MSBoolSort examplePredLanguage,
        examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa)⟩, example_memPfa⟩
      ⟨⟨MSBoolSort examplePredLanguage, msTopConst examplePredLanguage⟩, example_memTop⟩ 


/-- Example 10.6.3: the witness that `P(f(a))` and `⊤` are `R'`-congruent
(the bool-sort collision `V9 ↔* V7`). The two `TERM(C')` nodes for
`P(f(a))` and `⊤` together with the closure proof. -/
@[blueprint "chap10__example_10_6_3"]
theorem exampleCollisionPfa :
    ∃ (p q : exampleGraphPred.Node),
      p.1 = ⟨MSBoolSort examplePredLanguage,
        msPredAsFuncTerm examplePredLanguage ExamplePredPred.P
          (fun i => by
            have hi : i.val < (examplePredLanguage.predArity ExamplePredPred.P).length := by
              have := i.isLt
              simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
                using this
            have hsort :
                (((boolExtendedLanguage examplePredLanguage).funRank
                  (Sum.inr ⟨ExamplePredPred.P, by decide⟩)).1.get i) =
                  some ((examplePredLanguage.predArity ExamplePredPred.P).get
                    ⟨i.val, hi⟩) := by
              simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
              all_goals exact List.getElem_map some
            exact hsort ▸ msLiftTerm examplePredLanguage examplePredTerm_fa)⟩ ∧
        q.1 = ⟨MSBoolSort examplePredLanguage, msTopConst examplePredLanguage⟩ ∧
        exampleClosurePred p q 

/-- Example 10.6.3 (companion): the concrete example conjunction
`C = (f³(a) ≐ a) ∧ (f⁵(a) ≐ a) ∧ P(a) ∧ ¬P(f(a))` is a conjunction of
literals — a right-nested conjunction whose four leaves are two equations
(`eq_`, atomic), a positive predicate atom `P(a)` (`pred`, atomic), and a
negated predicate atom `¬P(f(a))` (`neg (pred …)`, a negated literal). This
discharges the faithfulness hypothesis `hC` of Lemma 10.6.4 for the worked
example. -/
@[blueprint "chap10__example_10_6_3"]
theorem examplePredConjunction_isConjOfLiterals :
    Decision.msIsConjunctionOfLiterals examplePredConjunction 

/-- Example 10.6.3 (companion): every literal conjunct of the example
conjunction `C` is a (negated) equation or (negated) predicate atom — NONE
is bare `falsum`/`neg falsum`. Its conjuncts are `f³(a)≐a`, `f⁵(a)≐a`,
`P(a)`, `¬P(f(a))`, all distinct from `⊥`. This discharges the faithfulness
hypothesis `hNoBot` of Lemma 10.6.4 for the worked example. -/
@[blueprint "chap10__example_10_6_3"]
theorem examplePredConjunction_noBot :
    ∀ X, Decision.msConjunctContains examplePredConjunction X →
      MSFormula.isLiteral X →
      (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum) 

/-- Example 10.6.3: the conclusion that the concrete conjunction `C` is
unsatisfiable — the proposition `Decision.msUnsatisfiable
examplePredConjunction`, established by Lemma 10.6.4
(`msUnsatisfiable_iff_collision_withPredicates`) applied to the bool-sort
collision `P(f(a)) ↔* ⊤` (`exampleCollisionPfa`), the negated equation
`¬(P(f(a)) ≐ ⊤)` of `C'` whose terms collide. A genuine proposition (NOT
`True := trivial`). Realizes "example unsatisfiability verdict". Proof
body `sorry`.

FIX (mirrors the `hC` addition to the main lemma): the lemma now requires
`Decision.msIsConjunctionOfLiterals examplePredConjunction`, supplied by
the companion `examplePredConjunction_isConjOfLiterals`; the `rw` is
replaced by `apply (… examplePredConjunction_isConjOfLiterals).mpr`. -/
@[blueprint "chap10__example_10_6_3" (main := true)]
theorem examplePredicateDecision :
    Decision.msUnsatisfiable examplePredConjunction 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
end

