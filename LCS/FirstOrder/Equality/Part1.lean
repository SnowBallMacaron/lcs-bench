import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import Attach
import LCS.FirstOrder.Equality.Part1.ProofsStamp

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

/-- Definition 5.6.1 (companion): fold a list of formulae into a
conjunction. Returns the single formula if the list has one element;
conjoins left-to-right for multiple elements. For an empty list,
returns the provided default (trivial equality reflexivity formula). -/
@[blueprint "chap5__definition_5_6_1"]
def conjoinFormulae {L : Language} (default : FormulaN L) :
    List (FormulaN L) → FormulaN L
  | [] => default
  | [A] => A
  | A :: rest => FormulaN.conj A (conjoinFormulae default rest)

-- ===================================================================
-- Definition 5.6.1 (companion def): eqPairsList
-- ===================================================================

/-- Definition 5.6.1 (companion): build a list of equality pairs
(si doteq ti) from two Fin-indexed families of terms, collecting
indices 0..n-1. Requires `hL : L.hasEquality = true` so `.eq_`
can be constructed. -/
@[blueprint "chap5__definition_5_6_1"]
def eqPairsList {L : Language} (hL : L.hasEquality = true) {n : Nat}
    (ss ts : Fin n → Term L) : List (FormulaN L) :=
  (List.finRange n).map (fun i => FormulaN.eq_ hL (ss i) (ts i))

-- ===================================================================
-- Definition 5.6.1 (companion def): eqCongruenceImplFunc
-- ===================================================================

/-- Definition 5.6.1 (companion): The formula
(s1 doteq t1) and ... and (sn doteq tn) implies (f(s1,...,sn) doteq f(t1,...,tn)).
Builds the conjunction of equalities for each argument position, then forms
the implication to the equality of function applications. For n = 0, the
antecedent defaults to a reflexivity tautology. Requires
`hL : L.hasEquality = true`. -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplFunc (L : Language) (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) : FormulaN L :=
  let pairs := eqPairsList hL ss ts
  let consequent := FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)
  let default := consequent  -- trivial case: 0-ary function
  FormulaN.impl (conjoinFormulae default pairs) consequent

-- ===================================================================
-- Definition 5.6.1 (companion def): eqCongruenceImplPred
-- ===================================================================

/-- Definition 5.6.1 (companion): The formula
((s1 doteq t1) and ... and (sn doteq tn) and P(s1,...,sn)) implies P(t1,...,tn).
Builds the conjunction of equalities and the premise predicate application,
then forms the implication to the conclusion predicate application.
For n = 0, the antecedent is just P(s1,...,sn). Requires
`hL : L.hasEquality = true`. -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplPred (L : Language) (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) : FormulaN L :=
  let pairs := eqPairsList hL ss ts
  let premisePred := FormulaN.predN P ss
  let consequent := FormulaN.predN P ts
  let antecedent := conjoinFormulae premisePred (pairs ++ [premisePred])
  FormulaN.impl antecedent consequent


-- ===================================================================
-- Definition 5.6.1: IsHintikkaSetEq
-- ===================================================================

/-- Definition 5.6.1 (companion — base): The base Hintikka conditions
H0-H6 on a signed set S, with H a term algebra over its occurrence
language L_S. Equality atoms are permitted, and quantified components
must satisfy the free-for condition. -/
@[blueprint "chap5__definition_5_6_1"]
structure IsHintikkaSetEqBase (L : Language) (H : Set (Term L))
    (S : Set (SignedFormula L)) : Prop where
  /-- H is a term algebra over the symbols occurring in S. -/
  hTA : IsTermAlgebraOver L S H
  /-- H0: No atomic formula and its conjugate are both in S -/
  h0 : ∀ (A : FormulaN L), A.isAtomic = true →
    ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S)
  /-- H1: If a type-A formula is in S, then both components are in S -/
  h1 : ∀ (a : TypeA L), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S
  /-- H2: If a type-B formula is in S, then at least one component is in S -/
  h2 : ∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S
  /-- H3: Every free-for component C(t), for t in H, belongs to S.
  H6 supplies the required free-for evidence. -/
  h3 : ∀ (c : TypeC L), c.toSigned ∈ S →
    ∀ (t : Term L), t ∈ H → ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ S
  /-- H4: A type-D formula in S has a free-for witness t in H with D(t) in S. -/
  h4 : ∀ (d : TypeD L), d.toSigned ∈ S →
    ∃ (t : Term L), t ∈ H ∧ ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S
  /-- H5: Every variable occurring free in some formula of S is in H -/
  h5 : ∀ (sf : SignedFormula L), sf ∈ S →
    ∀ (x : Nat), x ∈ signedFormulaFreeVars sf → Term.var x ∈ H
  /-- H6: isFreeFor holds for quantified formulae in S -/
  h6 : ∀ (x : Nat) (A : FormulaN L) (t : Term L), t ∈ H →
    (SignedFormula.trueF (.all x A) ∈ S ∨
     SignedFormula.falseF (.all x A) ∈ S ∨
     SignedFormula.trueF (.ex x A) ∈ S ∨
     SignedFormula.falseF (.ex x A) ∈ S) →
    isFreeForN t x A

/-- Definition 5.6.1: A Hintikka set S with equality over a term algebra H
of the occurrence language L_S. Its base conditions include free-for
substitution. H6(i) requires reflexivity for every term in H. H6(ii)
requires function congruence for the function symbols occurring in S;
H6(iii) requires predicate congruence for the predicate
symbols occurring in S. Equality itself is covered by the explicit binary
predicate-congruence condition H6(iii-eq). -/
@[blueprint "chap5__definition_5_6_1" (main := true)]
structure IsHintikkaSetEq (L : Language) (hL : L.hasEquality = true)
    (H : Set (Term L))
    (S : Set (SignedFormula L)) : Prop where
  /-- The base conditions, including the term algebra over L_S and free-for substitution. -/
  base : IsHintikkaSetEqBase L H S
  /-- H6(i): For every term t in H, T(t doteq t) in S -/
  h6i : ∀ (t : Term L), t ∈ H →
    SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ S
  /-- H6(ii): For every function symbol f occurring in S and terms
      s1,...,sn, t1,...,tn in H, the function congruence implication
      is in S -/
  h6ii : ∀ (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
    (ss ts : Fin (L.funArity f) → Term L),
    (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
    SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈ S
  /-- H6(iii): For every predicate symbol P occurring in S and terms
      s1,...,sn, t1,...,tn in H, the predicate congruence implication
      is in S -/
  h6iii : ∀ (P : L.predSymbols) (hPS : P ∈ signedSetPredSyms S)
    (ss ts : Fin (L.predArity P) → Term L),
    (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
    SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈ S
  /-- H6(iii-eq): Equality congruence — H6(iii) applied to doteq.
      Since eq_ is not a predicate symbol in our formalization, this
      condition is stated explicitly: for all s1, s2, t1, t2 in H,
      T(((s1 = t1) /\ (s2 = t2) /\ (s1 = s2)) -> (t1 = t2)) in S.
      This is the textbook's H6(iii) with P = doteq, n = 2. -/
  h6iii_eq : ∀ (s1 s2 t1 t2 : Term L),
    s1 ∈ H → s2 ∈ H → t1 ∈ H → t2 ∈ H →
    SignedFormula.trueF
      (FormulaN.impl
        (FormulaN.conj (FormulaN.eq_ hL s1 t1)
          (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
        (FormulaN.eq_ hL t1 t2)) ∈ S

-- ===================================================================
-- Definition 5.6.2 (companion def): eqCongruenceImplEq
-- ===================================================================

/-- Definition 5.6.2 (companion): The predicate congruence formula
for the binary equality predicate doteq (which the textbook
explicitly lists as included in H6(iii)):
((s1 doteq t1) and (s2 doteq t2) and (s1 doteq s2)) implies
(t1 doteq t2). This is the instance of predicate congruence when
the predicate is doteq with arity 2. Since doteq is not a member of
`L.predSymbols` in our formalization, this case must be stated
explicitly (mirroring `h6iii_eq` in `IsHintikkaSetEq`). -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplEq {L : Language} (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L) :
    FormulaN L :=
  FormulaN.impl
    (FormulaN.conj (FormulaN.eq_ hL s1 t1)
      (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
    (FormulaN.eq_ hL t1 t2)

-- ===================================================================
-- Definition 5.6.2 (companion def): isEqAxiomInstance
-- ===================================================================

/-- Definition 5.6.2 (companion): A formula is an equality axiom
instance if it is (1) of the form t doteq t for some term t,
(2) a function congruence implication eqCongruenceImplFunc L f ss ts,
(3) a predicate congruence implication eqCongruenceImplPred L P ss ts
for a predicate P,
or (4) a predicate congruence instance for the equality predicate
itself (doteq-as-predicate, textbook H6(iii) "including doteq"). -/
@[blueprint "chap5__definition_5_6_2"]
def isEqAxiomInstance {L : Language} (hL : L.hasEquality = true)
    (A : FormulaN L) : Prop :=
  (∃ t : Term L, A = FormulaN.eq_ hL t t) ∨
  (∃ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
    A = eqCongruenceImplFunc L hL f ss ts) ∨
  (∃ (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L),
    A = eqCongruenceImplPred L hL P ss ts) ∨
  (∃ (s1 s2 t1 t2 : Term L), A = eqCongruenceImplEq hL s1 s2 t1 t2)

-- ===================================================================
-- Definition 5.6.2: GEqProofTree
-- ===================================================================

/-- Definition 5.6.2: The set of proof trees for the Gentzen system G_=
(G with equality), indexed by their conclusion sequent. Extends the
indexed `GProofTreeExt` with equality-specific rules: reflexivity,
function congruence, predicate congruence, and the generalized equality
rule which adds multiple equality axiom instances simultaneously. In
addition, G_= includes all G-rules directly (axiom leaves, one-premise
with `GentzenStep1Ext`, two-premise with `GentzenStep2Ext`), so G-rules
and eq-rules may freely interleave — matching textbook Def 5.6.2 which
presents G_= as G with the equality rules added. Section 5.6 is
post-§5.4.8, so G-rules carry the §5.4.8 extended rule schema. Each
rule constructor enforces the structural relationship between premise
and conclusion. -/
@[blueprint "chap5__definition_5_6_2" (main := true)]
inductive GEqProofTree {L : Language} (hL : L.hasEquality = true) :
    Sequent L → Type where
  /-- Embed a standard indexed G proof tree into G_=. -/
  | base {s : Sequent L} (g : GProofTreeExt s) : GEqProofTree hL s
  /-- G-axiom leaf inside G_=: an axiom sequent serves as a leaf of
      the G_= proof tree directly (without the `base` wrapper). -/
  | axiom_ (s : Sequent L) (hAx : isAxiom s) : GEqProofTree hL s
  /-- G one-premise rule lifted into G_=, so G-rules and eq-rules
      may interleave. -/
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem) :
      GEqProofTree hL conc
  /-- G two-premise rule lifted into G_=, so G-rules and eq-rules
      may interleave. -/
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2Ext prem1 prem2 conc)
      (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2) :
      GEqProofTree hL conc
  /-- Equality reflexivity rule: from a premise tree that contains
      `t ≐ t` at the right end of its antecedent, derive a tree whose
      conclusion drops it. -/
  | eqRefl (t : Term L) (Γ Δ : List (FormulaN L))
      (sub : GEqProofTree hL
        (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t]) Δ)) :
      GEqProofTree hL (Sequent.mk Γ Δ)
  /-- Equality function congruence rule, with the axiom last in the antecedent. -/
  | eqFuncCong (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
      (Γ Δ : List (FormulaN L))
      (sub : GEqProofTree hL
        (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ)) :
      GEqProofTree hL (Sequent.mk Γ Δ)
  /-- Equality congruence rule for predicates of arbitrary arity,
      with the axiom last in the antecedent. -/
  | eqPredCong (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L)
      (Γ Δ : List (FormulaN L))
      (sub : GEqProofTree hL
        (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ)) :
      GEqProofTree hL (Sequent.mk Γ Δ)
  /-- Generalized equality rule: append a nonempty list of equality axiom
      instances to the antecedent simultaneously. -/
  | eqGeneral (axioms : List (FormulaN L)) (hne : axioms ≠ [])
      (haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A)
      (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (sub : GEqProofTree hL (Sequent.mk (Γ ++ axioms) Δ)) :
      GEqProofTree hL (Sequent.mk Γ Δ)


-- ===================================================================
-- Definition 5.6.2 (companion): GEqDeductionTree
-- ===================================================================

/-- Definition 5.6.2 (companion): Deduction trees for the Gentzen system G_=,
    indexed by conclusion sequent. Parallel to `GEqProofTree` with free-form
    leaves (no embedded axiom constraint). Textbook Def 5.6.2 introduces both
    notions following Def 5.4.2 / Def 3.4.5; `GEqDeductionTree` formalizes the
    deduction-tree half. Proof trees are precisely the deduction trees whose
    leaves are all axioms (see `GEqDeductionTree.isProof` /
    `GEqDeductionTree.toProofTree`). Since §5.6 is post-§5.4.8, rule
    applications use the §5.4.8 extended rule schema
    (`GentzenStep1Ext` / `GentzenStep2Ext`). -/
@[blueprint "chap5__definition_5_6_2"]
inductive GEqDeductionTree {L : Language} (hL : L.hasEquality = true) :
    Sequent L → Type where
  /-- Free-form leaf: any sequent may serve as a leaf of a deduction tree
      (in contrast to `GEqProofTree.axiom_`, which forces the leaf to be
      an axiom sequent). -/
  | leaf (s : Sequent L) : GEqDeductionTree hL s
  /-- G one-premise rule lifted into G_=, matching `GEqProofTree.onePremise`. -/
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc)
      (sub : GEqDeductionTree hL prem) : GEqDeductionTree hL conc
  /-- G two-premise rule lifted into G_=, matching `GEqProofTree.twoPremise`. -/
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2Ext prem1 prem2 conc)
      (sub1 : GEqDeductionTree hL prem1) (sub2 : GEqDeductionTree hL prem2) :
      GEqDeductionTree hL conc
  /-- Equality reflexivity rule, matching `GEqProofTree.eqRefl`. -/
  | eqRefl (t : Term L) (Γ Δ : List (FormulaN L))
      (sub : GEqDeductionTree hL
        (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t]) Δ)) :
      GEqDeductionTree hL (Sequent.mk Γ Δ)
  /-- Equality function congruence rule, matching `GEqProofTree.eqFuncCong`. -/
  | eqFuncCong (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
      (Γ Δ : List (FormulaN L))
      (sub : GEqDeductionTree hL
        (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ)) :
      GEqDeductionTree hL (Sequent.mk Γ Δ)
  /-- Equality congruence rule for predicates of arbitrary arity, matching `GEqProofTree.eqPredCong`. -/
  | eqPredCong (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L)
      (Γ Δ : List (FormulaN L))
      (sub : GEqDeductionTree hL
        (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ)) :
      GEqDeductionTree hL (Sequent.mk Γ Δ)
  /-- Generalized equality rule with a nonempty appended axiom list,
      matching `GEqProofTree.eqGeneral`. -/
  | eqGeneral (axioms : List (FormulaN L)) (hne : axioms ≠ [])
      (haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A)
      (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (sub : GEqDeductionTree hL (Sequent.mk (Γ ++ axioms) Δ)) :
      GEqDeductionTree hL (Sequent.mk Γ Δ)

end LCS.FirstOrder.Equality
end

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
namespace GEqDeductionTree

/-- Definition 5.6.2 (companion): The conclusion of an indexed G_=
    deduction tree is its type index (same as for `GEqProofTree`). -/
@[blueprint "chap5__definition_5_6_2"]
def conclusion {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (_ : GEqDeductionTree hL s) : Sequent L := s

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} (t : GEqDeductionTree hL s) : t.conclusion = s := rfl

/-- Definition 5.6.2 (companion): A G_= deduction tree is a proof tree
    iff all its leaves are axiom sequents. Bridge between the two
    Def 5.6.2 notions. -/
@[blueprint "chap5__definition_5_6_2"]
def isProof {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqDeductionTree hL s → Prop
  | _, .leaf s => isAxiom s
  | _, .onePremise _ t => t.isProof
  | _, .twoPremise _ t1 t2 => t1.isProof ∧ t2.isProof
  | _, .eqRefl _ _ _ t => t.isProof
  | _, .eqFuncCong _ _ _ _ _ t => t.isProof
  | _, .eqPredCong _ _ _ _ _ t => t.isProof
  | _, .eqGeneral _ _ _ _ _ t => t.isProof

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.2 (companion): Converts a G_= deduction tree whose
    leaves are all axioms into a `GEqProofTree` of the same conclusion. -/
def toProofTree {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → (t : GEqDeductionTree hL s) → t.isProof →
      GEqProofTree hL s
  | _, .leaf s, hax => GEqProofTree.axiom_ s hax
  | _, .onePremise rule t, hp =>
      GEqProofTree.onePremise rule (t.toProofTree hp)
  | _, .twoPremise rule t1 t2, hp =>
      GEqProofTree.twoPremise rule
        (t1.toProofTree hp.1) (t2.toProofTree hp.2)
  | _, .eqRefl t Γ Δ sub, hp =>
      GEqProofTree.eqRefl t Γ Δ (sub.toProofTree hp)
  | _, .eqFuncCong f ss ts Γ Δ sub, hp =>
      GEqProofTree.eqFuncCong f ss ts Γ Δ (sub.toProofTree hp)
  | _, .eqPredCong P ss ts Γ Δ sub, hp =>
      GEqProofTree.eqPredCong P ss ts Γ Δ (sub.toProofTree hp)
  | _, .eqGeneral axioms hne haxioms Γ Δ sub, hp =>
      GEqProofTree.eqGeneral axioms hne haxioms Γ Δ (sub.toProofTree hp)

end GEqDeductionTree
end LCS.FirstOrder.Equality
end

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

/-- Example 5.6.1 (companion): Predicate symbols for the equality example
language: a single unary predicate symbol P. -/
@[blueprint "chap5__example_5_6_1"]
inductive ExPredEq1 : Type where
  | P : ExPredEq1

-- ===================================================================
-- Example 5.6.1 (companion type): ExFuncEq1
-- ===================================================================

/-- Example 5.6.1 (companion): Function symbols for the equality example
language: a single unary function symbol f. -/
@[blueprint "chap5__example_5_6_1"]
inductive ExFuncEq1 : Type where
  | f : ExFuncEq1

end LCS.FirstOrder.Equality
end

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
namespace GEqProofTree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.2 (companion): Returns the conclusion sequent
of the G_= proof tree. Since GEqProofTree is indexed by its
conclusion, the conclusion IS the index. This is a shim for
backward compatibility with code that was written against the
unindexed version. -/
def conclusion {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (_ : GEqProofTree hL s) : Sequent L := s

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} (t : GEqProofTree hL s) : t.conclusion = s := rfl

end GEqProofTree
end LCS.FirstOrder.Equality
end

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

/-- Definition 5.6.2 (companion): A sequent is provable in G_= if
there exists a G_= proof tree with that sequent as its conclusion.
Since GEqProofTree is indexed by conclusion, this is simply
`Nonempty (GEqProofTree s)`. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentProvableEq {L : Language} (hL : L.hasEquality = true)
    (s : Sequent L) : Prop :=
  Nonempty (GEqProofTree hL s)

-- ===================================================================
-- Lemma 5.6.1 (companion def): eqCongruence
-- ===================================================================

/-- Lemma 5.6.1 (companion): The congruence relation on terms
defined by the equality symbol in S. Two terms s and t are
congruent (s ~ t) iff T(s doteq t) is in S. Uses SignedFormula. -/
@[blueprint "chap5__lemma_5_6_1"]
def eqCongruence {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (s t : Term L) : Prop :=
  SignedFormula.trueF (FormulaN.eq_ hL s t) ∈ S

-- ===================================================================
-- Lemma 5.6.1 (companion def): quotientHintikkaStructure
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- The structure on the subtype of a generated ambient term algebra H.
Functions and constants are syntactic constructors; predicate interpretations
are membership in S. The carrier consists of terms themselves. -/
noncomputable def quotientHintikkaStructure {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (_hHS : IsHintikkaSetEq L hL H S)
    (hTA : IsGeneratedTermAlgebra L H) : Structure L where
  carrier := { t : Term L // t ∈ H }
  carrierNonempty := by
    obtain ⟨t, ht⟩ := hTA.nonempty
    exact ⟨⟨t, ht⟩⟩
  interpFunc f ts :=
    ⟨Term.func f (fun i => (ts i).val),
     hTA.closedFunc f _ (fun i => (ts i).property)⟩
  interpConst c := ⟨Term.const c, hTA.closedConst c⟩
  interpPred P ts :=
    SignedFormula.trueF (FormulaN.predN P (fun i => (ts i).val)) ∈ S

-- ===================================================================
-- Lemma 5.6.1 (companion def): quotientIdentityAssignment
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): The identity assignment for the
subtype structure on H, mapping each variable x to Term.var x
(as an element of the subtype carrier). For variables not in H,
uses a default element. -/
noncomputable def quotientIdentityAssignment {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S)
    (hTA : IsGeneratedTermAlgebra L H) :
    Assignment (quotientHintikkaStructure hL H S hHS hTA) :=
  open Classical in
  fun x =>
    if h : Term.var x ∈ H then
      ⟨Term.var x, h⟩
    else
      ⟨hTA.nonempty.choose, hTA.nonempty.choose_spec⟩

-- ===================================================================
-- Example 5.6.1 (companion def): exampleLangEqFP
-- ===================================================================

/-- Example 5.6.1: A Language with one unary function
symbol f, no constants, one unary predicate symbol P. -/
@[blueprint "chap5__example_5_6_1"]
def exampleLangEqFP : Language where
  funSymbols := ExFuncEq1
  funArity := fun | .f => 1
  constSymbols := Empty
  predSymbols := ExPredEq1
  predArity := fun | .P => 1

-- ===================================================================
-- Example 5.6.1 (companion def): exEqFormulaRefl
-- ===================================================================

/-- Example 5.6.1: The formula forall x (x doteq f(y) implies P(x)) implies
P(f(y)), where f is a unary function symbol and P is a unary predicate symbol. Variables: x = 0, y = 1. -/
@[blueprint "chap5__example_5_6_1"]
def exEqFormulaRefl : FormulaN exampleLangEqFP :=
  let fy : Term exampleLangEqFP :=
    Term.func ExFuncEq1.f (fun _ => Term.var 1)
  let px : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => Term.var 0)
  let pfy : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => fy)
  let xDoteqFy : FormulaN exampleLangEqFP :=
    FormulaN.eq_ rfl (Term.var 0) fy
  -- forall x (x doteq f(y) implies P(x)) implies P(f(y))
  FormulaN.impl
    (FormulaN.all 0 (FormulaN.impl xDoteqFy px))
    pfy

-- ===================================================================
-- Example 5.6.1: exEqProofTreeRefl
-- ===================================================================

/-- Example 5.6.1: The displayed proof of
→ ∀x (x ≐ f(y) ⊃ P(x)) ⊃ P(f(y)). The root is ⊃:right, followed
by ∀:left instantiated at f(y) and ⊃:left. Its left premise T₁ drops
the final antecedent equation f(y) ≐ f(y) by reflexivity; its right
premise is the axiom P(f(y)), ∀x (x ≐ f(y) ⊃ P(x)) → P(f(y)). -/
@[blueprint "chap5__example_5_6_1" (main := true)]
noncomputable def exEqProofTreeRefl : GEqProofTree (L := exampleLangEqFP) rfl
    (Sequent.mk ([] : List (FormulaN exampleLangEqFP)) [exEqFormulaRefl]) :=
  let fy : Term exampleLangEqFP :=
    Term.func ExFuncEq1.f (fun _ => Term.var 1)
  let px : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => Term.var 0)
  let pfy : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => fy)
  let xDoteqFy : FormulaN exampleLangEqFP :=
    FormulaN.eq_ rfl (Term.var 0) fy
  let fyDoteqFy : FormulaN exampleLangEqFP := FormulaN.eq_ rfl fy fy
  let forallBody : FormulaN exampleLangEqFP :=
    FormulaN.all 0 (FormulaN.impl xDoteqFy px)
  let t1Leaf : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [forallBody, fyDoteqFy] [fyDoteqFy, pfy]) :=
    GEqProofTree.axiom_ _ ⟨fyDoteqFy, by simp, by simp⟩
  let t1 : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [forallBody] [fyDoteqFy, pfy]) :=
    GEqProofTree.eqRefl fy [forallBody] [fyDoteqFy, pfy] t1Leaf
  let rightLeaf : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [pfy, forallBody] [pfy]) :=
    GEqProofTree.axiom_ _ ⟨pfy, by simp, by simp⟩
  let tImplLeft : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [FormulaN.impl fyDoteqFy pfy, forallBody] [pfy]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.implLeft [] [forallBody] [pfy] fyDoteqFy pfy)
      t1 rightLeaf
  have hFree : ∀ t ∈ [fy], isFreeForN t 0 (FormulaN.impl xDoteqFy px) := by
    intro t ht
    simp at ht; subst ht
    exact ⟨trivial, trivial⟩
  let tAllLeft : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [forallBody] [pfy]) :=
    GEqProofTree.onePremise
      (GentzenStep1Ext.allLeft [fy] [] [] [pfy] 0
        (FormulaN.impl xDoteqFy px) (by decide) hFree)
      tImplLeft
  GEqProofTree.onePremise
    (GentzenStep1Ext.implRight [] [] [] forallBody pfy) tAllLeft

-- ===================================================================
-- Example 5.6.2 (companion def): exEqFormulaPredCong
-- ===================================================================

/-- Example 5.6.2: The formula P(f(y)) implies forall x (x doteq f(y)
implies P(x)), where f is a unary function symbol and P is a unary predicate symbol. Variables: x = 0, y = 1. -/
@[blueprint "chap5__example_5_6_2"]
def exEqFormulaPredCong : FormulaN exampleLangEqFP :=
  let fy : Term exampleLangEqFP :=
    Term.func ExFuncEq1.f (fun _ => Term.var 1)
  let px : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => Term.var 0)
  let pfy : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => fy)
  let xDoteqFy : FormulaN exampleLangEqFP :=
    FormulaN.eq_ rfl (Term.var 0) fy
  -- P(f(y)) implies forall x (x doteq f(y) implies P(x))
  FormulaN.impl pfy
    (FormulaN.all 0 (FormulaN.impl xDoteqFy px))

-- ===================================================================
-- Example 5.6.2: exEqProofTreePredCong
-- ===================================================================

/-- Example 5.6.2: The intended displayed proof of
→ P(f(y)) ⊃ ∀x (x ≐ f(y) ⊃ P(x)), with eigenvariable z = var 2.
Above the inner ⊃:right conclusion, the antecedent context is ordered
z ≐ f(y), P(f(y)); principal side formulae precede that context and
equality axioms follow it. T₁ is the conjunction-right tree with T₂
as its left branch; T₂ uses equality-predicate congruence with T₃ as
its left branch; T₃ uses S₁ and reflexivity over two copies of S₂.
The threefold conjunction in T₃ is right-associated. -/
@[blueprint "chap5__example_5_6_2" (main := true)]
def exEqProofTreePredCong : GEqProofTree (L := exampleLangEqFP) rfl
    (Sequent.mk ([] : List (FormulaN exampleLangEqFP))
      [exEqFormulaPredCong]) :=
  let fy : Term exampleLangEqFP :=
    Term.func ExFuncEq1.f (fun _ => Term.var 1)
  let z : Term exampleLangEqFP := Term.var 2
  let pz : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => z)
  let pfy : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => fy)
  let xDoteqFy : FormulaN exampleLangEqFP :=
    FormulaN.eq_ rfl (Term.var 0) fy
  let px : FormulaN exampleLangEqFP :=
    FormulaN.predN ExPredEq1.P (fun _ => Term.var 0)
  let allBody : FormulaN exampleLangEqFP :=
    FormulaN.impl xDoteqFy px
  let forallForm : FormulaN exampleLangEqFP :=
    FormulaN.all 0 allBody
  let zEqFy : FormulaN exampleLangEqFP := FormulaN.eq_ rfl z fy
  let fyEqZ : FormulaN exampleLangEqFP := FormulaN.eq_ rfl fy z
  let zEqZ : FormulaN exampleLangEqFP := FormulaN.eq_ rfl z z
  -- Predicate-congruence axiom for P with ss=[fy], ts=[z]:
  --   ((fy=z) /\ P(fy)) -> P(z)
  let predCongAxiom : FormulaN exampleLangEqFP :=
    eqCongruenceImplPred exampleLangEqFP rfl ExPredEq1.P
      (fun _ => fy) (fun _ => z)
  -- Doteq-as-predicate axiom instance (eqCongruenceImplEq z z fy z):
  --   ((z=fy) /\ (z=z) /\ (z=z)) -> (fy=z)
  let eqEqAxiom : FormulaN exampleLangEqFP :=
    eqCongruenceImplEq rfl z z fy z
  -- Reflexivity uses the final antecedent equation to prove the repeated conjunct.
  let s2 : Sequent exampleLangEqFP :=
    Sequent.mk [zEqFy, pfy, zEqZ] [zEqZ, fyEqZ, pz]
  have hs2 : isAxiom s2 :=
    ⟨zEqZ, by simp [s2], by simp [s2]⟩
  let s2Leaf : GEqProofTree (L := exampleLangEqFP) rfl s2 :=
    GEqProofTree.axiom_ s2 hs2
  let t3Conj : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy, zEqZ]
        [FormulaN.conj zEqZ zEqZ, fyEqZ, pz]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.conjRight [zEqFy, pfy, zEqZ] [] [fyEqZ, pz] zEqZ zEqZ)
      s2Leaf s2Leaf
  let t3Refl : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy] [FormulaN.conj zEqZ zEqZ, fyEqZ, pz]) :=
    GEqProofTree.eqRefl z [zEqFy, pfy]
      [FormulaN.conj zEqZ zEqZ, fyEqZ, pz] t3Conj
  let s1 : Sequent exampleLangEqFP :=
    Sequent.mk [zEqFy, pfy] [zEqFy, fyEqZ, pz]
  have hs1 : isAxiom s1 :=
    ⟨zEqFy, by simp [s1], by simp [s1]⟩
  let s1Leaf : GEqProofTree (L := exampleLangEqFP) rfl s1 :=
    GEqProofTree.axiom_ s1 hs1
  let t3 : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy]
        [FormulaN.conj zEqFy (FormulaN.conj zEqZ zEqZ), fyEqZ, pz]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.conjRight [zEqFy, pfy] [] [fyEqZ, pz]
        zEqFy (FormulaN.conj zEqZ zEqZ))
      s1Leaf t3Refl
  let axSucSeq : Sequent exampleLangEqFP :=
    Sequent.mk [fyEqZ, zEqFy, pfy] [fyEqZ, pz]
  have hAxSuc : isAxiom axSucSeq :=
    ⟨fyEqZ, by simp [axSucSeq], by simp [axSucSeq]⟩
  let tAxSuc : GEqProofTree (L := exampleLangEqFP) rfl axSucSeq :=
    GEqProofTree.axiom_ axSucSeq hAxSuc
  -- Equality congruence yields the leading equation fy=z.
  let tImplLeftEqEq : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy, eqEqAxiom] [fyEqZ, pz]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.implLeft [zEqFy, pfy] [] [fyEqZ, pz]
        (FormulaN.conj zEqFy (FormulaN.conj zEqZ zEqZ)) fyEqZ)
      t3 tAxSuc
  have hAxIsInstance : ∀ A ∈ [eqEqAxiom], isEqAxiomInstance rfl A := by
    intro A hA
    simp at hA
    subst hA
    exact Or.inr (Or.inr (Or.inr ⟨z, z, fy, z, rfl⟩))
  let t2 : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy] [fyEqZ, pz]) :=
    GEqProofTree.eqGeneral [eqEqAxiom] (by simp) hAxIsInstance
      [zEqFy, pfy] [fyEqZ, pz] tImplLeftEqEq
  let axPfySeq : Sequent exampleLangEqFP :=
    Sequent.mk [zEqFy, pfy] [pfy, pz]
  have hAxPfy : isAxiom axPfySeq :=
    ⟨pfy, by simp [axPfySeq], by simp [axPfySeq]⟩
  let tAxPfy : GEqProofTree (L := exampleLangEqFP) rfl axPfySeq :=
    GEqProofTree.axiom_ axPfySeq hAxPfy
  let t1 : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy] [FormulaN.conj fyEqZ pfy, pz]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.conjRight [zEqFy, pfy] [] [pz] fyEqZ pfy)
      t2 tAxPfy
  let axPzSeq : Sequent exampleLangEqFP :=
    Sequent.mk [pz, zEqFy, pfy] [pz]
  have hAxPz : isAxiom axPzSeq :=
    ⟨pz, by simp [axPzSeq], by simp [axPzSeq]⟩
  let tAxPz : GEqProofTree (L := exampleLangEqFP) rfl axPzSeq :=
    GEqProofTree.axiom_ axPzSeq hAxPz
  -- Predicate congruence consumes its leading conjunction premise.
  let tImplLeftPredAx : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk ([zEqFy, pfy] ++ [predCongAxiom]) [pz]) :=
    GEqProofTree.twoPremise
      (GentzenStep2Ext.implLeft [zEqFy, pfy] [] [pz] (FormulaN.conj fyEqZ pfy) pz)
      t1 tAxPz
  -- Predicate congruence drops the final axiom from
  -- [zEqFy, pfy, predCongAxiom] -> [pz].
  let tEqPredCong : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [zEqFy, pfy] [pz]) :=
    GEqProofTree.eqPredCong ExPredEq1.P
      (fun _ => fy) (fun _ => z) [zEqFy, pfy] [pz] tImplLeftPredAx
  -- implRight Γ Δ Λ A B: from [A] ++ Γ -> [B] ++ Δ ++ Λ to Γ -> Δ ++ [impl A B] ++ Λ.
  -- Conclusion: [pfy] -> [impl (z=fy) pz] = premise after allRight subst.
  -- Γ = [pfy], A = z=fy, B = pz, Δ = [], Λ = [].
  -- Premise: [z=fy, pfy] -> [pz]  (tEqPredCong).
  let tImplRight2 : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [pfy] ([] ++ [FormulaN.impl zEqFy pz] ++ [])) :=
    GEqProofTree.onePremise
      (GentzenStep1Ext.implRight [pfy] [] [] zEqFy pz)
      tEqPredCong
  -- allRight with y = 2, x = 0, A = allBody = impl (eq_ (var 0) fy) (predN P (var 0)).
  -- Premise: [pfy] -> [formulaSubstN allBody (var 2) 0] = [pfy] -> [impl (z=fy) pz].
  -- Conclusion: [pfy] -> [forallForm].
  -- Γ = [pfy], Δ = [], Λ = [].
  have hfreeFor : isFreeForN (Term.var 2) 0 allBody := by
    refine ⟨?_, ?_⟩ <;> exact (by trivial : True)
  have hfresh : ∀ F ∈
      (Sequent.mk [pfy] ([] ++ [forallForm] ++ [])).antecedent ++
        (Sequent.mk [pfy] ([] ++ [forallForm] ++ [])).succedent,
      (2 : Nat) ∉ formulaFVN F := by
    -- All formulae in the sequent have FV ⊆ {1}; 2 ≠ 1.
    -- pfy = P(f(var 1)): FV = {1}.
    -- forallForm = all 0 (impl (eq_ (var 0) fy) P(var 0)): FV = ({0,1} ∪ {0}) \ {0} = {1}.
    have h21 : (2 : Nat) ≠ 1 := by decide
    have h20 : (2 : Nat) ≠ 0 := by decide
    intro F hF
    simp at hF
    rcases hF with rfl | rfl
    · -- F = pfy = P(f(var 1))
      -- formulaFVN unfolds to Set.iUnion (fun j : Fin 1 => termFV (ts j))
      -- where ts = fun _ => f(var 1), termFV (f(var 1)) = Set.iUnion (fun _ => {1}).
      intro hMem
      -- Set.iUnion f x = ∃ i, f i x
      obtain ⟨_, h⟩ := hMem
      obtain ⟨_, h⟩ := h
      -- h : termFV (Term.var 1) 2, i.e., Set.singleton 1 2, i.e., 2 = 1.
      exact h21 h
    · -- F = forallForm = all 0 (impl (eq_ (var 0) fy) P(var 0))
      -- formulaFVN = formulaFVN (impl ...) \ Set.singleton 0
      intro hMem
      obtain ⟨hLeft, _hNE0⟩ := hMem
      rcases hLeft with h1 | h2
      · -- h1 : formulaFVN (eq_ (var 0) fy) 2 = (termFV (var 0) ∪ termFV fy) 2
        rcases h1 with h1a | h1b
        · exact h20 h1a
        · -- h1b : termFV fy 2 = Set.iUnion (fun _ => termFV (var 1)) 2
          obtain ⟨_, hh⟩ := h1b
          exact h21 hh
      · -- h2 : formulaFVN (predN P (var 0)) 2 = Set.iUnion (fun _ => termFV (var 0)) 2
        obtain ⟨_, hh⟩ := h2
        exact h20 hh
  let tAllRight : GEqProofTree (L := exampleLangEqFP) rfl
      (Sequent.mk [pfy] ([] ++ [forallForm] ++ [])) :=
    GEqProofTree.onePremise
      (GentzenStep1Ext.allRight 2 [pfy] [] [] 0 allBody hfresh hfreeFor)
      tImplRight2
  -- implRight at top: from [pfy] -> [forallForm] to [] -> [impl pfy forallForm].
  -- Γ = [], A = pfy, B = forallForm, Δ = [], Λ = [].
  GEqProofTree.onePremise
    (GentzenStep1Ext.implRight [] [] [] pfy forallForm)
    tAllRight

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_symm
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): Symmetry of the congruence relation:
if T(s doteq t) in S then T(t doteq s) in S, using H6(iii)
with doteq as predicate and H2. -/
theorem eqCongruence_symm {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (s t : Term L) (hs : s ∈ H) (ht : t ∈ H)
    (h : eqCongruence hL S s t) : eqCongruence hL S t s :=
-- BEGIN PROOF
by
  -- Following the textbook proof of Lemma 5.6.1, step (2):
  -- From T(s = t) in S, use H6(iii-eq) with s1=s, s2=s, t1=t, t2=s
  -- to get T(((s = t) /\ (s = s) /\ (s = s)) -> (t = s)) in S.
  unfold eqCongruence
  have h6eq := hHS.h6iii_eq s s t s hs hs ht hs
  -- h6eq : T(((s = t) /\ (s = s) /\ (s = s)) -> (t = s)) ∈ S
  -- By H2 (type-b for implication): F(antecedent) ∈ S ∨ T(t = s) ∈ S
  have hb := hHS.base.h2 (TypeB.tImpl
    (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.conj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s)))
    (FormulaN.eq_ hL t s))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  cases hb h6eq with
  | inr hgoal => exact hgoal
  | inl hF =>
    -- F(antecedent) ∈ S, i.e., F((s = t) /\ ((s = s) /\ (s = s))) ∈ S
    -- By H2 (type-b for conjunction): F(s = t) ∈ S ∨ F((s = s) /\ (s = s)) ∈ S
    have hb2 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s t) (FormulaN.conj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s)))
    simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
    cases hb2 hF with
    | inl hFst =>
      -- F(s = t) ∈ S contradicts H0 + T(s = t) ∈ S (which is h)
      exfalso
      exact hHS.base.h0 (FormulaN.eq_ hL s t) rfl ⟨h, hFst⟩
    | inr hFss =>
      -- F((s = s) /\ (s = s)) ∈ S
      -- By H2: F(s = s) ∈ S ∨ F(s = s) ∈ S
      have hb3 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb3
      cases hb3 hFss with
      | inl hFss' =>
        -- F(s = s) contradicts H0 + H6(i) (T(s = s) ∈ S)
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss'⟩
      | inr hFss' =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss'⟩

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_trans
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): Transitivity of the congruence relation:
if T(r doteq s) and T(s doteq t) in S then T(r doteq t) in S,
using symmetry, H6(iii), and H2. -/
theorem eqCongruence_trans {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (r s t : Term L) (hr : r ∈ H) (hs : s ∈ H) (ht : t ∈ H)
    (hrs : eqCongruence hL S r s) (hst : eqCongruence hL S s t) :
    eqCongruence hL S r t :=
-- BEGIN PROOF
by
  unfold eqCongruence
  have hsr : eqCongruence hL S s r := eqCongruence_symm hHS r s hr hs hrs
  have h6eq := hHS.h6iii_eq s s r t hs hs hr ht
  have hb := hHS.base.h2 (TypeB.tImpl
    (FormulaN.conj (FormulaN.eq_ hL s r) (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s)))
    (FormulaN.eq_ hL r t))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  cases hb h6eq with
  | inr hgoal => exact hgoal
  | inl hF =>
    have hb2 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s r) (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s)))
    simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
    cases hb2 hF with
    | inl hFsr =>
      exfalso
      exact hHS.base.h0 (FormulaN.eq_ hL s r) rfl ⟨hsr, hFsr⟩
    | inr hFst_ss =>
      have hb3 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb3
      cases hb3 hFst_ss with
      | inl hFst' =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s t) rfl ⟨hst, hFst'⟩
      | inr hFss =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss⟩

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_equiv
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): The congruence relation restricted to H
is an equivalence relation: reflexivity from H6(i), symmetry from
H6(iii-eq)+H2, transitivity from symmetry+H6(iii-eq)+H2. The relation
is stated on the subtype { t : Term L // t ∈ H } so that reflexivity
is well-typed (every element of the subtype is in H by definition). -/
theorem eqCongruence_equiv {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S) :
    Equivalence (fun (s t : { t : Term L // t ∈ H }) =>
      eqCongruence hL S s.val t.val) :=
-- BEGIN PROOF
by
  constructor
  · -- Reflexivity: by H6(i), T(t = t) ∈ S for every t ∈ H
    intro ⟨x, hx⟩
    exact hHS.h6i x hx
  · -- Symmetry: by eqCongruence_symm
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact eqCongruence_symm hHS x y hx hy hxy
  · -- Transitivity: by eqCongruence_trans
    intro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hxy hyz
    exact eqCongruence_trans hHS x y z hx hy hz hxy hyz

-- ===================================================================
-- Helper: false conjunction of nonempty list with all true atomic
-- components is absurd in a Hintikka set.
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Helper: If F(conjoinFormulae default fs) ∈ S where fs is nonempty,
T(fi) ∈ S for every fi in fs, and all fi are atomic, then False.
Uses H0 and H2 (TypeB.fConj). -/
theorem falseConjoinContra {L : Language}
    {S : Set (SignedFormula L)}
    (h0 : ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S))
    (h2 : ∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S)
    (default : FormulaN L) (fs : List (FormulaN L))
    (hne : fs ≠ [])
    (hF : SignedFormula.falseF (conjoinFormulae default fs) ∈ S)
    (hTs : ∀ F, F ∈ fs → SignedFormula.trueF F ∈ S)
    (hAt : ∀ F, F ∈ fs → F.isAtomic = true) :
    False := by
-- BEGIN PROOF
  induction fs with
  | nil => exact absurd rfl hne
  | cons A rest ih =>
    have hmem_head : A ∈ A :: rest := List.Mem.head _
    match rest with
    | [] =>
      simp only [conjoinFormulae] at hF
      exact h0 A (hAt A hmem_head) ⟨hTs A hmem_head, hF⟩
    | B :: tail =>
      simp only [conjoinFormulae] at hF
      have hb2 := h2 (TypeB.fConj A (conjoinFormulae default (B :: tail)))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
      cases hb2 hF with
      | inl hFA =>
        exact h0 A (hAt A hmem_head) ⟨hTs A hmem_head, hFA⟩
      | inr hFrest =>
        exact ih (List.cons_ne_nil B tail) hFrest
          (fun F hF' => hTs F (List.Mem.tail _ hF'))
          (fun F hF' => hAt F (List.Mem.tail _ hF'))

end LCS.FirstOrder.Equality
end

