import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality.HintikkaSets
import Attach
import LCS.FirstOrder.Equality.SystemGEq.ProofsStamp

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

namespace GEqDeductionTree

/-- Definition 5.6.2 (companion): The conclusion of an indexed G_=
    deduction tree is its type index (same as for `GEqProofTree`). -/
@[blueprint "chap5__definition_5_6_2"]
def conclusion {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (_ : GEqDeductionTree hL s) : Sequent L := s

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

namespace GEqProofTree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.2 (companion): Returns the conclusion sequent
of the G_= proof tree. Since GEqProofTree is indexed by its
conclusion, the conclusion IS the index. This is a shim for
backward compatibility with code that was written against the
unindexed version. -/
def conclusion {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (_ : GEqProofTree hL s) : Sequent L := s

end GEqProofTree

/-- Definition 5.6.2 (companion): A sequent is provable in G_= if
there exists a G_= proof tree with that sequent as its conclusion.
Since GEqProofTree is indexed by conclusion, this is simply
`Nonempty (GEqProofTree s)`. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentProvableEq {L : Language} (hL : L.hasEquality = true)
    (s : Sequent L) : Prop :=
  Nonempty (GEqProofTree hL s)

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

end LCS.FirstOrder.Equality
end
