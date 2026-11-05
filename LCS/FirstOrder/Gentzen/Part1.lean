import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.FirstOrder.Gentzen.Part1.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution





/-- Definition 5.4.1 (connective convention): An available predicate symbol
supplies a target formula, so every formula over a language without equality
has a semantically equivalent formula using the six connectives. -/
@[blueprint "chap5__definition_5_4_1"]
theorem exists_equiv_formulaN {L : Language} (hL : L.withoutEquality)
    (P : L.predSymbols) (A : Syntax.Formula L) :
    ∃ B : FormulaN L, ∀ (M : Structure L) (s : Assignment M),
      Semantics.formulaEval M A s ↔ formulaEvalN M B s 

-- ===================================================================
-- Definition 5.4.1: First-order sequent (normalized, FormulaN-based)
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is a pair of finite sequences of
formulae. This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
structure Sequent (L : Language) where
  antecedent : List (FormulaN L)
  succedent : List (FormulaN L)

/-- Definition 5.4.1: A first-order sequent over a language without equality
is a pair of finite sequences of formulae. -/
@[blueprint "chap5__definition_5_4_1"]
abbrev SequentNoEq (L : Language) (hL : L.withoutEquality) : Type := Sequent L

-- ===================================================================
-- Definition 5.4.1 (companion): Axiom predicate for first-order G
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is an axiom if its antecedent and
succedent contain a common formula. This general form allows any equality flag;
G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def isAxiom {L : Language} (s : Sequent L) : Prop :=
  ∃ A : FormulaN L, A ∈ s.antecedent ∧ A ∈ s.succedent

/-- Definition 5.4.1: A sequent over a language without equality is an axiom
of G if its antecedent and succedent contain a common formula. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
def isAxiomNoEq {L : Language} (hL : L.withoutEquality)
    (s : SequentNoEq L hL) : Prop :=
  isAxiom s

-- ===================================================================
-- Definition 5.4.2 (indexed types): Constrained Gentzen Steps for G
-- ===================================================================

/-- Definition 5.4.1: One-premise inference rules of G over a language without
equality, indexed by premise and conclusion sequents so that each constructor enforces the structural relationship mandated by the rule. For quantifier rules, side conditions (free-for, fresh variable) are fields of the constructor. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
inductive GentzenStep1 {L : Language} (hL : L.withoutEquality) : Sequent L → Sequent L → Type where
  | conjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.conj A B] ++ Δ) Λ)
  | disjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.disj A B] ++ Λ))
  | implRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk ([A] ++ Γ) ([B] ++ Δ ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.impl A B] ++ Λ))
  | negLeft (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1 hL (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk (Γ ++ [FormulaN.neg A] ++ Δ) Λ)
  | negRight (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1 hL (Sequent.mk ([A] ++ Γ) (Δ ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.neg A] ++ Λ))
  | allLeft (t : Term L) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hfree : isFreeForN t x A) :
      GentzenStep1 hL
        (Sequent.mk
          (Γ ++ [formulaSubstN A t x, FormulaN.all x A] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ)
  | allRight (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).antecedent ++
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1 hL
        (Sequent.mk Γ
          (Δ ++ [formulaSubstN A (Term.var y) x] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ))
  | exLeft (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).antecedent ++
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1 hL
        (Sequent.mk
          (Γ ++ [formulaSubstN A (Term.var y) x] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ)
  | exRight (t : Term L) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hfree : isFreeForN t x A) :
      GentzenStep1 hL
        (Sequent.mk Γ
          (Δ ++ [formulaSubstN A t x, FormulaN.ex x A] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ))

/-- Definition 5.4.1: Two-premise inference rules of G over a language without
equality, indexed by premise and conclusion sequents. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
inductive GentzenStep2 {L : Language} (hL : L.withoutEquality) :
    Sequent L → Sequent L → Sequent L → Type where
  | conjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk Γ (Δ ++ [A] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ))
  | disjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk (Γ ++ [A] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.disj A B] ++ Δ) Λ)
  | implLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk ([B] ++ Γ ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ)

-- ===================================================================
-- Definition 5.4.2 (companion type): GProofTree (indexed)
-- ===================================================================

/-- Definition 5.4.2: Proof trees for the Gentzen system G over a language
without equality, indexed by their conclusion sequent. Textbook: "Deduction trees and proof trees
for the system G are defined as in definition 3.4.5, but for formulae
and with the rules given in definition 5.4.1." Structural validity is
built into the type: leaves must be axiom sequents, and each rule
application constrains its premise(s) to have the form mandated by the
rule (including side conditions for quantifier rules). No separate
WellFormed predicate is needed. -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
inductive GProofTree {L : Language} (hL : L.withoutEquality) : Sequent L → Type where
  | axiom_ (s : Sequent L) (h : isAxiom s) : GProofTree hL s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1 hL prem conc)
      (t : GProofTree hL prem) : GProofTree hL conc
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2 hL prem1 prem2 conc)
      (t1 : GProofTree hL prem1) (t2 : GProofTree hL prem2) :
      GProofTree hL conc

-- ===================================================================
-- Definition 5.4.2 (companion type): GDeductionTree (indexed)
-- ===================================================================

/-- Definition 5.4.2 (companion): Deduction trees for the Gentzen system G
    over a language without equality, indexed by their conclusion sequent. Textbook: "Deduction trees and proof
    trees for the system G are defined as in Definition 3.4.5, but for
    formulae and with the rules given in Definition 5.4.1." Parallel of
    `GProofTree` with FREE-FORM leaves (i.e. leaves are not forced to be
    axioms). Proof trees are precisely the deduction trees whose leaves are
    all axioms (see `GDeductionTree.isProof` / `GDeductionTree.toProofTree`
    for the bridge). -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
inductive GDeductionTree {L : Language} (hL : L.withoutEquality) : Sequent L → Type where
  | leaf (s : Sequent L) : GDeductionTree hL s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1 hL prem conc)
      (t : GDeductionTree hL prem) : GDeductionTree hL conc
  | twoPremise {p1 p2 conc : Sequent L}
      (rule : GentzenStep2 hL p1 p2 conc)
      (t1 : GDeductionTree hL p1) (t2 : GDeductionTree hL p2) :
      GDeductionTree hL conc

-- ===================================================================
-- Example 5.4.1 (companion type): ExPredPQ
-- ===================================================================

/-- Example 5.4.1 (companion type): Predicate symbols for the example language
with a propositional symbol P (zero-arity) and a unary predicate Q. -/
@[blueprint "chap5__example_5_4_1"]
inductive ExPredPQ : Type where
  | P : ExPredPQ
  | Q : ExPredPQ

-- ===================================================================
-- Example 5.4.1 (companion def): exampleLangPQ
-- ===================================================================

/-- Example 5.4.1 (companion def): A Language with no function symbols,
no constants, predicate symbols P and Q, where P has arity 0 and Q has
arity 1. Equality-free. -/
@[blueprint "chap5__example_5_4_1"]
def exampleLangPQ : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPredPQ
  predArity := fun
    | .P => 0
    | .Q => 1
  hasEquality := false

-- ===================================================================
-- Example 5.4.1 (companion def): exFormulaExistentialImpl
-- ===================================================================

/-- Example 5.4.1 (companion def): The formula
A = ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z)),
where P is a propositional symbol (zero-arity predicate) and Q is a
unary predicate. Variables: x = 0, z = 2. -/
@[blueprint "chap5__example_5_4_1"]
def exFormulaExistentialImpl : FormulaN exampleLangPQ :=
  let pF : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i)
  let qVar (n : Nat) : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.Q (fun _ => Term.var n)
  FormulaN.impl
    (FormulaN.ex 0 (FormulaN.impl pF (qVar 0)))
    (FormulaN.impl pF (FormulaN.ex 2 (qVar 2)))

-- ===================================================================
-- Example 5.4.1: exProofTreeExistentialImpl
-- ===================================================================

/-- Example 5.4.1: A concrete proof tree for the sequent
→ ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z)).

The textbook tree (bottom-up, conclusions first):
  -- root: → A
  ⊃:right gives ∃x(P ⊃ Q(x)) → P ⊃ ∃z Q(z)
  ∃:left (y=y_1) gives P ⊃ Q(y_1) → P ⊃ ∃z Q(z)
  ⊃:right gives P, P ⊃ Q(y_1) → ∃z Q(z)
  ⊃:left splits into two branches:
    left: P → P, ∃z Q(z)  (axiom; the side formula P is first)
    right: Q(y_1), P → ∃z Q(z)
      ∃:right (t=var 1) gives Q(y_1), P → Q(y_1), ∃z Q(z) (axiom).

Note: because P has arity 0, P[y_1/x] is not definitionally equal to P
under Lean's `formulaSubstN`; the proof-tree index uses the substituted
form, which is provably equal to P via `funext` (cf. `pF_eq_Aimpl`
lemma hidden in the construction). -/
@[blueprint "chap5__example_5_4_1" (main := true)]
def exProofTreeExistentialImpl :
    GProofTree (L := exampleLangPQ) rfl (Sequent.mk ([] : List (FormulaN exampleLangPQ))
                           [exFormulaExistentialImpl]) :=
  let pF : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i)
  let qVar (n : Nat) : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.Q (fun _ => Term.var n)
  let exZQz : FormulaN exampleLangPQ := FormulaN.ex 2 (qVar 2)
  let exXPimplQx : FormulaN exampleLangPQ :=
    FormulaN.ex 0 (FormulaN.impl pF (qVar 0))
  let Aimpl : FormulaN exampleLangPQ := formulaSubstN pF (Term.var 1) 0
  let pImplQy1 : FormulaN exampleLangPQ := FormulaN.impl Aimpl (qVar 1)
  -- pF = Aimpl up to funext on the vacuous Fin 0 argument
  have pF_eq_Aimpl : pF = Aimpl := by
    simp [Aimpl, pF, formulaSubstN]
    apply congrArg (FormulaN.predN (L := exampleLangPQ) ExPredPQ.P)
    funext i; exact Fin.elim0 i
  -- Leaf 1: P → P[y_1/x], ∃z Q(z)   (axiom, witnessed by Aimpl = pF via funext)
  let leaf1Seq : Sequent exampleLangPQ :=
    Sequent.mk ([pF] ++ []) ([Aimpl] ++ [exZQz])
  let tLeaf1 : GProofTree (L := exampleLangPQ) rfl leaf1Seq :=
    GProofTree.axiom_ leaf1Seq
      ⟨Aimpl,
       by
         show Aimpl ∈ [pF] ++ ([] : List (FormulaN exampleLangPQ))
         rw [← pF_eq_Aimpl]; exact List.Mem.head _,
       by
         show Aimpl ∈ [Aimpl] ++ [exZQz]
         exact List.Mem.head _⟩
  -- Leaf 2: Q(y_1), P → Q(y_1), ∃z Q(z)   (axiom on Q(y_1))
  let leaf2Seq : Sequent exampleLangPQ :=
    Sequent.mk [qVar 1, pF] ([] ++ [qVar 1, exZQz] ++ [])
  let tLeaf2 : GProofTree (L := exampleLangPQ) rfl leaf2Seq :=
    GProofTree.axiom_ leaf2Seq ⟨qVar 1, List.Mem.head _, List.Mem.head _⟩
  -- ∃:right (t = Term.var 1): Q(y_1), P → ∃z Q(z)
  let exRightConc : Sequent exampleLangPQ :=
    Sequent.mk [qVar 1, pF] ([] ++ [exZQz] ++ [])
  let tExRight : GProofTree (L := exampleLangPQ) rfl exRightConc :=
    GProofTree.onePremise
      (GentzenStep1.exRight (Term.var 1) [qVar 1, pF] [] [] 2 (qVar 2)
        (by simp [isFreeForN, qVar]))
      tLeaf2
  -- ⊃:left: P, P ⊃ Q(y_1) → ∃z Q(z)
  let implLeftConc : Sequent exampleLangPQ :=
    Sequent.mk ([pF] ++ [pImplQy1] ++ []) [exZQz]
  let tImplLeft : GProofTree (L := exampleLangPQ) rfl implLeftConc :=
    GProofTree.twoPremise
      (GentzenStep2.implLeft [pF] [] [exZQz] Aimpl (qVar 1))
      tLeaf1
      tExRight
  -- ⊃:right (inner): P ⊃ Q(y_1) → P ⊃ ∃z Q(z)
  let implRightInnerConc : Sequent exampleLangPQ :=
    Sequent.mk [pImplQy1] ([] ++ [FormulaN.impl pF exZQz] ++ [])
  let tImplRightInner : GProofTree (L := exampleLangPQ) rfl implRightInnerConc :=
    GProofTree.onePremise
      (GentzenStep1.implRight [pImplQy1] [] [] pF exZQz)
      tImplLeft
  -- ∃:left (y = 1): ∃x(P ⊃ Q(x)) → P ⊃ ∃z Q(z)
  let exLeftConc : Sequent exampleLangPQ :=
    Sequent.mk ([] ++ [exXPimplQx] ++ []) [FormulaN.impl pF exZQz]
  let tExLeft : GProofTree (L := exampleLangPQ) rfl exLeftConc :=
    GProofTree.onePremise
      (GentzenStep1.exLeft 1 [] [] [FormulaN.impl pF exZQz] 0
        (FormulaN.impl pF (qVar 0))
        (by
          intro F hF
          simp at hF
          rcases hF with rfl | rfl
          · -- F = exXPimplQx = ex 0 (impl pF (qVar 0))
            intro h
            simp [formulaFVN, pF, qVar, termFV] at h
            obtain ⟨h1, h2⟩ := h
            rcases h1 with ⟨i, _⟩ | ⟨_j, hj⟩
            · exact Fin.elim0 i
            · exact (by decide : (1 : Nat) ≠ 0) hj
          · -- F = impl pF exZQz
            intro h
            simp [formulaFVN, pF, exZQz, qVar, termFV] at h
            rcases h with ⟨i, _⟩ | ⟨hSet, _h2⟩
            · exact Fin.elim0 i
            · rcases hSet with ⟨_j, hj⟩
              exact (by decide : (1 : Nat) ≠ 2) hj)
        (by simp [isFreeForN, pF, qVar]))
      tImplRightInner
  -- ⊃:right (outer): → ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z))
  GProofTree.onePremise
    (GentzenStep1.implRight [] [] [] exXPimplQx (FormulaN.impl pF exZQz))
    tExLeft

-- ===================================================================
-- Example 5.4.2 (companion types): ExPredPQ2 and ExFunc
-- ===================================================================

/-- Example 5.4.2: Predicate symbols for the example language with
unary predicates P and Q. -/
@[blueprint "chap5__example_5_4_2"]
inductive ExPredPQ2 : Type where
  | P : ExPredPQ2
  | Q : ExPredPQ2

/-- Example 5.4.2: Function symbols for the example language with
a unary function symbol f. -/
@[blueprint "chap5__example_5_4_2"]
inductive ExFunc : Type where
  | f : ExFunc

/-- Example 5.4.2: The equality-free language with unary predicates P and Q,
unary function f, and no constants. -/
@[blueprint "chap5__example_5_4_2"]
def exampleLangPQf : Language where
  funSymbols := ExFunc
  funArity := fun _ => 1
  constSymbols := Empty
  predSymbols := ExPredPQ2
  predArity := fun _ => 1
  hasEquality := false

/-- Example 5.4.2: A = (∀x P(x) ∧ ∃y Q(y)) ⊃ (P(f(v)) ∧ ∃z Q(z)),
with x = 0, y = 1, z = 2, and v = 3. -/
@[blueprint "chap5__example_5_4_2"]
def exFormulaQuantifiedConj : FormulaN exampleLangPQf :=
  let p (t : Term exampleLangPQf) := FormulaN.predN ExPredPQ2.P (fun _ => t)
  let q (t : Term exampleLangPQf) := FormulaN.predN ExPredPQ2.Q (fun _ => t)
  FormulaN.impl
    (.conj (.all 0 (p (.var 0))) (.ex 1 (q (.var 1))))
    (.conj (p (.func ExFunc.f (fun _ => .var 3))) (.ex 2 (q (.var 2))))

/-- Example 5.4.2: The displayed G-proof of → A, with Π as the left
premise of ∧:right, ∀:left instantiated by f(v), and ∃:left followed upward
by ∃:right using u = 4, distinct from v = 3. -/
@[blueprint "chap5__example_5_4_2" (main := true)]
def exProofTreeQuantifiedConj :
    GProofTree (L := exampleLangPQf) rfl (Sequent.mk [] [exFormulaQuantifiedConj]) := by
  let p (t : Term exampleLangPQf) := FormulaN.predN ExPredPQ2.P (fun _ => t)
  let q (t : Term exampleLangPQf) := FormulaN.predN ExPredPQ2.Q (fun _ => t)
  let fv : Term exampleLangPQf := .func ExFunc.f (fun _ => .var 3)
  let pfv := p fv
  let allPx := FormulaN.all 0 (p (.var 0))
  let exQy := FormulaN.ex 1 (q (.var 1))
  let exQz := FormulaN.ex 2 (q (.var 2))
  let qu := q (.var 4)
  -- Π: P(f(v)), ∀x P(x), ∃y Q(y) → P(f(v)).
  let piTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [pfv, allPx, exQy] [pfv]) :=
    .axiom_ _ ⟨pfv, by simp, by simp⟩
  -- Right axiom: P(f(v)), ∀x P(x), Q(u) → Q(u), ∃z Q(z).
  let qLeaf : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [pfv, allPx, qu] [qu, exQz]) :=
    .axiom_ _ ⟨qu, by simp, by simp⟩
  let exRightTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [pfv, allPx, qu] [exQz]) :=
    .onePremise
      (.exRight (.var 4) [pfv, allPx, qu] [] [] 2 (q (.var 2))
        (by trivial)) qLeaf
  let exLeftTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [pfv, allPx, exQy] [exQz]) :=
    .onePremise
      (.exLeft 4 [pfv, allPx] [] [exQz] 1 (q (.var 1))
        (by
          intro F hF
          simp at hF
          rcases hF with rfl | rfl | rfl | rfl
          · rintro ⟨_, _, h⟩
            exact (by decide : (4 : Nat) ≠ 3) h
          · rintro ⟨⟨_, h⟩, _⟩
            exact (by decide : (4 : Nat) ≠ 0) h
          · rintro ⟨⟨_, h⟩, _⟩
            exact (by decide : (4 : Nat) ≠ 1) h
          · rintro ⟨⟨_, h⟩, _⟩
            exact (by decide : (4 : Nat) ≠ 2) h)
        (by trivial)) exRightTree
  let conjRightTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [pfv, allPx, exQy] [.conj pfv exQz]) :=
    .twoPremise (.conjRight [pfv, allPx, exQy] [] [] pfv exQz) piTree exLeftTree
  let allLeftTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [allPx, exQy] [.conj pfv exQz]) :=
    .onePremise (.allLeft fv [] [exQy] [.conj pfv exQz] 0 (p (.var 0))
      (by trivial)) conjRightTree
  let conjLeftTree : GProofTree (L := exampleLangPQf) rfl
      (Sequent.mk [.conj allPx exQy] [.conj pfv exQz]) :=
    .onePremise (.conjLeft [] [] [.conj pfv exQz] allPx exQy) allLeftTree
  exact .onePremise (.implRight [] [] [] (.conj allPx exQy) (.conj pfv exQz))
    conjLeftTree

end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
namespace GProofTree

/-- Definition 5.4.2 (companion): The conclusion of an indexed proof
tree is its type index. Textbook Def 3.4.5 / Def 5.4.2: "The sequent
labeling the root of a proof tree is called the conclusion of the
proof tree." This lemma witnesses that fact definitionally. -/
@[blueprint "chap5__definition_5_4_2"]
def conclusion {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (_ : GProofTree hL s) : Sequent L := s

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (t : GProofTree hL s) : t.conclusion hL = s := rfl

end GProofTree
end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
namespace GDeductionTree

/-- Definition 5.4.2 (companion): The conclusion of an indexed deduction
    tree is its type index (same as for `GProofTree`). -/
@[blueprint "chap5__definition_5_4_2"]
def conclusion {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (_ : GDeductionTree hL s) : Sequent L := s

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (t : GDeductionTree hL s) : t.conclusion hL = s := rfl

/-- Definition 5.4.2 (companion): A deduction tree is a proof tree iff all
    its leaves are axiom sequents. This is the bridge between the two Def
    5.4.2 notions. -/
@[blueprint "chap5__definition_5_4_2"]
def isProof {L : Language} (hL : L.withoutEquality) : {s : Sequent L} → GDeductionTree hL s → Prop
  | _, .leaf s => isAxiom s
  | _, .onePremise _ t => t.isProof hL
  | _, .twoPremise _ t1 t2 => t1.isProof hL ∧ t2.isProof hL

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.2 (companion): Converts a deduction tree whose leaves
    are all axioms into a proof tree of the same conclusion. -/
def toProofTree {L : Language} (hL : L.withoutEquality) :
    {s : Sequent L} → (t : GDeductionTree hL s) → t.isProof hL → GProofTree hL s
  | _, .leaf s, hax => GProofTree.axiom_ s hax
  | _, .onePremise rule t, hp => GProofTree.onePremise rule (t.toProofTree hL hp)
  | _, .twoPremise rule t1 t2, hp =>
      GProofTree.twoPremise rule
        (t1.toProofTree hL hp.1) (t2.toProofTree hL hp.2)

end GDeductionTree
end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

/-- Definition 5.4.2 (companion): Over a language without equality, a sequent is
G-provable iff there exists a GProofTree with that sequent as conclusion. Textbook Def 3.4.5 /
Def 5.4.2: "A sequent is provable iff there exists a proof tree of
which it is the conclusion." -/
@[blueprint "chap5__definition_5_4_2"]
def sequentProvable {L : Language} (hL : L.withoutEquality) (s : Sequent L) : Prop :=
  Nonempty (GProofTree hL s)

-- ===================================================================
-- Definition 5.4.2: sequentValid (normalized, FormulaN-based)
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is valid iff for every structure
and assignment, truth of all antecedent formulae implies truth of some succedent
formula. This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentValid {L : Language} (seq : Sequent L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A ∈ seq.antecedent, formulaEvalN M A s) →
    (∃ B, B ∈ seq.succedent ∧ formulaEvalN M B s)

/-- Definition 5.4.2: A sequent over a language without equality is valid iff
for every structure and assignment, truth of all antecedent formulae implies
truth of some succedent formula. -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
def sequentValidNoEq {L : Language} (hL : L.withoutEquality)
    (seq : SequentNoEq L hL) : Prop :=
  sequentValid seq

-- ===================================================================
-- termCoincidence imported from SemanticsN

-- ===================================================================
-- Lemma 5.4.1 (Part i): Term substitution-evaluation equivalence
-- ===================================================================

/-- Lemma 5.4.1 (companion, Part i): For any terms t and r, structure
M, and assignment s, the evaluation of r[t/x] under s equals the
evaluation of r[a/x] under s, where a is the naming constant for
t_M[s]. Proved by structural induction on term r. -/
@[blueprint "chap5__lemma_5_4_1" (main := true)]
theorem termSubstNamingConst {L : Language}
    (M : Structure L) (s : Assignment (extendedInterp M))
    (t r : Term (extendedLanguage L M.carrier)) (x : Nat) :
    termEval (extendedInterp M) s (termSubst r t x) =
    termEval (extendedInterp M) s
      (termSubst r (namingConst (termEval (extendedInterp M) s t)) x) 

-- ===================================================================
-- Lemma 5.4.1 (Part ii): FormulaN substitution-evaluation equivalence
-- on the extended language
-- ===================================================================



/-- Proof of Lemma 5.4.1 (ii): Over a language without equality, replacing
    a free-for term by its naming constant preserves formula satisfaction. -/
@[blueprint "chap5__lemma_5_4_1" (main := true)]
theorem formulaSubstNamingConstNoEq {L : Language} (hL : L.withoutEquality)
    (M : Structure L) (s : Assignment (extendedInterp M))
    (A : FormulaN (extendedLanguage L M.carrier))
    (t : Term (extendedLanguage L M.carrier)) (x : Nat)
    (hfree : isFreeForN t x A) :
    formulaEvalN (extendedInterp M) (formulaSubstN A t x) s ↔
    formulaEvalN (extendedInterp M)
      (formulaSubstN A (namingConst (termEval (extendedInterp M) s t)) x) s 

-- ===================================================================
-- Helpers for list membership reasoning
-- ===================================================================

-- Decompose membership in Γ ++ [X] ++ Δ
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_cases {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ ++ [X] ++ Δ) : a ∈ Γ ∨ a = X ∨ a ∈ Δ := by
-- BEGIN PROOF
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

-- Construct membership in Γ ++ [X] ++ Δ
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_left {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_left _ h)
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem1_center {α : Type} {Γ Δ : List α} {X : α} :
    X ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_right {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_right _ h

-- Decompose membership in Γ ++ [X, Y] ++ Δ
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_cases {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ ++ [X, Y] ++ Δ) : a ∈ Γ ∨ a = X ∨ a = Y ∨ a ∈ Δ := by
-- BEGIN PROOF
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2 | h3) | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

-- Construct membership in Γ ++ [X, Y] ++ Δ
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_left {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_left _ h)
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_first {α : Type} {Γ Δ : List α} {X Y : α} :
    X ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_second {α : Type} {Γ Δ : List α} {X Y : α} :
    Y ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_right {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_right _ h

-- Decompose/construct membership in Γ ++ Δ (no middle)
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_cases {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ ++ Δ) : a ∈ Γ ∨ a ∈ Δ := List.mem_append.mp h
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_left {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ) : a ∈ Γ ++ Δ := List.mem_append_left _ h
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_right {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Δ) : a ∈ Γ ++ Δ := List.mem_append_right _ h

-- Decompose/construct membership in [X] ++ Γ (cons)
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_cases {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ [X] ++ Γ) : a = X ∨ a ∈ Γ := by
-- BEGIN PROOF
  simp only [List.singleton_append, List.mem_cons] at h; exact h
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_head {α : Type} {Γ : List α} {X : α} :
    X ∈ [X] ++ Γ := List.mem_cons_self
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_tail {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ [X] ++ Γ := List.mem_cons.mpr (Or.inr h)

-- Construct membership in Γ ++ [X] (snoc)



-- ===================================================================
-- coincidenceLemmaN imported from SemanticsN

-- ===================================================================
-- Definition 5.4.2 (companion): sequentFalsifiableIn
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is falsifiable in a
given structure M iff there exists an assignment s such that all
antecedent formulae are true and all succedent formulae are false
under (M, s). This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentFalsifiableIn {L : Language} (M : Structure L)
    (seq : Sequent L) : Prop :=
  ∃ (s : Assignment M),
    (∀ A ∈ seq.antecedent, formulaEvalN M A s) ∧
    (∀ B ∈ seq.succedent, ¬ formulaEvalN M B s)

/-- Definition 5.4.2 (companion): A sequent over a language without equality
is falsifiable in M iff some assignment makes all antecedent formulae true
and all succedent formulae false. -/
@[blueprint "chap5__definition_5_4_2"]
def sequentFalsifiableInNoEq {L : Language} (hL : L.withoutEquality)
    (M : Structure L) (seq : SequentNoEq L hL) : Prop :=
  sequentFalsifiableIn M seq

-- ===================================================================
-- Lemma 5.4.2: Rule falsification preservation
-- ===================================================================

/-- Lemma 5.4.2: For each one-premise rule of G over a language without
equality, the conclusion sequent is falsifiable in M iff the premise is. (Lemma 5.4.2 covers both one-premise and two-premise rules; this is the one-premise primary.) -/
@[blueprint "chap5__lemma_5_4_2" (main := true)]
theorem ruleFalsificationIff1 {L : Language} (hL : L.withoutEquality) (M : Structure L)
    {prem conc : Sequent L} (rule : GentzenStep1 hL prem conc) :
    sequentFalsifiableIn M conc ↔ sequentFalsifiableIn M prem 

/-- Lemma 5.4.2 (companion, two-premise): For each two-premise rule of G
over a language without equality, the conclusion sequent is falsifiable in M iff at least one premise is
falsifiable. -/
@[blueprint "chap5__lemma_5_4_2" (main := true)]
theorem ruleFalsificationIff2 {L : Language} (hL : L.withoutEquality) (M : Structure L)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2 hL prem1 prem2 conc) :
    sequentFalsifiableIn M conc ↔
    (sequentFalsifiableIn M prem1 ∨ sequentFalsifiableIn M prem2) 

end LCS.FirstOrder.Gentzen
end

