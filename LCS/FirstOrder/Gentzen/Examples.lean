import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FirstOrder.Gentzen.DeductionTrees
import Attach
import LCS.FirstOrder.Gentzen.Examples.ProofsStamp

/-! # Examples 5.4.1 and 5.4.2 (Section 5.4.2)

The two G-proof trees worked out in Section 5.4.2.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

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
