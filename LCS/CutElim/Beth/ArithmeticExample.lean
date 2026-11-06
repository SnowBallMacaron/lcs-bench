import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import LCS.CutElim.Beth.Definability
import Attach
import LCS.CutElim.Beth.ArithmeticExample.ProofsStamp

section
namespace LCS.CutElim.Beth
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

/-- Example 6.6.1 (companion): Function symbols for the exact language
of the example: unary successor and binary addition. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExampleFunc : Type where
  | succ : BethExampleFunc
  | plus : BethExampleFunc

/-- Example 6.6.1 (companion): The sole constant symbol 0. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExampleConst : Type where
  | zero : BethExampleConst

/-- Example 6.6.1 (companion): The sole non-equality predicate symbol <. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExamplePred : Type where
  | lt : BethExamplePred

/-- Example 6.6.1 (companion): The exact equality language with constant 0,
unary function S, binary function +, and binary predicate <. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_arithWithOrder : Language :=
  { funSymbols := BethExampleFunc
    funArity := fun
      | .succ => 1
      | .plus => 2
    constSymbols := BethExampleConst
    predSymbols := BethExamplePred
    predArity := fun
      | .lt => 2
    hasEquality := true }

/-- Example 6.6.1 (companion): Build the term S(t). -/
@[blueprint "chap6__example_6_6_1"]
def bethExampleSucc (t : Term bethExample_arithWithOrder) :
    Term bethExample_arithWithOrder :=
  Term.func BethExampleFunc.succ (vec1 t)

/-- Example 6.6.1 (companion): Build the term t₁ + t₂. -/
@[blueprint "chap6__example_6_6_1"]
def bethExamplePlus (t1 t2 : Term bethExample_arithWithOrder) :
    Term bethExample_arithWithOrder :=
  Term.func BethExampleFunc.plus (vec2 t1 t2)

/-- Example 6.6.1 (companion): The constant term 0. -/
@[blueprint "chap6__example_6_6_1"]
def bethExampleZero : Term bethExample_arithWithOrder :=
  Term.const BethExampleConst.zero

-- ===================================================================
-- Example 6.6.1 (companion defs): axiom formulae
-- ===================================================================
/-- Example 6.6.1 (companion): First of the five axioms of Example 6.6.1:
`forall x, ¬(S(x) = 0)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_succNonZeroAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.neg
      (FormulaN.eq_ rfl (bethExampleSucc (Term.var 0)) bethExampleZero))

/-- Example 6.6.1 (companion): Second of the five axioms:
`forall x y, S(x) = S(y) → x = y`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_succInjectiveAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.impl
      (FormulaN.eq_ rfl
        (bethExampleSucc (Term.var 0))
        (bethExampleSucc (Term.var 1)))
      (FormulaN.eq_ rfl (Term.var 0) (Term.var 1))))

/-- Example 6.6.1 (companion): Third of the five axioms:
`forall x, x + 0 = x`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_addZeroAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.eq_ rfl
      (bethExamplePlus (Term.var 0) bethExampleZero)
      (Term.var 0))

/-- Example 6.6.1 (companion): Fourth of the five axioms:
`forall x y, x + S(y) = S(x + y)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_addSuccAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.eq_ rfl
      (bethExamplePlus (Term.var 0) (bethExampleSucc (Term.var 1)))
      (bethExampleSucc (bethExamplePlus (Term.var 0) (Term.var 1)))))

/-- Example 6.6.1 (companion): Fifth of the five axioms:
`forall x, 0 < S(x)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_zeroLtSuccAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.predN BethExamplePred.lt
      (vec2 bethExampleZero (bethExampleSucc (Term.var 0))))

/-- Example 6.6.1 (companion): The conjunction of the five textbook axioms
of Example 6.6.1. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_fiveAxioms : FormulaN bethExample_arithWithOrder :=
  FormulaN.conj
    (FormulaN.conj
      (FormulaN.conj
        (FormulaN.conj
          bethExample_succNonZeroAxiom
          bethExample_succInjectiveAxiom)
        bethExample_addZeroAxiom)
      bethExample_addSuccAxiom)
    bethExample_zeroLtSuccAxiom

-- ===================================================================
-- Example 6.6.1 (companion defs): structures
-- ===================================================================
/-- Example 6.6.1 (companion): Standard arithmetic structure on ℕ, in
which < is the usual strict order. Used as structure M1 in the
non-implicit-definability witness. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_standardOrderStructure :
    Structure bethExample_arithWithOrder where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | BethExampleFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | BethExampleFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | BethExampleConst.zero => 0
  interpPred
    | BethExamplePred.lt, args =>
        (args ⟨0, by decide⟩) < (args ⟨1, by decide⟩)

/-- Example 6.6.1 (companion): Nonstandard arithmetic structure on ℕ,
agreeing with the standard structure on 0, S, +, but interpreting
`x < y` exactly as `x = 0`. Used as structure M2 in the
non-implicit-definability witness. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_nonstandardOrderStructure :
    Structure bethExample_arithWithOrder where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | BethExampleFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | BethExampleFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | BethExampleConst.zero => 0
  interpPred
    | BethExamplePred.lt, args =>
        args ⟨0, by decide⟩ = 0

-- ===================================================================
-- Example 6.6.1 (companion theorem): bethExample_nonImplicitDef
-- ===================================================================
-- ===================================================================
-- Example 6.6.1 (companion defs): order characterization
-- ===================================================================
/-- Example 6.6.1 (companion): The order characterization axiom
`forall x y (x < y iff exists z (y = x + S(z)))` added to the five
axioms to give a six-axiom theory in which < is explicitly definable.
Uses FormulaN.equiv (abbreviation for conj (impl A B) (impl B A)). -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_orderCharAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.equiv
      (FormulaN.predN BethExamplePred.lt
        (vec2 (Term.var 0) (Term.var 1)))
      (FormulaN.ex 2
        (FormulaN.eq_ rfl (Term.var 1)
          (bethExamplePlus (Term.var 0)
            (bethExampleSucc (Term.var 2)))))))

/-- Example 6.6.1 (companion): The textbook's explicit definition
`D = exists z (y = x + S(z))` of < in the six-axiom theory. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_explicitDefOfOrder : FormulaN bethExample_arithWithOrder :=
  FormulaN.ex 2
    (FormulaN.eq_ rfl (Term.var 1)
      (bethExamplePlus (Term.var 0)
        (bethExampleSucc (Term.var 2))))

/-- Example 6.6.1 (companion): The extended 6-axiom theory (five
original axioms together with the order-characterization axiom). -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_sixAxioms : FormulaN bethExample_arithWithOrder :=
  FormulaN.conj bethExample_fiveAxioms bethExample_orderCharAxiom

-- ===================================================================
-- Example 6.6.1: claim (a) five-axiom theory does NOT implicitly
-- define <
-- ===================================================================
/-- Example 6.6.1: (claim a) Under the five axioms, < is NOT
implicitly definable from {=, 0, S, +}: there are two structures on ℕ
that agree on 0, S, +, both satisfy the five axioms, and disagree on <. -/
@[blueprint "chap6__example_6_6_1" (main := true)]
theorem bethExample_fiveAxioms_notImplicitlyDefinesLt :
    ∃ (M1 M2 : Structure bethExample_arithWithOrder),
      M1.carrier = Nat ∧ M2.carrier = Nat ∧
      HEq M1.interpFunc M2.interpFunc ∧
      HEq M1.interpConst M2.interpConst ∧
      validInN M1 bethExample_fiveAxioms ∧
      validInN M2 bethExample_fiveAxioms ∧
      ¬ (HEq M1.interpPred M2.interpPred) 

-- ===================================================================
-- Example 6.6.1: claim (b) the six-axiom theory explicitly defines <
-- ===================================================================
/-- Example 6.6.1: (claim b) Adding the order-characterization axiom
∀x∀y (x<y ≡ ∃z (y = x + S(z))) to the five axioms yields a theory in
which < is explicitly defined by D = ∃z (y = x + S(z)). -/
@[blueprint "chap6__example_6_6_1" (main := true)]
theorem bethExample_sixAxioms_explicitlyDefinesLt :
    universallyValidN
      (FormulaN.impl bethExample_sixAxioms
        (bethUniversalPrefix 2
          (FormulaN.equiv
            (bethPredApplied BethExamplePred.lt)
            bethExample_explicitDefOfOrder))) 

end LCS.CutElim.Beth
end
