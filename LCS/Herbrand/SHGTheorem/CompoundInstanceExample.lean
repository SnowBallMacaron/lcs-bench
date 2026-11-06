import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.SHGTheorem.CompoundInstances
import Attach
import LCS.Herbrand.SHGTheorem.CompoundInstanceExample.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

/-- Example 7.6.4 (companion type): Predicate symbols for the
compound instance example: P (unary) and Q (binary). -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExPred : Type where
  | P : CInstExPred
  | Q : CInstExPred

-- ===================================================================
-- Example 7.6.4 (companion type): CInstExConst
-- ===================================================================

/-- Example 7.6.4 (companion type): Constant symbols for the
compound instance example: a and b. -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExConst : Type where
  | a : CInstExConst
  | b : CInstExConst

-- ===================================================================
-- Example 7.6.4 (companion type): CInstExFunc
-- ===================================================================

/-- Example 7.6.4 (companion type): Function symbols for the
compound instance example: f (unary). -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExFunc : Type where
  | f : CInstExFunc

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExLang
-- ===================================================================

/-- Example 7.6.4 (companion def): A language with unary predicate P,
binary predicate Q, constants a and b, and unary function symbol f. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExLang : Language where
  funSymbols := CInstExFunc
  funArity := fun | .f => 1
  constSymbols := CInstExConst
  predSymbols := CInstExPred
  predArity := fun
    | .P => 1
    | .Q => 2

-- ===================================================================
-- Example 7.6.4 (helpers): cInstExVec1, cInstExVec2
-- ===================================================================

/-- Example 7.6.4 (companion def): Build a Fin 1 -> Term from a single
term in cInstExLang. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExVec1 (t : Term cInstExLang) :
    Fin 1 → Term cInstExLang
  | ⟨0, _⟩ => t

/-- Example 7.6.4 (companion def): Build a Fin 2 -> Term from two terms
in cInstExLang. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExVec2 (t1 t2 : Term cInstExLang) :
    Fin 2 → Term cInstExLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- Variables: x = 0, y = 1.

-- ===================================================================
-- Example 7.6.4: cInstExSkolemForm
-- ===================================================================

/-- Example 7.6.4: The Skolem form B = forall x(P(x) or forall y Q(y, f(x))) and (not P(a) and (not Q(a, f(a)) or not Q(b, f(a)))). Variables: x = 0, y = 1. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExSkolemForm : FormulaN cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  FormulaN.conj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN CInstExPred.P (cInstExVec1 (.var 0)))
        (FormulaN.all 1
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.var 1)
              (Term.func CInstExFunc.f
                (cInstExVec1 (.var 0))))))))
    (FormulaN.conj
      (FormulaN.neg
        (FormulaN.predN CInstExPred.P
          (cInstExVec1 (.const CInstExConst.a))))
      (FormulaN.disj
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.a) fa)))
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.b) fa)))))

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExCInstance
-- ===================================================================

/-- Example 7.6.4 (companion def): The c-instance (P(a) or (Q(a, f(a)) and Q(b, f(a)))) and (not P(a) and (not Q(a, f(a)) or not Q(b, f(a)))). Obtained by: instantiating forall x with a, then instantiating forall y with a and b, producing Q(a, f(a)) and Q(b, f(a)). -/
@[blueprint "chap7__example_7_6_4"]
def cInstExCInstance : FormulaN cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  FormulaN.conj
    (FormulaN.disj
      (FormulaN.predN CInstExPred.P
        (cInstExVec1 (.const CInstExConst.a)))
      (FormulaN.conj
        (FormulaN.predN CInstExPred.Q
          (cInstExVec2 (.const CInstExConst.a) fa))
        (FormulaN.predN CInstExPred.Q
          (cInstExVec2 (.const CInstExConst.b) fa))))
    (FormulaN.conj
      (FormulaN.neg
        (FormulaN.predN CInstExPred.P
          (cInstExVec1 (.const CInstExConst.a))))
      (FormulaN.disj
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.a) fa)))
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.b) fa)))))

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExDerivation
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.6.4 (companion def): The derivation tree witnessing that cInstExCInstance is a c-instance of cInstExSkolemForm. Constructed using: - connective true (outer conjunction) - forallInst 0 _ [a] [outer disjunction c-instance] - connective false (disjunction: P(a) or ...) - atom P(a) - forallInst 1 _ [a, b] [atom Q(a,f(a)), atom Q(b,f(a))] - connective true (inner conjunction) - negAtom P(a) - connective false (inner disjunction) - negAtom Q(a, f(a)) - negAtom Q(b, f(a)) -/
def cInstExDerivation : CInstance cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  -- P(a) is atomic
  let pa := FormulaN.predN CInstExPred.P
    (cInstExVec1 (.const CInstExConst.a))
  -- Q(a, f(a)) is atomic
  let qafa := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.const CInstExConst.a) fa)
  -- Q(b, f(a)) is atomic
  let qbfa := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.const CInstExConst.b) fa)
  -- Parent shape operands for the outer conjunction / inner disj / inner conj
  let pxBody := FormulaN.predN CInstExPred.P (cInstExVec1 (.var 0))
  let allyQ := FormulaN.all 1
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.var 1)
        (Term.func CInstExFunc.f
          (cInstExVec1 (.var 0)))))
  let outerForallBody := FormulaN.disj pxBody allyQ
  let outerForall := FormulaN.all 0 outerForallBody
  let notPa := FormulaN.neg
    (FormulaN.predN CInstExPred.P
      (cInstExVec1 (.const CInstExConst.a)))
  let notQafa := FormulaN.neg
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.const CInstExConst.a) fa))
  let notQbfa := FormulaN.neg
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.const CInstExConst.b) fa))
  let innerDisj := FormulaN.disj notQafa notQbfa
  let innerConj := FormulaN.conj notPa innerDisj
  -- Inner forall y Q(y, f(a)) instantiated with a and b (k=2: t₀=a, tsRest=[b])
  let innerForallInstBody := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.var 1)
      (Term.func CInstExFunc.f
        (cInstExVec1 (.const CInstExConst.a))))
  let innerForallInst :=
    CInstance.forallInst 1 innerForallInstBody
      (.const CInstExConst.a) (CInstance.atom qafa rfl)
      [.const CInstExConst.b]
      [CInstance.atom qbfa rfl]
      (by simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
      (by intro t ht; simp at ht; subst ht;
          simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
  -- P(a) or (Q(a,f(a)) and Q(b,f(a)))
  let leftDisj :=
    CInstance.connective false pa (.all 1 innerForallInstBody)
      (CInstance.atom pa rfl)
      innerForallInst
  -- forall x(P(x) or forall y Q(y, f(x))) instantiated with a (k=1: t₀=a)
  let outerForallInst :=
    CInstance.forallInst 0 outerForallBody
      (.const CInstExConst.a) leftDisj
      [] []
      (by simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
      (by intro _ h; simp at h)
  -- not P(a) and (not Q(a,f(a)) or not Q(b,f(a)))
  let rightConj :=
    CInstance.connective true notPa innerDisj
      (CInstance.negAtom pa rfl)
      (CInstance.connective false notQafa notQbfa
        (CInstance.negAtom qafa rfl)
        (CInstance.negAtom qbfa rfl))
  -- Outer conjunction
  CInstance.connective true outerForall innerConj outerForallInst rightConj

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- Example 7.6.4: the witness produces exactly the displayed c-instance,
with the ordered pair Q(a,f(a)), Q(b,f(a)) as its inner conjunction. -/
theorem cInstExDerivation_toFormula :
    cInstExDerivation.toFormula = cInstExCInstance := by
  simp! [cInstExDerivation, CInstance.toFormula, cInstExCInstance]

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- Example 7.6.4: every stored connective operand matches its child source,
and every universal child has the complete prescribed substitution source. -/
theorem cInstExDerivation_wellFormed : CInstance.WellFormed cInstExDerivation := by
  simp! [cInstExDerivation, CInstance.WellFormed, CInstance.WellFormedList,
    CInstance.source, formulaSubstN, termSubst, cInstExLang,
    cInstExVec1, cInstExVec2, funext_iff, Fin.forall_fin_succ]

/-- Example 7.6.4: the displayed formula is a c-instance of B, witnessed
by the explicit source-matching derivation. -/
@[blueprint "chap7__example_7_6_4" (main := true)]
theorem cInstExCInstance_isCInstanceOf :
    isCInstanceOf cInstExCInstance cInstExSkolemForm 

end LCS.Herbrand.SHGTheorem
end
