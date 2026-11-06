import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.SHGTheorem.SkolemForm
import Attach
import LCS.Herbrand.SHGTheorem.SkolemFormExample.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution
section SkExComputation
set_option backward.isDefEq.respectTransparency false

/-- Example 7.6.3: the fixed original-root environment for all four
Skolem computations. Its allocations are y, u, w, in preorder. -/
@[blueprint "chap7__example_7_6_3"]
def skExSpec : SkolemSpec usExLang where
  source := usExFormula
  hNNF := by trivial
  hRect := by
    simp [usExFormula, usExLang,
      LCS.FirstOrder.Semantics.Subformulae.isRectified,
      LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.FirstOrder.SyntaxN.Variables.formulaFVN, LCS.FirstOrder.SyntaxN.Variables.formulaBVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      usExVec1, usExVec2, Fin.exists_fin_succ, Fin.forall_fin_succ] <;>
      (try constructor) <;> (intros; omega)
  hSentence := by
    change LCS.FirstOrder.SyntaxN.Variables.formulaFVN usExFormula = (∅ : Set Nat)
    funext x
    apply propext
    simp [usExFormula, usExLang, LCS.FirstOrder.SyntaxN.Variables.formulaFVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      usExVec1, usExVec2, Fin.exists_fin_succ, Fin.forall_fin_succ] <;> omega

/-- Example 7.6.3: the positive-rank fresh functions allocated to A.
The names g and f below identify the original y and u indices. -/
@[blueprint "chap7__example_7_6_3"]
abbrev SKExSkolemFunc : Type := skExSpec.language.funSymbols

@[blueprint "chap7__example_7_6_3"]
def SKExSkolemFunc.g : SKExSkolemFunc := .inr ⟨⟨0, by decide⟩, by decide⟩

@[blueprint "chap7__example_7_6_3"]
def SKExSkolemFunc.f : SKExSkolemFunc := .inr ⟨⟨1, by decide⟩, by decide⟩

/-- Example 7.6.3: the exact Skolem extension of the original language.
The old constant a embeds on the left; the fresh constant c is allocated
to w. The positive-rank allocations are g for y and f for u. -/
@[blueprint "chap7__example_7_6_3"]
def skExSkolemLang : Language := skExSpec.language

/-- Example 7.6.3: the genuine fresh constant allocated to the empty
universal scope of w, distinct from every embedded base constant. -/
@[blueprint "chap7__example_7_6_3"]
def skExC : skExSkolemLang.constSymbols := .inr ⟨⟨2, by decide⟩, by decide⟩

-- ===================================================================
-- Example 7.6.3 (helpers): skExVec1, skExVec2
-- ===================================================================

/-- Example 7.6.3 (companion def): Build a Fin 1 -> Term from a single
term in skExSkolemLang. -/
@[blueprint "chap7__example_7_6_3"]
def skExVec1 (t : Term skExSkolemLang) :
    Fin 1 → Term skExSkolemLang
  | ⟨0, _⟩ => t

/-- Example 7.6.3 (companion def): Build a Fin 2 -> Term from two terms
in skExSkolemLang. -/
@[blueprint "chap7__example_7_6_3"]
def skExVec2 (t1 t2 : Term skExSkolemLang) :
    Fin 2 → Term skExSkolemLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- Variables: x = 0, y = 1, z = 2, u = 3, w = 4.

-- ===================================================================
-- Example 7.6.3: skExFormula
-- ===================================================================

/-- Example 7.6.3: The formula A = forall x(P(a) or exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) or exists w Q(a, w), same formula as Example 7.6.2, reencoded in skExSkolemLang for demonstrating the Skolem form computation. Variables: x = 0, y = 1, z = 2, u = 3, w = 4. -/
@[blueprint "chap7__example_7_6_3"]
def skExFormula : FormulaN skExSkolemLang :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (skExVec1 (.const (.inl USExConst.a))))
        (FormulaN.ex 1
          (FormulaN.conj
            (FormulaN.predN USExPred.Q1
              (skExVec1 (.var 1)))
            (FormulaN.all 2
              (FormulaN.disj
                (FormulaN.predN USExPred.P2
                  (skExVec2 (.var 1) (.var 2)))
                (FormulaN.ex 3
                  (FormulaN.predN USExPred.Q2
                    (skExVec2 (.var 0) (.var 3))))))))))
    (FormulaN.ex 4
      (FormulaN.predN USExPred.Q2
        (skExVec2 (.const (.inl USExConst.a)) (.var 4))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsW
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists w Q(a, w)) = Q(a, c), where c is the Skolem constant for the empty universal scope. The existential quantifier exists w is eliminated by replacing w with the Skolem constant c (a fresh constant symbol). -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsW : FormulaN skExSkolemLang :=
  FormulaN.predN USExPred.Q2
    (skExVec2 (.const (.inl USExConst.a))
      (Term.const skExC))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsU
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists u Q(x, u)) = Q(x, f(x, z)), where f is the binary Skolem function for the universal scope <x, z>. Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsU : FormulaN skExSkolemLang :=
  FormulaN.predN USExPred.Q2
    (skExVec2 (.var 0)
      (Term.func SKExSkolemFunc.f
        (skExVec2 (.var 0) (.var 2))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsY
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) = Q(g(x)) and forall z(P(g(x), z) or Q(x, f(x, z))), where g is the unary Skolem function for the universal scope <x>. Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsY : FormulaN skExSkolemLang :=
  let gx := Term.func SKExSkolemFunc.g (skExVec1 (.var 0))
  FormulaN.conj
    (FormulaN.predN USExPred.Q1 (skExVec1 gx))
    (FormulaN.all 2
      (FormulaN.disj
        (FormulaN.predN USExPred.P2 (skExVec2 gx (.var 2)))
        (FormulaN.predN USExPred.Q2
          (skExVec2 (.var 0)
            (Term.func SKExSkolemFunc.f
              (skExVec2 (.var 0) (.var 2)))))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExFullSK
-- ===================================================================

/-- Example 7.6.3 (companion def): The complete Skolem form SK(A) = forall x(P(a) or (Q(g(x)) and forall z(P(g(x), z) or Q(x, f(x, z))))) or Q(a, c). Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExFullSK : FormulaN skExSkolemLang :=
  let gx := Term.func SKExSkolemFunc.g (skExVec1 (.var 0))
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (skExVec1 (.const (.inl USExConst.a))))
        (FormulaN.conj
          (FormulaN.predN USExPred.Q1 (skExVec1 gx))
          (FormulaN.all 2
            (FormulaN.disj
              (FormulaN.predN USExPred.P2
                (skExVec2 gx (.var 2)))
              (FormulaN.predN USExPred.Q2
                (skExVec2 (.var 0)
                  (Term.func SKExSkolemFunc.f
                    (skExVec2 (.var 0) (.var 2))))))))))
    (FormulaN.predN USExPred.Q2
      (skExVec2 (.const (.inl USExConst.a))
        (Term.const skExC)))

/-- Fixed-origin SK equation for w, using original allocation index 2. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsW_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsWSubformula)
      [] [⟨2, by decide⟩] = some (skExSKExistsW, 1) 

/-- Fixed-origin SK equation for u: index 1 retains both x and z, even
though z does not occur free in the detached formula exists u Q(x,u). -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsU_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsUSubformula)
      [0, 2] [⟨1, by decide⟩] = some (skExSKExistsU, 1) 

/-- Fixed-origin SK equation for y and its nested u, using indices 0,1
of the original A rather than allocating symbols from the detached body. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsY_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsYSubformula)
      [0] [⟨0, by decide⟩, ⟨1, by decide⟩] = some (skExSKExistsY, 2) 

/-- The complete displayed SK(A), computed using the same original-root
allocation environment as the three indexed subformula equations. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExFullSK_eq : SK skExSpec = skExFullSK  

end SkExComputation
end LCS.Herbrand.SHGTheorem
end
