import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.Model
import LCS.FirstOrder.Gentzen.Hintikka.SearchClosure
import LCS.FirstOrder.Gentzen.Hintikka.PathModel
import LCS.FirstOrder.Gentzen.Hintikka.Construction
import Attach
import LCS.FirstOrder.Gentzen.Hintikka.Examples.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Example 5.4.3 (companion def): The formula
A = ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z)) — identical to the formula of
Example 5.4.1, on the same language exampleLangPQ. -/
@[blueprint "chap5__example_5_4_3"]
def exSearchFormula_5_4_3 : FormulaN exampleLangPQ :=
  exFormulaExistentialImpl

-- ===================================================================
-- Example 5.4.3: exSearchProofTree_5_4_3
-- ===================================================================

/-- Example 5.4.3: The round-three proof tree for the search on
    → ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z)). With x = 0 and z = 2,
    y₀ = 1 is the least absent variable; the canonical availability
    stream starts at y₁ = 4. The single extended ∃:right inference uses
    both terms [y₀, y₁], with leaf Q(y₁), P → Q(y₀), Q(y₁), ∃z Q(z). -/
@[blueprint "chap5__example_5_4_3"]
noncomputable def exSearchProofTree_5_4_3 :
    GProofTreeExt (Sequent.mk ([] : List (FormulaN exampleLangPQ))
                               [exSearchFormula_5_4_3]) :=
  let pF : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i)
  let qVar (n : Nat) : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.Q (fun _ => Term.var n)
  let exZQz : FormulaN exampleLangPQ := FormulaN.ex 2 (qVar 2)
  let exXPimplQx : FormulaN exampleLangPQ :=
    FormulaN.ex 0 (FormulaN.impl pF (qVar 0))
  let Aimpl : FormulaN exampleLangPQ := formulaSubstN pF (Term.var 4) 0
  let pImplQy1 : FormulaN exampleLangPQ := FormulaN.impl Aimpl (qVar 4)
  -- pF = Aimpl up to funext on the vacuous Fin 0 argument
  have pF_eq_Aimpl : pF = Aimpl := by
    simp [Aimpl, pF, formulaSubstN]
    apply congrArg (FormulaN.predN (L := exampleLangPQ) ExPredPQ.P)
    funext i; exact Fin.elim0 i
  -- Leaf 1: P → P[y_1/x], ∃z Q(z)   (axiom, witnessed by Aimpl = pF via funext)
  let leaf1Seq : Sequent exampleLangPQ :=
    Sequent.mk ([pF] ++ []) ([Aimpl] ++ [exZQz])
  let tLeaf1 : GProofTreeExt leaf1Seq :=
    GProofTreeExt.axiom_ leaf1Seq
      ⟨Aimpl,
       by
         show Aimpl ∈ [pF] ++ ([] : List (FormulaN exampleLangPQ))
         rw [← pF_eq_Aimpl]; exact List.Mem.head _,
       by
         show Aimpl ∈ [Aimpl] ++ [exZQz]
         exact List.Mem.head _⟩
  -- Leaf 2: Q(y_1), P → Q(y_0), Q(y_1), ∃z Q(z)   (axiom on Q(y_1))
  let leaf2Seq : Sequent exampleLangPQ :=
    Sequent.mk [qVar 4, pF] ([] ++ [qVar 1, qVar 4, exZQz] ++ [])
  let tLeaf2 : GProofTreeExt leaf2Seq :=
    GProofTreeExt.axiom_ leaf2Seq ⟨qVar 4, List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩
  -- ∃:right (extended, with ts = [Term.var 1, Term.var 4]):
  --   Q(y_1), P → ∃z Q(z)
  let exRightConc : Sequent exampleLangPQ :=
    Sequent.mk [qVar 4, pF] ([] ++ [exZQz] ++ [])
  let tExRight : GProofTreeExt exRightConc :=
    GProofTreeExt.onePremise
      (GentzenStep1Ext.exRight [Term.var 1, Term.var 4] [qVar 4, pF] [] [] 2 (qVar 2)
        (by decide)
        (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> simp [isFreeForN, qVar]))
      tLeaf2
  -- ⊃:left: P, P ⊃ Q(y_1) → ∃z Q(z)
  let implLeftConc : Sequent exampleLangPQ :=
    Sequent.mk ([pF] ++ [pImplQy1] ++ []) [exZQz]
  let tImplLeft : GProofTreeExt implLeftConc :=
    GProofTreeExt.twoPremise
      (GentzenStep2Ext.implLeft [pF] [] [exZQz] Aimpl (qVar 4))
      tLeaf1
      tExRight
  -- ⊃:right (inner): P ⊃ Q(y_1) → P ⊃ ∃z Q(z)
  let implRightInnerConc : Sequent exampleLangPQ :=
    Sequent.mk [pImplQy1] ([] ++ [FormulaN.impl pF exZQz] ++ [])
  let tImplRightInner : GProofTreeExt implRightInnerConc :=
    GProofTreeExt.onePremise
      (GentzenStep1Ext.implRight [pImplQy1] [] [] pF exZQz)
      tImplLeft
  -- ∃:left (y = 4): ∃x(P ⊃ Q(x)) → P ⊃ ∃z Q(z)
  let exLeftConc : Sequent exampleLangPQ :=
    Sequent.mk ([] ++ [exXPimplQx] ++ []) [FormulaN.impl pF exZQz]
  let tExLeft : GProofTreeExt exLeftConc :=
    GProofTreeExt.onePremise
      (GentzenStep1Ext.exLeft 4 [] [] [FormulaN.impl pF exZQz] 0
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
            · exact (by decide : (4 : Nat) ≠ 0) hj
          · -- F = impl pF exZQz
            intro h
            simp [formulaFVN, pF, exZQz, qVar, termFV] at h
            rcases h with ⟨i, _⟩ | ⟨hSet, _h2⟩
            · exact Fin.elim0 i
            · rcases hSet with ⟨_j, hj⟩
              exact (by decide : (4 : Nat) ≠ 2) hj)
        (by simp [isFreeForN, pF, qVar]))
      tImplRightInner
  -- ⊃:right (outer): → ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∃z Q(z))
  GProofTreeExt.onePremise
    (GentzenStep1Ext.implRight [] [] [] exXPimplQx (FormulaN.impl pF exZQz))
    tExLeft

-- ===================================================================
-- Example 5.4.4 (companion def): exSearchFormula_5_4_4
-- ===================================================================

/-- Example 5.4.4 (companion def): The formula
B = ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∀z Q(z)), where P is a propositional letter
and Q is a unary predicate symbol. Variables: x = 0, z = 2. Differs
from Example 5.4.1 only in the final quantifier (∀z vs ∃z). -/
@[blueprint "chap5__example_5_4_4"]
def exSearchFormula_5_4_4 : FormulaN exampleLangPQ :=
  let pF : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i)
  let qVar (n : Nat) : FormulaN exampleLangPQ :=
    FormulaN.predN ExPredPQ.Q (fun _ => Term.var n)
  FormulaN.impl
    (FormulaN.ex 0 (FormulaN.impl pF (qVar 0)))
    (FormulaN.impl pF (FormulaN.all 2 (qVar 2)))

-- ===================================================================
-- Example 5.4.4 (companion type): exCounterDomain
-- ===================================================================

/-- Example 5.4.4 (companion type): An enumeration type with three
elements y_0, y_1, y_2 representing the activated terms in TERM_0 at
the end of the search trace for Example 5.4.4. -/
@[blueprint "chap5__example_5_4_4"]
inductive exCounterDomain : Type where
  | y0 : exCounterDomain
  | y1 : exCounterDomain
  | y2 : exCounterDomain

-- ===================================================================
-- Example 5.4.4: exSearchCounterModel
-- ===================================================================

/-- Example 5.4.4: A counter-example structure for
B = ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∀z Q(z)).
Domain {y_0, y_1, y_2}; P is vacuously true (arity 0); Q is true on
y_0 and y_1, false on y_2. Witnesses the textbook's falsification:
under this structure, (∃x(P ⊃ Q(x))) holds (take x = y_0 so P ⊃ Q(y_0)
reduces to True) and P holds, but ∀z Q(z) fails at z = y_2. -/
@[blueprint "chap5__example_5_4_4"]
def exSearchCounterModel : Structure exampleLangPQ where
  carrier := exCounterDomain
  carrierNonempty := ⟨exCounterDomain.y0⟩
  interpFunc f := Empty.elim f
  interpConst c := Empty.elim c
  interpPred
    | ExPredPQ.P, _ => True
    | ExPredPQ.Q, args =>
      match args ⟨0, by decide⟩ with
      | .y0 => True
      | .y1 => True
      | .y2 => False

-- ===================================================================
-- Example 5.4.4 (companion theorem): exSearchCounterModel_falsifies
-- ===================================================================

/-- Example 5.4.4 (companion theorem): The counter-example structure
`exSearchCounterModel` falsifies the sequent → B, where
B = ∃x(P ⊃ Q(x)) ⊃ (P ⊃ ∀z Q(z)). Proof: pick any assignment; the
antecedent list is empty so the left conjunct is vacuous; for the
succedent formula B, we exhibit that under the assignment the impl B
fails because its hypothesis ∃x(P ⊃ Q(x)) holds (witness x = y_0 with
Q(y_0) = True) and P holds (arity 0, always True) but ∀z Q(z) fails at
z = y_2 since Q(y_2) = False. -/
@[blueprint "chap5__example_5_4_4" (main := true)]
theorem exSearchCounterModel_falsifies :
    sequentFalsifiableIn exSearchCounterModel
      (Sequent.mk [] [exSearchFormula_5_4_4]) 

/-- Example 5.4.4: The two-element counterexample domain {y₁, y₂}. -/
@[blueprint "chap5__example_5_4_4"]
inductive exCounterDomainTwo : Type where
  | y1
  | y2

/-- Example 5.4.4: P is true; Q is true at y₁ and false at y₂. -/
@[blueprint "chap5__example_5_4_4"]
def exSearchCounterModelTwo : Structure exampleLangPQ where
  carrier := exCounterDomainTwo
  carrierNonempty := ⟨exCounterDomainTwo.y1⟩
  interpFunc f := Empty.elim f
  interpConst c := Empty.elim c
  interpPred
    | ExPredPQ.P, _ => True
    | ExPredPQ.Q, args =>
      match args ⟨0, by decide⟩ with
      | .y1 => True
      | .y2 => False

/-- Example 5.4.4: The input sequent is falsified by the two-element structure. -/
@[blueprint "chap5__example_5_4_4" (main := true)]
theorem exSearchCounterModelTwo_falsifies :
    sequentFalsifiableIn exSearchCounterModelTwo (.mk [] [exSearchFormula_5_4_4]) 

end LCS.FirstOrder.Gentzen.Hintikka
end

