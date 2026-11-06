import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.KeyLemma
import LCS.CutElim.Interpolation.Craig.Lowering
import Attach
import LCS.CutElim.Interpolation.Craig.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Example 6.5.1 (companion type): InterpExPred
-- ===================================================================

/-- Example 6.5.1 (companion type): Predicate symbols for the
interpolation example: P (unary), Q (unary), S (unary). -/
@[blueprint "chap6__example_6_5_1"]
inductive InterpExPred : Type where
  | P : InterpExPred
  | Q : InterpExPred
  | S_ : InterpExPred

-- ===================================================================
-- Example 6.5.1 (companion type): InterpExConst
-- ===================================================================

/-- Example 6.5.1 (companion type): Constant symbols for the
interpolation example: a and b. -/
@[blueprint "chap6__example_6_5_1"]
inductive InterpExConst : Type where
  | a : InterpExConst
  | b : InterpExConst

-- ===================================================================
-- Example 6.5.1 (companion def): interpExLanguage
-- ===================================================================

/-- Example 6.5.1 (companion): The first-order language with unary
predicate symbols P, Q, S (each of arity 1), constant symbols a and b,
no function symbols, and no equality. -/
@[blueprint "chap6__example_6_5_1"]
def interpExLanguage : Language where
  funSymbols := Empty
  funArity := fun e => e.elim
  constSymbols := InterpExConst
  predSymbols := InterpExPred
  predArity := fun | .P => 1 | .Q => 1 | .S_ => 1
  hasEquality := false

-- ===================================================================
-- Example 6.5.1 (companion def): interpExAntecedent
-- ===================================================================

/-- Example 6.5.1 (companion): The formula A = P(a) /\ forall x Q(x),
the antecedent of the example implication. Variable x is encoded as
variable 0. -/
@[blueprint "chap6__example_6_5_1"]
def interpExAntecedent : FormulaN interpExLanguage :=
  .conj (.predN InterpExPred.P (fun _ => Term.const InterpExConst.a))
        (.all 0 (.predN InterpExPred.Q (fun _ => Term.var 0)))

-- ===================================================================
-- Example 6.5.1 (companion def): interpExConsequent
-- ===================================================================

/-- Example 6.5.1 (companion): The formula B = forall y S(y) \/ Q(b),
the consequent of the example implication. Variable y is encoded as
variable 1. -/
@[blueprint "chap6__example_6_5_1"]
def interpExConsequent : FormulaN interpExLanguage :=
  .disj (.all 1 (.predN InterpExPred.S_ (fun _ => Term.var 1)))
        (.predN InterpExPred.Q (fun _ => Term.const InterpExConst.b))

-- ===================================================================
-- Example 6.5.1 (companion def): interpExInterpolant
-- ===================================================================

/-- Example 6.5.1 (companion): The formula C = forall x Q(x), the
interpolant of the example implication. Q is the common predicate
symbol between A and B. -/
@[blueprint "chap6__example_6_5_1"]
def interpExInterpolant : FormulaN interpExLanguage :=
  .all 0 (.predN InterpExPred.Q (fun _ => Term.var 0))

-- ===================================================================
-- Example 6.5.1: interpolation_example
-- ===================================================================


/-- Example 6.5.1: ∀x Q(x) is an interpolant of
(P(a) ∧ ∀x Q(x)) ⊃ (∀y S(y) ∨ Q(b)). -/
@[blueprint "chap6__example_6_5_1" (main := true)]
theorem interpolation_example_spec : IsImplicationInterpolant
    interpExAntecedent interpExConsequent interpExInterpolant 

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

-- ===================================================================
-- formula_empty_pred_no_base
-- ===================================================================

theorem formula_empty_pred_no_base {L : Language}
    (hEmpty : ¬Nonempty L.predSymbols)
    (F : FormulaN L)
    (hNoEq : formulaNoEq F) : False := by
-- BEGIN PROOF
  induction F with
  | predN P _ => exact hEmpty ⟨P⟩
  | eq_ _ _ => exact hNoEq
  | neg A ih => exact ih hNoEq
  | conj A B ihA _ => exact ihA hNoEq.1
  | disj A B ihA _ => exact ihA hNoEq.1
  | impl A B ihA _ => exact ihA hNoEq.1
  | all _ A ih => exact ih hNoEq
  | ex _ A ih => exact ih hNoEq

-- ===================================================================
-- botFormula_lkBotProvable_or_lkBotRefutable
-- ===================================================================

theorem botFormula_lkBotProvable_or_lkBotRefutable {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (C : FormulaN L)
    (hOnlyBot : ∀ P : L.predSymbols, formulaPredSymbolsN C P → P = botP)
    (hNoEq : formulaNoEq C) :
    lkBotProvable botP hBotArity { antecedent := ([] : List (FormulaN L)), succedent := [C] } ∨
    lkBotProvable botP hBotArity { antecedent := [C], succedent := ([] : List (FormulaN L)) } := by
-- BEGIN PROOF
  induction C with
  | predN P ts =>
    have hP : P = botP := hOnlyBot P rfl
    subst P
    have hFormula : FormulaN.predN botP ts = botFormula botP hBotArity := by
      simp only [botFormula, FormulaN.predN.injEq, heq_eq_eq, true_and]
      funext i
      exact Fin.elim0 (hBotArity ▸ i)
    right
    rw [hFormula]
    exact ⟨.axiom_ ⟨[botFormula botP hBotArity], []⟩
      (Or.inr ⟨rfl, rfl⟩)⟩
  | eq_ _ _ _ => exact hNoEq.elim
  | neg A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · right
      exact lkBot_onePremise (.negLeft A [] []) hA
    · left
      exact lkBot_onePremise (.negRight A [] []) hA
  | conj A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        exact lkBot_twoPremise (.andRight A B [] []) hA hB
      · right
        exact lkBot_onePremise (.andLeftR A B [] []) hB
    · right
      exact lkBot_onePremise (.andLeftL A B [] []) hA
  | disj A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · left
      exact lkBot_onePremise (.orRightL A B [] []) hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        exact lkBot_onePremise (.orRightR A B [] []) hB
      · right
        exact lkBot_twoPremise (.orLeft A B [] []) hA hB
  | impl A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        have hPrem := lkBot_onePremise (.weakenLeft A [] [B]) hB
        exact lkBot_onePremise (.implRight A B [] []) hPrem
      · right
        exact lkBot_twoPremise (.implLeft A B [] [] [] []) hA hB
    · left
      have hPrem := lkBot_onePremise (.weakenRight B [A] []) hA
      exact lkBot_onePremise (.implRight A B [] []) hPrem
  | all x A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · left
      have hfresh :
          ∀ F ∈ (Sequent.mk [] ([] ++ [FormulaN.all x A])).antecedent ++
              (Sequent.mk [] ([] ++ [FormulaN.all x A])).succedent,
            x ∉ formulaFVN F := by
        intro F hF
        simp only [List.nil_append, List.mem_singleton] at hF
        subst F
        rintro ⟨_, hx⟩
        exact hx rfl
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[], [formulaSubstN A (.var x) x]⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.allRight x x A [] [] hfresh (isFreeForN_var_self A x)) hPrem
    · right
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[formulaSubstN A (.var x) x], []⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.allLeft (.var x) x A [] [] (isFreeForN_var_self A x)) hPrem
  | ex x A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · left
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[], [formulaSubstN A (.var x) x]⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.exRight (.var x) x A [] [] (isFreeForN_var_self A x)) hPrem
    · right
      have hfresh :
          ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: []) []).antecedent ++
              (Sequent.mk (FormulaN.ex x A :: []) []).succedent,
            x ∉ formulaFVN F := by
        intro F hF
        simp only [List.append_nil, List.mem_singleton] at hF
        subst F
        rintro ⟨_, hx⟩
        exact hx rfl
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[formulaSubstN A (.var x) x], []⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.exLeft x x A [] [] hfresh (isFreeForN_var_self A x)) hPrem

end LCS.CutElim.Interpolation
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

/-- Internal existence form of Craig interpolation in the common-predicate
case.  The proof adjoins a genuinely fresh nullary predicate, applies the
key lemma there, and then lowers both proof obligations simultaneously by
replacing the fresh predicate with Gallier's contradiction over `P`. -/
@[blueprint "chap6__theorem_6_5_1" (main := true)]
theorem craig_interpolant_common_pred_exists {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P)
    (hPB : formulaPredSymbolsN B P) :
    ∃ C, IsImplicationInterpolant A B C 

-- ===================================================================
-- Theorem 6.5.1 (part b): craig_interpolation_no_common_pred
-- ===================================================================

/-- Theorem 6.5.1 (part b, required helper): Let `L` be a first-order
language without equality. If `A ⊃ B` is LK-provable and `A` and `B`
share no predicate symbol, then either `A →` is LK-provable or `→ B`
is LK-provable. -/
@[blueprint "chap6__theorem_6_5_1" (main := true)]
theorem craig_interpolation_no_common_pred {L : Language}
    (A B : FormulaN L)
    (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (hNoPred : ∀ P : L.predSymbols, ¬ (formulaPredSymbolsN A P ∧ formulaPredSymbolsN B P)) :
    folkProvable { antecedent := [A], succedent := [] } ∨
    folkProvable { antecedent := [], succedent := [B] } 

end LCS.CutElim.Interpolation
end
