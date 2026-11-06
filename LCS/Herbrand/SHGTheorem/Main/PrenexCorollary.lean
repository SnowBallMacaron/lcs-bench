import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemHerbrandGodel
import LCS.Herbrand.SHGTheorem.Main.PrenexSkolemForm
import LCS.Herbrand.SHGTheorem.Main.CInstanceGroundMatrix
import Attach
import LCS.Herbrand.SHGTheorem.Main.PrenexCorollary.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem

private theorem universalPrenex_eval_prenexMatrix {L : Language}
    (B : FormulaN L) (hUniversal : UniversalPrenexFormula B)
    (M : Structure L) (s : Assignment M)
    (hEval : formulaEvalN M B s) :
    formulaEvalN M (prenexMatrix B) s := by
  induction B generalizing s with
  | all x C ih =>
    have hBody :=
      universalPrenexFormula_body_of_all C x hUniversal
    have hSelf : assignUpdate s x (s x) = s := by
      funext y
      unfold assignUpdate
      split <;> simp_all
    have hEvalC := hEval (s x)
    rw [hSelf] at hEvalC
    exact ih hBody s hEvalC
  | ex x C ih =>
    have hImpossible :=
      hUniversal.2
        (QuantifierKind.existential, x)
        (by simp [prenexPrefix])
    cases hImpossible
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact hEval /- ATTACH-BLOCKER: private declaration -/

private theorem applyGroundSubstitution_eval_of_all_assignments
    {L : Language} (M : Structure L) :
    ∀ (matrix : FormulaN L) (substs : List (Nat × Term L)),
      (∀ p ∈ substs, Term.isClosed p.2) →
      (∀ s : Assignment M, formulaEvalN M matrix s) →
      ∀ s : Assignment M,
        formulaEvalN M
          (applyGroundSubstitution matrix substs) s := by
  intro matrix substs
  induction substs generalizing matrix with
  | nil =>
    intro hClosed hAll s
    exact hAll s
  | cons p rest ih =>
    intro hClosed hAll s
    have hpClosed : Term.isClosed p.2 :=
      hClosed p List.mem_cons_self
    have hRestClosed :
        ∀ q ∈ rest, Term.isClosed q.2 := by
      intro q hq
      exact hClosed q (List.mem_cons_of_mem _ hq)
    have hSubAll :
        ∀ s' : Assignment M,
          formulaEvalN M
            (formulaSubstN matrix p.2 p.1) s' := by
      intro s'
      rw [formulaSubstEval_closed matrix p.2 p.1 hpClosed s']
      exact hAll _
    exact ih (formulaSubstN matrix p.2 p.1)
      hRestClosed hSubAll s /- ATTACH-BLOCKER: private declaration -/

theorem universalPrenex_eval_groundSubstitution
    {L : Language} (B : FormulaN L)
    (hUniversal : UniversalPrenexFormula B)
    (hClosed : FormulaN.isClosed B)
    (M : Structure L) (s : Assignment M)
    (hEval : formulaEvalN M B s)
    (substs : List (Nat × Term L))
    (hSubstsClosed : ∀ p ∈ substs, Term.isClosed p.2) :
    formulaEvalN M
      (applyGroundSubstitution (prenexMatrix B) substs) s := by
  have hEvalAll : ∀ s' : Assignment M, formulaEvalN M B s' := by
    intro s'
    apply (coincidenceLemmaN M B s s' (fun y hy => ?_)).mp hEval
    rw [hClosed] at hy
    exact hy.elim
  have hMatrixAll :
      ∀ s' : Assignment M,
        formulaEvalN M (prenexMatrix B) s' := by
    intro s'
    exact universalPrenex_eval_prenexMatrix
      B hUniversal M s' (hEvalAll s')
  exact applyGroundSubstitution_eval_of_all_assignments
    M (prenexMatrix B) substs hSubstsClosed hMatrixAll s /- ATTACH-BLOCKER: private declaration -/

-- ===================================================================
-- Corollary 7.6.1: shgCorollary_prenex
-- ===================================================================

/-- Corollary after Theorem 7.6.1: If A is a prenex sentence in NNF, A is unsatisfiable iff a finite conjunction of ground substitution instances of the matrix of the Skolem form B of A is unsatisfiable. Follows from Theorem 7.6.1 (part a): when A is prenex, SK(A) is prenex with only universal quantifiers (existentials eliminated), so any c-instance C of B is (by Def 7.6.3 case iii) a finite conjunction of ground substitution instances of the matrix of B. Under the current metadata policy, this work belongs to Theorem 7.6.1 rather than a standalone corollary item. -/
@[blueprint "chap7__theorem_7_6_1" (main := true)]
theorem shgCorollary_prenex {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (_hPrenex : LCS.Herbrand.PrenexForm.isPrenex A) :
    ¬ satisfiableN A ↔
      ∃ (F : FormulaN spec.language),
        isFiniteGroundConjunctionOfMatrix F (SK spec) ∧
        ¬ satisfiableN F

end LCS.Herbrand.SHGTheorem.Main
end
