import LCS.SLD.LogicProgramming.Queries
import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.ExampleProgram
import LCS.SLD.LogicProgramming.Correctness.ExampleTeacherRefutations
import LCS.SLD.LogicProgramming.Correctness.ExampleRichRefutations
import Attach
import LCS.SLD.LogicProgramming.Correctness.ExampleAnswers.ProofsStamp

/-! # Example 9.5.4: computed answers

Section 9.5.3: the answers computed by the four refutations, the indefinite answer and its validity. -/

section
namespace LCS.SLD.LogicProgramming.Correctness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.LogicProgramming

/-- Example 9.5.4 (companion): The indefinite answer substitution
    (Y_1/Y, Y_1/Z): maps both Y (var 2) and Z (var 1) to the fresh
    variable Y_1 (var 22). For all other variables, acts as identity. -/
@[blueprint "chap9__example_9_5_4"]
def exIndefiniteAnswer : Nat → Term exCorrectnessLang
  | 1 => Term.var 22   -- Z -> Y_1
  | 2 => Term.var 22   -- Y -> Y_1
  | n => Term.var n

/-- The original five-clause P of Examples 9.5.1 and 9.5.4.
    The two query clauses are added only in exCorrectnessProgram. -/
@[blueprint "chap9__example_9_5_4"]
def exOriginalProgram : Set (FOHornClause exCorrectnessLang exCorrectnessLang_noEq) :=
  fun c => c ∈ [ex954_C1, ex954_C2, ex954_C3, ex954_C4, exCorrectnessGoalClause1]

/-- Example 9.5.4: the open diagonal answer follows from the original P
    in every ordinary structure and at every assignment (SQ37, SQ40). -/
@[blueprint "chap9__example_9_5_4"]
theorem exIndefiniteAnswerValidity :
    programConsequence exOriginalProgram
      (.disj (.neg (mkCorrAtom .rocksinger (.var 22)).toFormula)
        (mkCorrAtom .rich (.var 22)).toFormula)

/-- The four displayed completed traces, projected to original outputs
    (Y,Z). Each pair retains the initial negative clause and the answer
    pattern; auxiliary variables are observed only through those outputs. -/
@[blueprint "chap9__example_9_5_4"]
noncomputable def exDisplayedAnswers :
    List (FOHornClause exCorrectnessLang exCorrectnessLang_noEq ×
      (Term exCorrectnessLang × Term exCorrectnessLang)) :=
  [(exCorrectnessGoalClause1, (exRefutation_i.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_i.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause1, (exRefutation_ii.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_ii.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause2, (exRefutation_iii.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_iii.resultSubstitution exCorrectnessLang_noEq 1)),
   (exCorrectnessGoalClause2, (exRefutation_iv.resultSubstitution exCorrectnessLang_noEq 2,
      exRefutation_iv.resultSubstitution exCorrectnessLang_noEq 1))]

/-- Example 9.5.4 has four distinct displayed-policy answer patterns, two
    for each negative goal. SQ40 counts these projected patterns, modulo
    fresh auxiliary renaming, rather than every raw refutation. -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exDisplayedRefutation_answerClasses :
    exDisplayedAnswers =
      [(exCorrectnessGoalClause1, (.const .jean, .var 1)),
       (exCorrectnessGoalClause1, (.const .susan, .var 1)),
       (exCorrectnessGoalClause2, (.var 2, .const .jackson)),
       (exCorrectnessGoalClause2, (.var 22, .var 22))] ∧
    (exDisplayedAnswers.map Prod.snd).Nodup ∧
    exDisplayedAnswers.length = 4 ∧
    (exDisplayedAnswers.take 2).map Prod.fst = [exCorrectnessGoalClause1, exCorrectnessGoalClause1] ∧
    (exDisplayedAnswers.drop 2).map Prod.fst = [exCorrectnessGoalClause2, exCorrectnessGoalClause2]

/-- The open answer matrix ¬rocksinger(Y) ∨ rich(Z) of Example 9.5.4. -/
@[blueprint "chap9__example_9_5_4"]
def exAnswerMatrix (y z : Term exCorrectnessLang) : FormulaN exCorrectnessLang :=
  .disj (.neg (mkCorrAtom .rocksinger y).toFormula) (mkCorrAtom .rich z).toFormula

/-- The first three displayed cases have independent free coordinates:
    (jean,t), (susan,t), and (t,jackson), for every ambient ground t. -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exAnswer_groundCoordinateCases (t : GroundTerm exCorrectnessLang) :
    programConsequence exOriginalProgram (exAnswerMatrix (.const .jean) t.val) ∧
    programConsequence exOriginalProgram (exAnswerMatrix (.const .susan) t.val) ∧
    programConsequence exOriginalProgram (exAnswerMatrix t.val (.const .jackson))

/-- The fourth displayed answer uses one common finite η on the residual
    variable Y₁, hence both output coordinates are the same ground term.
    It is valid over the original P (SQ37, SQ39, SQ40). -/
@[attach_debt, blueprint "chap9__example_9_5_4"]
theorem exAnswer_diagonalCase (eta : Nat → Term exCorrectnessLang)
    (hFinite : ∃ support : List Nat, ∀ v, v ∉ support → eta v = .var v)
    (hGround : Term.isClosed (eta 22)) :
    programConsequence exOriginalProgram
      (exAnswerMatrix (termSubstAll (exIndefiniteAnswer 2) eta)
        (termSubstAll (exIndefiniteAnswer 1) eta)) ∧
    termSubstAll (exIndefiniteAnswer 2) eta = eta 22 ∧
    termSubstAll (exIndefiniteAnswer 1) eta = eta 22

end LCS.SLD.LogicProgramming.Correctness
end
