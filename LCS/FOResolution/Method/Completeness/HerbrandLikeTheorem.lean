import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import Attach
import LCS.FOResolution.Method.Completeness.HerbrandLikeTheorem.ProofsStamp

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical
namespace Formula

/-- Theorem 8.5.2 (companion): Predicate that a formula is in prenex
    form: all quantifiers appear at the front, preceding the
    quantifier-free matrix. -/
@[blueprint "chap8__theorem_8_5_2"]
def isPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => Formula.isPrenex A
  | .ex _ A => Formula.isPrenex A
  | A => ¬ (∃ i B, A = FormulaN.all i B ∨ A = FormulaN.ex i B) ∧
         formulaQuantifierFree A
where
  /-- A formula is quantifier-free if it contains no quantifiers. -/
  formulaQuantifierFree {L : Language} : FormulaN L → Prop
    | .predN _ _ => True
    | .eq_ _ _ _ => True
    | .neg A => formulaQuantifierFree A
    | .conj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .disj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .impl A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .all _ _ => False
    | .ex _ _ => False

/-- Theorem 8.5.2 (companion): Canonical wrapper for the clause-form
    module's predicate that strips a leading quantifier prefix and
    requires the remaining matrix to be in conjunctive normal form. -/
@[blueprint "chap8__theorem_8_5_2"]
def matrixIsCNF {L : Language} (A : FormulaN L) : Prop :=
  LCS.FOResolution.ClauseForm.Formula.matrixIsCNF A

end Formula

namespace FOClauseForm

/-- Convert a proof-certified disjunction of literals into a clause.
    Invalid formula shapes have no fallback branch: their certification
    hypotheses are contradictory. -/
noncomputable def clauseOfDisj {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (hDisj :
      LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals A) :
    FOClause L hNoEq := by
  induction A with
  | predN P args => exact [.pos (.predN P args)]
  | eq_ hL lhs rhs => exact [.pos (.eq_ hL lhs rhs)]
  | neg B _ =>
      cases B with
      | predN P args => exact [.neg (.predN P args)]
      | eq_ hL lhs rhs => exact [.neg (.eq_ hL lhs rhs)]
      | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
          simp [LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals,
            LCS.FOResolution.ClauseForm.Formula.isClauseLiteral] at hDisj
  | disj B C ihB ihC => exact ihB hDisj.1 ++ ihC hDisj.2
  | conj _ _ _ _
  | impl _ _ _ _
  | all _ _ _
  | ex _ _ _ =>
      simp [LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals,
        LCS.FOResolution.ClauseForm.Formula.isClauseLiteral] at hDisj

/-- Flatten a proof-certified CNF matrix into its clauses. -/
noncomputable def ofCNFMatrix {L : Language} (hNoEq : L.withoutEquality) :
    (A : FormulaN L) →
      LCS.FOResolution.ClauseForm.Formula.isCNFMatrix A →
      FOClauseForm L hNoEq
  | .conj A B, hCNF =>
      (ofCNFMatrix (hNoEq := by all_goals exact hNoEq)) A hCNF.1 ++ (ofCNFMatrix (hNoEq := by all_goals exact hNoEq)) B hCNF.2
  | .predN P args, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.predN P args) hCNF]
  | .eq_ hL lhs rhs, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.eq_ hL lhs rhs) hCNF]
  | .neg A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.neg A) hCNF]
  | .disj A B, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.disj A B) hCNF]
  | .impl A B, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.impl A B) hCNF]
  | .all i A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.all i A) hCNF]
  | .ex i A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.ex i A) hCNF]

/-- Theorem 8.5.2 (companion): clauses extracted from the actual Skolem
    form of A in its canonical fresh-signature extension. The specification
    has source A itself. Only the universal prefix of its Skolem form is
    stripped, and the remaining CNF matrix is flattened by the certified
    structural extractor. -/
@[blueprint "chap8__theorem_8_5_2"]
def ofFormula {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (clauses : FOClauseForm spec.language hNoEq) : Prop :=
  spec.source = A ∧
    ∃ hCNF : LCS.FOResolution.ClauseForm.Formula.isCNFMatrix
        (LCS.FOResolution.ClauseForm.Formula.stripAllPrenex
          (LCS.Herbrand.SHGTheorem.skolemForm spec)).2,
      clauses = ofCNFMatrix (L := spec.language) hNoEq
        (LCS.FOResolution.ClauseForm.Formula.stripAllPrenex
          (LCS.Herbrand.SHGTheorem.skolemForm spec)).2 hCNF

end FOClauseForm

/-- Theorem 8.5.2: a supplied LK proof of A ⇒ ∅, for a rectified
    prenex sentence A with CNF matrix, yields a resolution refutation of
    its actual Skolem clauses in the fresh Skolem signature. This states
    existence; the uniform executable proof-to-refutation converter is
    deferred under OD-A17. -/
@[attach_debt, blueprint "chap8__theorem_8_5_2" (main := true)]
theorem herbrand_resolution {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (hPrenex : Formula.isPrenex A)
    (hCNF : Formula.matrixIsCNF A)
    (hSent : formulaFVN A = ∅)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A)
    (proof : FOLKProofTree (Sequent.mk [A] [])) :
    ∃ (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
      (clauses : FOClauseForm spec.language hNoEq)
      (D : FOResolutionDAG spec.language hNoEq),
      FOClauseForm.ofFormula hNoEq A spec clauses ∧
      @FOResolutionDAG.isResolutionRefutation spec.language hNoEq
        (fun _ _ => Classical.propDecidable _) D (fun c => c ∈ clauses)

end LCS.FOResolution.Method.Completeness
end
