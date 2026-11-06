import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.FreshVariables
import LCS.CutElim.Interpolation.ProofSubstitution.Variable
import LCS.CutElim.Interpolation.ProofSubstitution.Constant
import Attach
import LCS.CutElim.Interpolation.ProofSubstitution.ProofsStamp

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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

/-- A variable is not bound in any node sequent or rule annotation of an LKₑ deduction tree. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LKe.LKeDeductionTree.notBoundIn {L : Language} :
    {s : Sequent L} → LKeDeductionTree s → Nat → Prop
  | s, .leaf _, y => sequentNotBoundIn s y
  | _, .eqAxiom hL ax, y => sequentNotBoundIn (ax.toSequent hL) y
  | _, .onePremise rule t, y => rule.notBoundIn y ∧ t.notBoundIn y
  | _, .twoPremise rule t₁ t₂, y =>
      rule.notBoundIn y ∧ t₁.notBoundIn y ∧ t₂.notBoundIn y

/-- A variable occurs in no node sequent or rule annotation of an LKₑ deduction tree. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LKe.LKeDeductionTree.varNotOccurs {L : Language} :
    {s : Sequent L} → LKeDeductionTree s → Nat → Prop
  | s, .leaf _, z => sequentVarNotOccurs s z
  | _, .eqAxiom hL ax, z => sequentVarNotOccurs (ax.toSequent hL) z
  | _, .onePremise rule t, z => rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t₁ t₂, z =>
      rule.varNotOccurs z ∧ t₁.varNotOccurs z ∧ t₂.varNotOccurs z

/-- Substitute z for y throughout an LKₑ deduction tree, including arbitrary
leaf sequents and equality axioms; eigenvariables equal to y become z. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LKe.LKeDeductionTree.substVar {L : Language} {s : Sequent L}
    (T : LKeDeductionTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LKeDeductionTree (sequentSubstVar s z y) := by
  exact match T with
  | .leaf q => .leaf (sequentSubstVar q z y)
  | .eqAxiom hL ax => by
    cases ax with
    | refl t =>
      simpa [sequentSubstVar, LKeEqualityAxiom.toSequent,
        formulaSubstN] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.refl (termSubst t (.var z) y)))
    | funcCong f ss ts =>
      simpa [sequentSubstVar, LKeEqualityAxiom.toSequent,
        formulaSubstN, termSubst, List.map_map, Function.comp_def] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.funcCong f
              (fun i => termSubst (ss i) (.var z) y)
              (fun i => termSubst (ts i) (.var z) y)))
    | predCong P ss ts =>
      simpa [sequentSubstVar, LKeEqualityAxiom.toSequent,
        formulaSubstN, List.map_map, Function.comp_def] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.predCong P
              (fun i => termSubst (ss i) (.var z) y)
              (fun i => termSubst (ts i) (.var z) y)))
    | eqCong s₁ s₂ t₁ t₂ =>
      simpa [sequentSubstVar, LKeEqualityAxiom.toSequent,
        formulaSubstN] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.eqCong
              (termSubst s₁ (.var z) y)
              (termSubst s₂ (.var z) y)
              (termSubst t₁ (.var z) y)
              (termSubst t₂ (.var z) y)))
  | .onePremise rule t => by
    simp only [LKeDeductionTree.notBoundIn] at hNotBound
    simp only [LKeDeductionTree.varNotOccurs] at hNotOccurs
    exact LKeDeductionTree.onePremise
      (folkStep1SubstVar rule z y hNotBound.1 hNotOccurs.1)
      (LCS.CutElim.LKe.LKeDeductionTree.substVar t z y hNotBound.2 hNotOccurs.2)
  | .twoPremise rule t₁ t₂ => by
    simp only [LKeDeductionTree.notBoundIn] at hNotBound
    simp only [LKeDeductionTree.varNotOccurs] at hNotOccurs
    exact LKeDeductionTree.twoPremise
      (folkStep2SubstVar rule z y)
      (LCS.CutElim.LKe.LKeDeductionTree.substVar t₁ z y hNotBound.2.1 hNotOccurs.2.1)
      (LCS.CutElim.LKe.LKeDeductionTree.substVar t₂ z y hNotBound.2.2 hNotOccurs.2.2)

/-- Substitute a fresh variable z for any constant c throughout an LKₑ
deduction tree, including arbitrary leaves and every rule annotation. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def _root_.LCS.CutElim.LKe.LKeDeductionTree.substConst {L : Language} {s : Sequent L}
    (T : LKeDeductionTree s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LKeDeductionTree (sequentSubstConst s z c) := by
  let rec transform {q : Sequent L}
      (U : LKeDeductionTree q) (hNO : U.varNotOccurs z) :
      LKeDeductionTree (sequentSubstConst q z c) :=
    match U with
  | .leaf q => .leaf (sequentSubstConst q z c)
  | .eqAxiom hL ax => by
    cases ax with
    | refl t =>
      simpa [sequentSubstConst, LKeEqualityAxiom.toSequent,
        formulaSubstConst] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.refl (termSubstConst t z c)))
    | funcCong f ss ts =>
      simpa [sequentSubstConst, LKeEqualityAxiom.toSequent,
        formulaSubstConst, termSubstConst, List.map_map,
        Function.comp_def] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.funcCong f
              (fun i => termSubstConst (ss i) z c)
              (fun i => termSubstConst (ts i) z c)))
    | predCong P ss ts =>
      simpa [sequentSubstConst, LKeEqualityAxiom.toSequent,
        formulaSubstConst, List.map_map, Function.comp_def] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.predCong P
              (fun i => termSubstConst (ss i) z c)
              (fun i => termSubstConst (ts i) z c)))
    | eqCong s₁ s₂ t₁ t₂ =>
      simpa [sequentSubstConst, LKeEqualityAxiom.toSequent,
        formulaSubstConst] using
          (LKeDeductionTree.eqAxiom hL
            (LKeEqualityAxiom.eqCong
              (termSubstConst s₁ z c)
              (termSubstConst s₂ z c)
              (termSubstConst t₁ z c)
              (termSubstConst t₂ z c)))
  | .onePremise rule t => by
    simp only [LKeDeductionTree.varNotOccurs] at hNO
    exact LKeDeductionTree.onePremise
      (folkStep1SubstConst rule z c hNO.1)
      (transform t hNO.2)
  | .twoPremise rule t₁ t₂ => by
    simp only [LKeDeductionTree.varNotOccurs] at hNO
    exact LKeDeductionTree.twoPremise
      (folkStep2SubstConst rule z c)
      (transform t₁ hNO.2.1)
      (transform t₂ hNO.2.2)
  exact transform T hNotOccurs

/-- Variable substitution preserves the `isProof` predicate on LKₑ deduction trees. -/
theorem _root_.LCS.CutElim.LKe.LKeDeductionTree.substVar_isProof
    {L : Language} {s : Sequent L} (T : LKeDeductionTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    (T.substVar z y hNotBound hNotOccurs).isProof := by
  -- REPAIR(T6-42b): proof pending
  sorry

/-- Constant substitution preserves the `isProof` predicate on LKₑ deduction trees. -/
theorem _root_.LCS.CutElim.LKe.LKeDeductionTree.substConst_isProof
    {L : Language} {s : Sequent L} (T : LKeDeductionTree s) (z : Nat)
    (c : L.constSymbols) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    (T.substConst z c hNotOccurs).isProof := by
  -- REPAIR(T6-42b): proof pending
  sorry

/-- Lemma 6.5.1: Substitution preserves being a proof. For LK over a
language without equality, and for LKₑ over a language with equality,
a deduction tree satisfying `isProof` still satisfies `isProof` after
substituting a fresh variable z for a variable y not bound in the tree,
or for any constant c. The resulting trees are indexed by the corresponding
substituted end-sequents. -/
@[blueprint "chap6__lemma_6_5_1" (main := true)]
theorem folkProofSubst_6_5_1 {L : Language} :
    ((∀ (hL : L.withoutEquality) {s : Sequent L} (T : FOLKDeductionTree hL s)
        (_hp : T.isProof) (y z : Nat) (hNB : T.notBoundIn y) (hNO : T.varNotOccurs z),
        (T.substVar z y hNB hNO).isProof) ∧
      (∀ (hL : L.withoutEquality) {s : Sequent L} (T : FOLKDeductionTree hL s)
        (_hp : T.isProof) (z : Nat) (hNO : T.varNotOccurs z) (c : L.constSymbols),
        (T.substConst z c hNO).isProof)) ∧
    ((∀ (_hEq : L.hasEquality = true) {s : Sequent L} (T : LKeDeductionTree s)
        (_hp : T.isProof) (y z : Nat) (hNB : T.notBoundIn y) (hNO : T.varNotOccurs z),
        (T.substVar z y hNB hNO).isProof) ∧
      (∀ (_hEq : L.hasEquality = true) {s : Sequent L} (T : LKeDeductionTree s)
        (_hp : T.isProof) (z : Nat) (hNO : T.varNotOccurs z) (c : L.constSymbols),
        (T.substConst z c hNO).isProof)) 

end LCS.CutElim.Interpolation
end
