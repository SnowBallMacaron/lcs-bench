import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import Attach
import LCS.CutElim.Interpolation.VariableSubstitution.ProofsStamp

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

/-- Variable substitution T[z/y] on LK deduction trees. Every node sequent
and rule annotation is substituted, including arbitrary leaf sequents.
If a quantifier rule's eigenvariable is y, its new eigenvariable is z.
The source variable is not bound in the tree and the target variable is fresh. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.substVar {L : Language}
    {hL : L.withoutEquality} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstVar s z y) := by
  exact transform T z y hNotBound hNotOccurs
where
  transform {L : Language}
      {hL : L.withoutEquality} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z y : Nat)
      (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstVar s z y) := by
    have termSubstVarEqOfNotFree :
        ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree :
        ∀ F : FormulaN L, y ∉ formulaFVN F →
          formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉
          formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++
            (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    exact match T with
    | .leaf q => FOLKDeductionTree.leaf (sequentSubstVar q z y)
    | .onePremise rule t => by
      simp only [FOLKDeductionTree.notBoundIn] at hNotBound
      simp only [FOLKDeductionTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨hRuleNB, hTreeNB⟩
      rcases hNotOccurs with ⟨hRuleNO, hTreeNO⟩
      have transformedTree :=
        transform t z y hTreeNB hTreeNO
      exact dedVar_oneRule L hL z y sequentFreshAfterSubst _ _ rule hRuleNB hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKDeductionTree.notBoundIn] at hNotBound
      simp only [FOLKDeductionTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨_, hTree₁NB, hTree₂NB⟩
      rcases hNotOccurs with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ :=
        transform t₁ z y hTree₁NB hTree₁NO
      have transformedTree₂ :=
        transform t₂ z y hTree₂NB hTree₂NO
      exact dedVar_twoRule L hL z y _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural T

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Passing from a deduction tree to its proof tree preserves bound-variable exclusion. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.notBoundIn_toProofTree
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (hp : T.isProof) (v : Nat) :
    (T.toProofTree hp).notBoundIn v ↔ T.notBoundIn v := by
  induction T with
  | leaf q => rfl
  | onePremise rule t ih =>
    exact and_congr Iff.rfl (ih hp)
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    exact and_congr Iff.rfl (and_congr (ih₁ hp.1) (ih₂ hp.2))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Passing from a deduction tree to its proof tree preserves variable freshness. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.varNotOccurs_toProofTree
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (hp : T.isProof) (v : Nat) :
    (T.toProofTree hp).varNotOccurs v ↔ T.varNotOccurs v := by
  induction T with
  | leaf q => rfl
  | onePremise rule t ih =>
    exact and_congr Iff.rfl (ih hp)
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    exact and_congr Iff.rfl (and_congr (ih₁ hp.1) (ih₂ hp.2))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- On proof trees, deduction-tree substitution has exactly the proof-tree
image given by `folkProofSubstVar`. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.substVar_proof_image
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    ∃ hp' : (T.substVar z y hNotBound hNotOccurs).isProof,
      (T.substVar z y hNotBound hNotOccurs).toProofTree hp' =
        folkProofSubstVar (T.toProofTree hp) z y
          ((T.notBoundIn_toProofTree hp y).mpr hNotBound)
          ((T.varNotOccurs_toProofTree hp z).mpr hNotOccurs) := by
  -- REPAIR(T6-41a): proof pending
  sorry

end LCS.CutElim.Interpolation
end

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
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (hL : L.withoutEquality) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_allLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL
      (sequentSubstConst (Sequent.mk (formulaSubstN A t₀ x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.allLeft t₀ x
      A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.allLeft
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_allRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e)
      x A) (transformedTree : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A
      (Term.var e) x])) z c)) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++
            [formulaSubstN (formulaSubstConst A z c) (.var e) x])) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.allRight e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_exLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x
      A) (transformedTree : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e)
      x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (.var e) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exLeft e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_exRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL
      (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t₀ x])) z c)) (hRuleNO : (FOLKStep1.exRight t₀
      x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++ [formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x])) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exRight
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_oneRule
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (q :
      Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem q) (hRuleNO : rule.varNotOccurs z) (transformedTree
      : FOLKDeductionTree hL (sequentSubstConst prem z c))
    : FOLKDeductionTree hL (sequentSubstConst q z c) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.orRightL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.orRightR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise (FOLKStep1.implRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.negLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.onePremise
        (FOLKStep1.negRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact dedConst_allLeft L hL z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact dedConst_allRight L hL z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact dedConst_exLeft L hL z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact dedConst_exRight L hL z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def dedConst_twoRule
    (q : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 q) (transformedTree₁
      : FOLKDeductionTree hL (sequentSubstConst prem1 z c)) (transformedTree₂ : FOLKDeductionTree hL
      (sequentSubstConst prem2 z c))
    : FOLKDeductionTree hL (sequentSubstConst q z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.cut (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKDeductionTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)

end
end LCS.CutElim.Interpolation
end

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

/-- Constant substitution T[z/c] on LK deduction trees. For any constant c
and a variable z fresh in T, substitute in every leaf sequent and every rule
annotation, retaining the tree's inference structure. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def _root_.LCS.CutElim.LK.FOLKDeductionTree.substConst
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst s z c) := by
  exact prepare T z c hNotOccurs
where
  prepare
      {L : Language} {hL : L.withoutEquality} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
      (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst s z c) := by
    have termComm (u t : Term L) (x : Nat) (hzx : z ≠ x) :
        termSubstConst (termSubst u t x) z c =
          termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
      exact folkConst_termComm L z c u _ x hzx
    have formulaComm (A : FormulaN L) (t : Term L) (x : Nat)
        (hzx : z ≠ x) :
        formulaSubstConst (formulaSubstN A t x) z c =
          formulaSubstN (formulaSubstConst A z c)
            (termSubstConst t z c) x := by
      exact folkConst_formulaComm L z c termComm A t x hzx
    have termFreshAfterConst (t : Term L) (v : Nat) (hvz : v ≠ z)
        (h : v ∉ termFV t) :
        v ∉ termFV (termSubstConst t z c) := by
      exact folkConst_termFreshAfterConst L z c t _ hvz h
    have freeAfterConst (A : FormulaN L) (t : Term L) (x : Nat)
        (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A) :
        isFreeForN (termSubstConst t z c) x
          (formulaSubstConst A z c) := by
      exact folkConst_freeAfterConst L z c termFreshAfterConst A t _ hfree hNoZ
    have formulaFreshAfterConst (A : FormulaN L) (v : Nat)
        (hvz : v ≠ z) (h : v ∉ formulaFVN A) :
        v ∉ formulaFVN (formulaSubstConst A z c) := by
      exact folkConst_formulaFreshAfterConst L z c termFreshAfterConst A v hvz h
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++
            (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      exact folkConst_sequentFreshAfterConst L z c formulaFreshAfterConst q e he hez
    exact transform z c formulaComm freeAfterConst sequentFreshAfterConst T hNotOccurs

  transform {L : Language} {hL : L.withoutEquality} (z : Nat) (c : L.constSymbols)
      (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x), formulaSubstConst (formulaSubstN
        A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A
        : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A), isFreeForN
        (termSubstConst t z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e :
        Nat) (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F) (hez : e ≠ z), ∀ F ∈
        (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent, e ∉ formulaFVN F)
      {q : Sequent L}
      (U : LCS.CutElim.LK.FOLKDeductionTree hL q) (hNO : U.varNotOccurs z) :
      LCS.CutElim.LK.FOLKDeductionTree hL (sequentSubstConst q z c) :=
    match U with
    | .leaf q => FOLKDeductionTree.leaf (sequentSubstConst q z c)
    | .onePremise rule t => by
      simp only [FOLKDeductionTree.varNotOccurs] at hNO
      rcases hNO with ⟨hRuleNO, hTreeNO⟩
      have transformedTree := transform z c formulaComm freeAfterConst sequentFreshAfterConst t hTreeNO
      exact dedConst_oneRule L hL z c formulaComm freeAfterConst sequentFreshAfterConst _ _ rule hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKDeductionTree.varNotOccurs] at hNO
      rcases hNO with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₁ hTree₁NO
      have transformedTree₂ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₂ hTree₂NO
      exact dedConst_twoRule L hL z c _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural U

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Deduction-tree constant substitution preserves proof trees, and its
proof-tree image is `folkProofSubstConst`. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.substConst_proof_image
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    ∃ hp' : (T.substConst z c hNotOccurs).isProof,
      (T.substConst z c hNotOccurs).toProofTree hp' =
        folkProofSubstConst (T.toProofTree hp) z c
          ((T.varNotOccurs_toProofTree hp z).mpr hNotOccurs) := by
  -- REPAIR(T6-41b): proof pending
  sorry



-- isFreeForN always holds for constant terms (no free variables to capture).
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem isFreeFor_const {L : Language} (c : L.constSymbols) (x : Nat) (A : FormulaN L) :
    isFreeForN (.const c) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ => exact trivial
  | conj A B ihA ihB => exact ⟨ihA, ihB⟩
  | disj A B ihA ihB => exact ⟨ihA, ihB⟩
  | impl A B ihA ihB => exact ⟨ihA, ihB⟩
  | neg A ih => exact ih
  | all y A ih => exact Or.inr ⟨fun h => absurd h id, ih⟩
  | ex y A ih => exact Or.inr ⟨fun h => absurd h id, ih⟩

-- Substitution symbol preservation lemmas

-- retained: used by LCS.CutElim.Interpolation.KeyLemma, LCS.CutElim.Interpolation.QuantifierCases, LCS.CutElim.Interpolation.RuleSubstitution
theorem termConstSymbols_termSubst {L : Language}
    (t' t : Term L) (x : Nat) :
    ∀ c, termConstSymbols (termSubst t' t x) c →
      termConstSymbols t' c ∨ termConstSymbols t c := by
-- BEGIN PROOF
  induction t' with
  | var y =>
    intro c hc
    simp only [termSubst] at hc
    split at hc
    · exact Or.inr hc
    · exact absurd hc id
  | const d =>
    intro c hc
    simp only [termSubst, termConstSymbols] at hc ⊢
    exact Or.inl hc
  | func f ts ih =>
    intro c hc
    simp only [termSubst, termConstSymbols] at hc ⊢
    obtain ⟨i, hi⟩ := hc
    rcases ih i c hi with h | h
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h

-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem termConstSymbols_termSubstConst {L : Language}
    (t : Term L) (z : Nat) (c d : L.constSymbols) :
    termConstSymbols (termSubstConst t z c) d →
    termConstSymbols t d ∧ d ≠ c := by
  induction t with
  | var _ =>
    simp only [termSubstConst]
    intro h; exact absurd h id
  | const e =>
    intro h
    simp only [termSubstConst] at h
    split at h
    · exact absurd h id
    · rename_i hne
      exact ⟨h, fun heq => by
        have : d = e := h
        rw [this] at heq; exact hne heq⟩
  | func f ts ih =>
    intro h
    simp only [termSubstConst, termConstSymbols] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact let ⟨h1, h2⟩ := ih i hi; ⟨⟨i, h1⟩, h2⟩

-- retained: used by LCS.CutElim.Interpolation.KeyLemma, LCS.CutElim.Interpolation.QuantifierCases, LCS.CutElim.Interpolation.RuleSubstitution
theorem formulaConstSymbolsN_formulaSubst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    ∀ c, formulaConstSymbolsN (formulaSubstN A t x) c →
      formulaConstSymbolsN A c ∨ termConstSymbols t c := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro c hc
    simp only [formulaSubstN, formulaConstSymbolsN] at hc ⊢
    obtain ⟨i, hi⟩ := hc
    rcases termConstSymbols_termSubst (ts i) t x c hi with h | h
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h
  | eq_ _ t1 t2 =>
    intro c hc
    simp only [formulaSubstN, formulaConstSymbolsN] at hc ⊢
    rcases hc with h | h
    · rcases termConstSymbols_termSubst t1 t x c h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases termConstSymbols_termSubst t2 t x c h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | conj A B ihA ihB =>
    intro c hc
    simp only [formulaSubstN, formulaConstSymbolsN] at hc ⊢
    rcases hc with hA | hB
    · rcases ihA c hA with h | h; exact Or.inl (Or.inl h); exact Or.inr h
    · rcases ihB c hB with h | h; exact Or.inl (Or.inr h); exact Or.inr h
  | disj A B ihA ihB =>
    intro c hc
    simp only [formulaSubstN, formulaConstSymbolsN] at hc ⊢
    rcases hc with hA | hB
    · rcases ihA c hA with h | h; exact Or.inl (Or.inl h); exact Or.inr h
    · rcases ihB c hB with h | h; exact Or.inl (Or.inr h); exact Or.inr h
  | impl A B ihA ihB =>
    intro c hc
    simp only [formulaSubstN, formulaConstSymbolsN] at hc ⊢
    rcases hc with hA | hB
    · rcases ihA c hA with h | h; exact Or.inl (Or.inl h); exact Or.inr h
    · rcases ihB c hB with h | h; exact Or.inl (Or.inr h); exact Or.inr h
  | neg A ih =>
    intro c hc; exact ih c hc
  | all y A ih =>
    intro c hc
    simp only [formulaSubstN] at hc
    split at hc
    · exact ih c hc
    · exact Or.inl hc
  | ex y A ih =>
    intro c hc
    simp only [formulaSubstN] at hc
    split at hc
    · exact ih c hc
    · exact Or.inl hc

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
theorem termFV_termSubst {L : Language}
    (t' t : Term L) (x : Nat) :
    ∀ v, termFV (termSubst t' t x) v →
      (termFV t' v ∧ v ≠ x) ∨ termFV t v := by
-- BEGIN PROOF
  induction t' with
  | var y =>
    intro v hv
    simp only [termSubst] at hv
    split at hv
    · exact Or.inr hv
    · exact Or.inl ⟨hv, by rename_i hne; intro heq; rw [hv] at heq; exact hne heq⟩
  | const _ =>
    intro v hv; simp only [termSubst, termFV] at hv; exact hv.elim
  | func f ts ih =>
    intro v hv
    simp only [termSubst, termFV] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    rcases ih i v hi with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨⟨i, h1⟩, h2⟩
    · exact Or.inr h

-- retained: used by LCS.CutElim.Interpolation.KeyLemma, LCS.CutElim.Interpolation.QuantifierCases, LCS.CutElim.Interpolation.RuleSubstitution
theorem formulaFV_formulaSubst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    ∀ v, formulaFVN (formulaSubstN A t x) v →
      (formulaFVN A v ∧ v ≠ x) ∨ termFV t v := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro v hv
    simp only [formulaSubstN, formulaFVN] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    rcases termFV_termSubst (ts i) t x v hi with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨⟨i, h1⟩, h2⟩
    · exact Or.inr h
  | eq_ _ t1 t2 =>
    intro v hv
    simp only [formulaSubstN, formulaFVN] at hv ⊢
    rcases hv with h | h
    · rcases termFV_termSubst t1 t x v h with ⟨h1, h2⟩ | h'
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr h'
    · rcases termFV_termSubst t2 t x v h with ⟨h1, h2⟩ | h'
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr h'
  | conj A B ihA ihB =>
    intro v hv
    simp only [formulaSubstN, formulaFVN] at hv
    rcases hv with hA | hB
    · rcases ihA v hA with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inl h1, h2⟩; exact Or.inr h
    · rcases ihB v hB with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inr h1, h2⟩; exact Or.inr h
  | disj A B ihA ihB =>
    intro v hv
    simp only [formulaSubstN, formulaFVN] at hv
    rcases hv with hA | hB
    · rcases ihA v hA with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inl h1, h2⟩; exact Or.inr h
    · rcases ihB v hB with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inr h1, h2⟩; exact Or.inr h
  | impl A B ihA ihB =>
    intro v hv
    simp only [formulaSubstN, formulaFVN] at hv
    rcases hv with hA | hB
    · rcases ihA v hA with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inl h1, h2⟩; exact Or.inr h
    · rcases ihB v hB with ⟨h1, h2⟩ | h; exact Or.inl ⟨Or.inr h1, h2⟩; exact Or.inr h
  | neg A ih => exact ih
  | all y A ih =>
    intro v hv
    simp only [formulaSubstN] at hv
    split at hv
    · have hv1 : formulaFVN (formulaSubstN A t x) v := by simp only [formulaFVN] at hv; exact hv.1
      have hv2 : v ≠ y := by simp only [formulaFVN] at hv; exact hv.2
      rcases ih v hv1 with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by simp only [formulaFVN]; exact ⟨h1, hv2⟩, h2⟩
      · exact Or.inr h
    · rename_i hne
      have hxy : x = y := by simp [bne, beq_iff_eq] at hne; exact hne
      exact Or.inl ⟨hv, by intro heq; simp only [formulaFVN] at hv; exact hv.2 (hxy ▸ heq)⟩
  | ex y A ih =>
    intro v hv
    simp only [formulaSubstN] at hv
    split at hv
    · have hv1 : formulaFVN (formulaSubstN A t x) v := by simp only [formulaFVN] at hv; exact hv.1
      have hv2 : v ≠ y := by simp only [formulaFVN] at hv; exact hv.2
      rcases ih v hv1 with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by simp only [formulaFVN]; exact ⟨h1, hv2⟩, h2⟩
      · exact Or.inr h
    · rename_i hne
      have hxy : x = y := by simp [bne, beq_iff_eq] at hne; exact hne
      exact Or.inl ⟨hv, by intro heq; simp only [formulaFVN] at hv; exact hv.2 (hxy ▸ heq)⟩

-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem formulaFV_formulaSubstConst_sub {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) (v : Nat) :
    formulaFVN (formulaSubstConst A z c) v →
    formulaFVN A v ∨ v = z := by
-- BEGIN PROOF
  intro h
  by_cases hA : formulaFVN A v
  · exact Or.inl hA
  · by_cases hz : v = z
    · exact Or.inr hz
    · exact absurd h (formulaFV_formulaSubstConst A z c v hz hA)

-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem formulaPredSymbolsN_formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) :
    formulaPredSymbolsN (formulaSubstConst A z c) = formulaPredSymbolsN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => simp [formulaSubstConst, formulaPredSymbolsN]
  | eq_ _ t1 t2 => simp [formulaSubstConst, formulaPredSymbolsN]
  | conj A B ihA ihB => simp [formulaSubstConst, formulaPredSymbolsN, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstConst, formulaPredSymbolsN, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstConst, formulaPredSymbolsN, ihA, ihB]
  | neg A ih => simp [formulaSubstConst, formulaPredSymbolsN, ih]
  | all x A ih => simp [formulaSubstConst, formulaPredSymbolsN, ih]
  | ex x A ih => simp [formulaSubstConst, formulaPredSymbolsN, ih]

-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem formulaConstSymbolsN_formulaSubstConst_ {L : Language}
    (A : FormulaN L) (z : Nat) (c d : L.constSymbols) :
    formulaConstSymbolsN (formulaSubstConst A z c) d →
    formulaConstSymbolsN A d ∧ d ≠ c := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro h; simp only [formulaSubstConst, formulaConstSymbolsN] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact let ⟨h1, h2⟩ := termConstSymbols_termSubstConst (ts i) z c d hi; ⟨⟨i, h1⟩, h2⟩
  | eq_ _ t1 t2 =>
    intro h; simp only [formulaSubstConst, formulaConstSymbolsN] at h ⊢
    rcases h with h | h
    · exact let ⟨h1, h2⟩ := termConstSymbols_termSubstConst t1 z c d h; ⟨Or.inl h1, h2⟩
    · exact let ⟨h1, h2⟩ := termConstSymbols_termSubstConst t2 z c d h; ⟨Or.inr h1, h2⟩
  | conj A B ihA ihB =>
    intro h; simp only [formulaSubstConst, formulaConstSymbolsN] at h ⊢
    rcases h with hA | hB
    · exact let ⟨h1, h2⟩ := ihA hA; ⟨Or.inl h1, h2⟩
    · exact let ⟨h1, h2⟩ := ihB hB; ⟨Or.inr h1, h2⟩
  | disj A B ihA ihB =>
    intro h; simp only [formulaSubstConst, formulaConstSymbolsN] at h ⊢
    rcases h with hA | hB
    · exact let ⟨h1, h2⟩ := ihA hA; ⟨Or.inl h1, h2⟩
    · exact let ⟨h1, h2⟩ := ihB hB; ⟨Or.inr h1, h2⟩
  | impl A B ihA ihB =>
    intro h; simp only [formulaSubstConst, formulaConstSymbolsN] at h ⊢
    rcases h with hA | hB
    · exact let ⟨h1, h2⟩ := ihA hA; ⟨Or.inl h1, h2⟩
    · exact let ⟨h1, h2⟩ := ihB hB; ⟨Or.inr h1, h2⟩
  | neg A ih => exact ih
  | all x A ih => exact ih
  | ex x A ih => exact ih

-- Remaining substitution helper lemmas





-- ===================================================================
-- Monotonicity helpers for symbol containment in interpolation
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.QuantifierCases
theorem listFormulaPredSymbols_mono {L : Language}
    {l l' : List (FormulaN L)} (h : ∀ A, A ∈ l → A ∈ l') :
    listFormulaPredSymbols l ⊆ listFormulaPredSymbols l' :=
-- BEGIN PROOF
  fun x ⟨A, hA, hP⟩ => ⟨A, h A hA, hP⟩

-- retained: used by LCS.CutElim.Interpolation.QuantifierCases
theorem listFormulaConstSymbols_mono {L : Language}
    {l l' : List (FormulaN L)} (h : ∀ A, A ∈ l → A ∈ l') :
    listFormulaConstSymbols l ⊆ listFormulaConstSymbols l' :=
-- BEGIN PROOF
  fun x ⟨A, hA, hC⟩ => ⟨A, h A hA, hC⟩

-- retained: used by LCS.CutElim.Interpolation.QuantifierCases
theorem listFormulaFV_mono {L : Language}
    {l l' : List (FormulaN L)} (h : ∀ A, A ∈ l → A ∈ l') :
    listFormulaFV l ⊆ listFormulaFV l' :=
-- BEGIN PROOF
  fun x ⟨A, hA, hV⟩ => ⟨A, h A hA, hV⟩

-- retained: used by LCS.CutElim.Interpolation.RuleSubstitution
theorem inter_mono_left {α : Type} {A B B' : Set α}
    (hBB' : B ⊆ B') : A ∩ B ⊆ A ∩ B' :=
-- BEGIN PROOF
  fun x hx => ⟨hx.1, hBB' x hx.2⟩

-- retained: used by LCS.CutElim.Interpolation.RuleSubstitution
theorem inter_mono_right {α : Type} {A A' B : Set α}
    (hAA' : A ⊆ A') : A ∩ B ⊆ A' ∩ B :=
-- BEGIN PROOF
  fun x hx => ⟨hAA' x hx.1, hx.2⟩

end LCS.CutElim.Interpolation
end

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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_axiom_id (X : FormulaN L) :
    lkBotProvable botP hBotArity { antecedent := [X], succedent := [X] } :=
-- BEGIN PROOF
  ⟨.axiom_ ⟨[X], [X]⟩ (Or.inl ⟨X, rfl, rfl⟩)⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_onePremise {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc)
    (h : lkBotProvable botP hBotArity prem) :
    lkBotProvable botP hBotArity conc := by
  obtain ⟨t⟩ := h; exact ⟨.onePremise rule t⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_twoPremise {p1 p2 conc : Sequent L}
    (rule : FOLKStep2 p1 p2 conc)
    (h1 : lkBotProvable botP hBotArity p1) (h2 : lkBotProvable botP hBotArity p2) :
    lkBotProvable botP hBotArity conc := by
  obtain ⟨t1⟩ := h1; obtain ⟨t2⟩ := h2; exact ⟨.twoPremise rule t1 t2⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_weakenLeft_list
    (Γ' Γ : List (FormulaN L)) (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ⟩) : lkBotProvable botP hBotArity ⟨Γ' ++ Γ, Δ⟩ := by
-- BEGIN PROOF
  induction Γ' with
  | nil => simpa using h
  | cons F rest ih =>
    exact lkBot_onePremise (.weakenLeft F (rest ++ Γ) Δ) ih
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_weakenRight_list
    (Γ : List (FormulaN L)) (Δ Δ' : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ⟩) : lkBotProvable botP hBotArity ⟨Γ, Δ ++ Δ'⟩ := by
-- BEGIN PROOF
  induction Δ' generalizing Δ with
  | nil => simp; exact h
  | cons F rest ih =>
    have h1 := lkBot_onePremise (.weakenRight F Γ Δ) h
    have h2 := ih (Δ ++ [F]) h1
    rwa [List.append_assoc] at h2
-- Other lkBot structural helpers
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_exchangeLeft_at
    (pfx : List (FormulaN L)) (A B : FormulaN L) (sfx : List (FormulaN L))
    (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨pfx ++ [A, B] ++ sfx, Δ⟩) :
    lkBotProvable botP hBotArity ⟨pfx ++ [B, A] ++ sfx, Δ⟩ :=
-- BEGIN PROOF
  lkBot_onePremise (.exchangeLeft pfx A B sfx Δ) h
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_sinkLeft
    (pfx : List (FormulaN L)) (A : FormulaN L) (mid sfx : List (FormulaN L))
    (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨pfx ++ [A] ++ mid ++ sfx, Δ⟩) :
    lkBotProvable botP hBotArity ⟨pfx ++ mid ++ [A] ++ sfx, Δ⟩ := by
-- BEGIN PROOF
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B rest ih =>
    have heq1 : pfx ++ [A] ++ (B :: rest) ++ sfx = pfx ++ [A, B] ++ (rest ++ sfx) := by
      simp [List.append_assoc, List.cons_append]
    have h1 := lkBot_exchangeLeft_at pfx A B (rest ++ sfx) Δ (heq1 ▸ h)
    have heq2 : pfx ++ [B, A] ++ (rest ++ sfx) = (pfx ++ [B]) ++ [A] ++ rest ++ sfx := by
      simp [List.append_assoc, List.cons_append]
    have h2 := ih (pfx ++ [B]) (heq2 ▸ h1)
    have heq3 : (pfx ++ [B]) ++ rest ++ [A] ++ sfx = pfx ++ (B :: rest) ++ [A] ++ sfx := by
      simp [List.append_assoc, List.cons_append]
    exact heq3 ▸ h2
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contractLeft_front
    (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨A :: A :: Γ, Δ⟩) :
    lkBotProvable botP hBotArity ⟨A :: Γ, Δ⟩ :=
-- BEGIN PROOF
  lkBot_onePremise (.contractLeft A Γ Δ) h
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_floatLeft_ante
    (pfx : List (FormulaN L)) (A : FormulaN L) (mid sfx : List (FormulaN L))
    (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨pfx ++ mid ++ [A] ++ sfx, Δ⟩) :
    lkBotProvable botP hBotArity ⟨pfx ++ [A] ++ mid ++ sfx, Δ⟩ := by
-- BEGIN PROOF
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B rest ih =>
    have h1 := ih (pfx ++ [B]) (by simp at h ⊢; exact h)
    have h2 := lkBot_exchangeLeft_at pfx B A (rest ++ sfx) Δ (by simp at h1 ⊢; exact h1)
    simp at h2 ⊢; exact h2
-- Contraction at arbitrary position in antecedent
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contractLeft_at
    (pfx : List (FormulaN L)) (A : FormulaN L) (sfx : List (FormulaN L))
    (Δ : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨pfx ++ [A, A] ++ sfx, Δ⟩) :
    lkBotProvable botP hBotArity ⟨pfx ++ [A] ++ sfx, Δ⟩ := by
-- BEGIN PROOF
  have step1 : lkBotProvable botP hBotArity ⟨[] ++ [A] ++ pfx ++ ([A] ++ sfx), Δ⟩ :=
    lkBot_floatLeft_ante [] A pfx ([A] ++ sfx) Δ (by simp at h ⊢; exact h)
  simp at step1
  have step2 : lkBotProvable botP hBotArity ⟨[A] ++ [A] ++ pfx ++ sfx, Δ⟩ :=
    lkBot_floatLeft_ante [A] A pfx sfx Δ (by simp at step1 ⊢; exact step1)
  simp at step2
  have step3 := lkBot_contractLeft_front A (pfx ++ sfx) Δ step2
  have step4 := lkBot_sinkLeft [] A pfx sfx Δ (by simp at step3 ⊢; exact step3)
  simp only [List.nil_append] at step4
  exact step4
-- Contract a suffix of the antecedent when all its elements appear in the prefix
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contract_suffix
    (Γ : List (FormulaN L)) (Γsuf : List (FormulaN L)) (Δ : List (FormulaN L))
    (hMem : ∀ x, x ∈ Γsuf → x ∈ Γ)
    (h : lkBotProvable botP hBotArity ⟨Γ ++ Γsuf, Δ⟩) :
    lkBotProvable botP hBotArity ⟨Γ, Δ⟩ := by
-- BEGIN PROOF
  induction Γsuf with
  | nil => simpa using h
  | cons x rest ih =>
    have hx : x ∈ Γ := hMem x (List.Mem.head _)
    obtain ⟨pre, post, hΓ⟩ := LCS.CutElim.LKe.Equivalence.perm_mem_split x Γ hx
    have h1 : lkBotProvable botP hBotArity ⟨pre ++ [x] ++ (post ++ [x] ++ rest), Δ⟩ := by
      rw [hΓ] at h; simp at h ⊢; exact h
    have h2 : lkBotProvable botP hBotArity ⟨(pre ++ [x]) ++ [x] ++ post ++ rest, Δ⟩ :=
      lkBot_floatLeft_ante (pre ++ [x]) x post rest Δ (by simp at h1 ⊢; exact h1)
    have h3 : lkBotProvable botP hBotArity ⟨pre ++ [x] ++ (post ++ rest), Δ⟩ :=
      lkBot_contractLeft_at pre x (post ++ rest) Δ (by simp at h2 ⊢; exact h2)
    have h4 : lkBotProvable botP hBotArity ⟨Γ ++ rest, Δ⟩ := by
      rw [hΓ]; simp at h3 ⊢; exact h3
    exact ih (fun y hy => hMem y (List.Mem.tail _ hy)) h4
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_mem_equiv_antecedent
    (Γ Γ' : List (FormulaN L)) (Δ : List (FormulaN L))
    (_hMem : ∀ x, x ∈ Γ' → x ∈ Γ) (hMem' : ∀ x, x ∈ Γ → x ∈ Γ')
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ⟩) :
    lkBotProvable botP hBotArity ⟨Γ', Δ⟩ := by
-- BEGIN PROOF
  have h1 := lkBot_weakenLeft_list (botP := botP) (hBotArity := hBotArity) Γ' Γ Δ h
  exact lkBot_contract_suffix Γ' Γ Δ (fun x hx => hMem' x hx) h1
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_exchangeRight_at
    (Γ : List (FormulaN L)) (pfx : List (FormulaN L)) (A B : FormulaN L)
    (sfx : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, pfx ++ [A, B] ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, pfx ++ [B, A] ++ sfx⟩ :=
-- BEGIN PROOF
  lkBot_onePremise (.exchangeRight Γ pfx A B sfx) h
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_sinkRight
    (Γ : List (FormulaN L)) (pfx : List (FormulaN L)) (A : FormulaN L)
    (mid sfx : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, pfx ++ [A] ++ mid ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, pfx ++ mid ++ [A] ++ sfx⟩ := by
-- BEGIN PROOF
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B rest ih =>
    have heq1 : pfx ++ [A] ++ (B :: rest) ++ sfx = pfx ++ [A, B] ++ (rest ++ sfx) := by
      simp [List.append_assoc, List.cons_append]
    have h1 := lkBot_exchangeRight_at Γ pfx A B (rest ++ sfx) (heq1 ▸ h)
    have heq2 : pfx ++ [B, A] ++ (rest ++ sfx) = (pfx ++ [B]) ++ [A] ++ rest ++ sfx := by
      simp [List.append_assoc, List.cons_append]
    have h2 := ih (pfx ++ [B]) (heq2 ▸ h1)
    have heq3 : (pfx ++ [B]) ++ rest ++ [A] ++ sfx = pfx ++ (B :: rest) ++ [A] ++ sfx := by
      simp [List.append_assoc, List.cons_append]
    exact heq3 ▸ h2
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_floatRight
    (Γ : List (FormulaN L)) (pfx : List (FormulaN L)) (A : FormulaN L)
    (mid sfx : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, pfx ++ mid ++ [A] ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, pfx ++ [A] ++ mid ++ sfx⟩ := by
-- BEGIN PROOF
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B rest ih =>
    have h1 := ih (pfx ++ [B]) (by simp at h ⊢; exact h)
    have h2 := lkBot_exchangeRight_at Γ pfx B A (rest ++ sfx) (by simp at h1 ⊢; exact h1)
    simp at h2 ⊢; exact h2
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contractRight_end
    (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (A : FormulaN L)
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ ++ [A, A]⟩) :
    lkBotProvable botP hBotArity ⟨Γ, Δ ++ [A]⟩ :=
-- BEGIN PROOF
  lkBot_onePremise (.contractRight A Γ Δ) h
-- Contraction at arbitrary position in succedent
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contractRight_at
    (Γ pfx : List (FormulaN L)) (A : FormulaN L) (sfx : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, pfx ++ [A, A] ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, pfx ++ [A] ++ sfx⟩ := by
-- BEGIN PROOF
  have step1 := lkBot_sinkRight Γ (pfx ++ [A]) A sfx [] (by simp at h ⊢; exact h)
  simp at step1
  have step2 := lkBot_sinkRight Γ pfx A sfx [A] (by simp at step1 ⊢; exact step1)
  simp at step2
  have step3 := lkBot_contractRight_end Γ (pfx ++ sfx) A (by simp at step2 ⊢; exact step2)
  have step4 := lkBot_floatRight Γ pfx A sfx [] (by simp at step3 ⊢; exact step3)
  simp at step4 ⊢; exact step4
-- Contract a suffix of the succedent when all its elements appear in the prefix
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_contract_suffix_succ
    (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (Δsuf : List (FormulaN L))
    (hMem : ∀ x, x ∈ Δsuf → x ∈ Δ)
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ ++ Δsuf⟩) :
    lkBotProvable botP hBotArity ⟨Γ, Δ⟩ := by
-- BEGIN PROOF
  induction Δsuf with
  | nil => simpa using h
  | cons x rest ih =>
    have hx := hMem x (List.Mem.head _)
    obtain ⟨pre, post, hΔ⟩ := LCS.CutElim.LKe.Equivalence.perm_mem_split x Δ hx
    have h1 : lkBotProvable botP hBotArity ⟨Γ, pre ++ [x] ++ (post ++ [x] ++ rest)⟩ := by
      rw [hΔ] at h; simp at h ⊢; exact h
    have h2 := lkBot_floatRight Γ (pre ++ [x]) x post rest (by simp at h1 ⊢; exact h1)
    have h3 := lkBot_contractRight_at Γ pre x (post ++ rest) (by simp at h2 ⊢; exact h2)
    have h4 : lkBotProvable botP hBotArity ⟨Γ, Δ ++ rest⟩ := by
      rw [hΔ]; simp at h3 ⊢; exact h3
    exact ih (fun y hy => hMem y (List.Mem.tail _ hy)) h4
-- Swap two adjacent blocks in the succedent (with a prefix)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_swap_succ_blocks_pfx
    (Γ pfx blk1 blk2 sfx : List (FormulaN L))
    (h : lkBotProvable botP hBotArity ⟨Γ, pfx ++ blk1 ++ blk2 ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, pfx ++ blk2 ++ blk1 ++ sfx⟩ := by
-- BEGIN PROOF
  induction blk1 generalizing pfx blk2 sfx with
  | nil => simpa using h
  | cons x rest ih =>
    have h1 := lkBot_sinkRight Γ pfx x (rest ++ blk2) sfx (by simp at h ⊢; exact h)
    have h2 := ih pfx blk2 ([x] ++ sfx) (by simp at h1 ⊢; exact h1)
    have h3 := lkBot_floatRight Γ (pfx ++ blk2) x rest sfx (by simp at h2 ⊢; exact h2)
    simp at h3 ⊢; exact h3
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBot_mem_equiv_succedent
    (Γ : List (FormulaN L)) (Δ Δ' sfx : List (FormulaN L))
    (_hMem : ∀ x, x ∈ Δ' → x ∈ Δ) (hMem' : ∀ x, x ∈ Δ → x ∈ Δ')
    (h : lkBotProvable botP hBotArity ⟨Γ, Δ ++ sfx⟩) :
    lkBotProvable botP hBotArity ⟨Γ, Δ' ++ sfx⟩ := by
-- BEGIN PROOF
  -- Weaken to get ⟨Γ, Δ ++ sfx ++ Δ'⟩
  have h1 := lkBot_weakenRight_list (botP := botP) (hBotArity := hBotArity) Γ (Δ ++ sfx) Δ' h
  -- Swap sfx and Δ': ⟨Γ, Δ ++ Δ' ++ sfx⟩
  have h2 := lkBot_swap_succ_blocks_pfx Γ Δ sfx Δ' [] (by simp at h1 ⊢; exact h1)
  simp at h2
  -- Swap Δ and Δ': ⟨Γ, Δ' ++ Δ ++ sfx⟩
  have h3 := lkBot_swap_succ_blocks_pfx Γ [] Δ Δ' sfx (by simp at h2 ⊢; exact h2)
  simp at h3
  -- Swap Δ and sfx: ⟨Γ, Δ' ++ sfx ++ Δ⟩
  have h4 := lkBot_swap_succ_blocks_pfx Γ Δ' Δ sfx [] (by simp at h3 ⊢; exact h3)
  simp at h4
  -- Contract Δ against Δ' ++ sfx
  exact lkBot_contract_suffix_succ Γ (Δ' ++ sfx) Δ
    (fun x hx => List.mem_append.mpr (Or.inl (hMem' x hx))) (by simp at h4 ⊢; exact h4)
-- ===================================================================
-- Theorem 6.5.1 (companion def): eliminateBot
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Theorem 6.5.1 (companion): Replaces each occurrence of ⊥
(encoded as `predN botP _`) by P' := ∀v(P(v,...,v) ∧ ¬P(v,...,v)),
per the proof strategy of Theorem 6.5.1. All argument positions of
P are filled with the fresh variable v (this is sound because the
replacement is semantic — P' is an arbitrary unsatisfiable formula,
and the choice of arity merely packages it). -/
noncomputable def eliminateBot {L : Language}
    (botP : L.predSymbols) (_hBotArity : L.predArity botP = 0)
    (C : FormulaN L) (P : L.predSymbols) (v : Nat) : FormulaN L :=
  open Classical in
  match C with
  | .predN Q args =>
    if Q = botP then
      let pApp := FormulaN.predN P (fun _ => Term.var v)
      FormulaN.all v (FormulaN.falsum pApp)
    else .predN Q args
  | .eq_ hL t1 t2 => .eq_ hL t1 t2
  | .conj A B =>
    FormulaN.conj (eliminateBot botP _hBotArity A P v)
      (eliminateBot botP _hBotArity B P v)
  | .disj A B =>
    FormulaN.disj (eliminateBot botP _hBotArity A P v)
      (eliminateBot botP _hBotArity B P v)
  | .impl A B =>
    FormulaN.impl (eliminateBot botP _hBotArity A P v)
      (eliminateBot botP _hBotArity B P v)
  | .neg A => FormulaN.neg (eliminateBot botP _hBotArity A P v)
  | .all x A => FormulaN.all x (eliminateBot botP _hBotArity A P v)
  | .ex x A => FormulaN.ex x (eliminateBot botP _hBotArity A P v)
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- When the input formula has no occurrence of the bot predicate
symbol `botP`, `eliminateBot` is the identity. -/
theorem eliminateBot_no_botP {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (A : FormulaN L) (P : L.predSymbols) (v : Nat)
    (hNoBot : ¬ formulaPredSymbolsN A botP) :
    eliminateBot botP hBotArity A P v = A := by
-- BEGIN PROOF
  induction A with
  | predN Q args =>
    simp only [eliminateBot]
    have hQne : Q ≠ botP := by
      intro heq
      apply hNoBot
      simp only [formulaPredSymbolsN]
      exact heq.symm
    simp [hQne]
  | eq_ _ _ => rfl
  | neg A ih =>
    have : ¬ formulaPredSymbolsN A botP := by
      intro h; exact hNoBot (by simp only [formulaPredSymbolsN]; exact h)
    simp [eliminateBot, ih this]
  | conj A B ihA ihB =>
    have hA : ¬ formulaPredSymbolsN A botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inl h)
    have hB : ¬ formulaPredSymbolsN B botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inr h)
    simp [eliminateBot, ihA hA, ihB hB]
  | disj A B ihA ihB =>
    have hA : ¬ formulaPredSymbolsN A botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inl h)
    have hB : ¬ formulaPredSymbolsN B botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inr h)
    simp [eliminateBot, ihA hA, ihB hB]
  | impl A B ihA ihB =>
    have hA : ¬ formulaPredSymbolsN A botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inl h)
    have hB : ¬ formulaPredSymbolsN B botP := fun h =>
      hNoBot (by simp only [formulaPredSymbolsN]; exact Or.inr h)
    simp [eliminateBot, ihA hA, ihB hB]
  | all _ A ih =>
    have : ¬ formulaPredSymbolsN A botP := by
      intro h; exact hNoBot (by simp only [formulaPredSymbolsN]; exact h)
    simp [eliminateBot, ih this]
  | ex _ A ih =>
    have : ¬ formulaPredSymbolsN A botP := by
      intro h; exact hNoBot (by simp only [formulaPredSymbolsN]; exact h)
    simp [eliminateBot, ih this]
-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def eliminateBotList {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (fs : List (FormulaN L)) (P : L.predSymbols) (v : Nat) : List (FormulaN L) :=
  fs.map (fun F => eliminateBot botP hBotArity F P v)
-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def eliminateBotSeq {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (P : L.predSymbols) (v : Nat) : Sequent L :=
  { antecedent := eliminateBotList botP hBotArity s.antecedent P v,
    succedent := eliminateBotList botP hBotArity s.succedent P v }
-- eliminateBot symbol/FV analysis
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_pred_sub {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (C : FormulaN L) (P : L.predSymbols) (v : Nat)
    (x : L.predSymbols)
    (hx : formulaPredSymbolsN (eliminateBot botP hBotArity C P v) x) :
    formulaPredSymbolsN C x ∨ x = P := by
-- BEGIN PROOF
  induction C with
  | predN Q args =>
    by_cases hQ : Q = botP
    · simp only [eliminateBot, hQ, ↓reduceIte, formulaPredSymbolsN] at hx
      rcases hx with hx | hx
      · exact Or.inr hx
      · exact Or.inr hx
    · exact Or.inl (by
        simpa [eliminateBot, hQ, formulaPredSymbolsN] using hx)
  | eq_ _ t1 t2 =>
    exact hx.elim
  | neg A ih =>
    exact ih hx
  | conj A B ihA ihB =>
    rcases hx with hA | hB
    · rcases ihA hA with hA' | hxP
      · exact Or.inl (Or.inl hA')
      · exact Or.inr hxP
    · rcases ihB hB with hB' | hxP
      · exact Or.inl (Or.inr hB')
      · exact Or.inr hxP
  | disj A B ihA ihB =>
    rcases hx with hA | hB
    · rcases ihA hA with hA' | hxP
      · exact Or.inl (Or.inl hA')
      · exact Or.inr hxP
    · rcases ihB hB with hB' | hxP
      · exact Or.inl (Or.inr hB')
      · exact Or.inr hxP
  | impl A B ihA ihB =>
    rcases hx with hA | hB
    · rcases ihA hA with hA' | hxP
      · exact Or.inl (Or.inl hA')
      · exact Or.inr hxP
    · rcases ihB hB with hB' | hxP
      · exact Or.inl (Or.inr hB')
      · exact Or.inr hxP
  | all y A ih =>
    exact ih hx
  | ex y A ih =>
    exact ih hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_const_sub {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (C : FormulaN L) (P : L.predSymbols) (v : Nat) :
    formulaConstSymbolsN (eliminateBot botP hBotArity C P v) ⊆
      formulaConstSymbolsN C := by
-- BEGIN PROOF
  intro c hc
  induction C with
  | predN Q args =>
    by_cases hQ : Q = botP
    · simp only [eliminateBot, hQ, ↓reduceIte, formulaConstSymbolsN,
        termConstSymbols] at hc
      rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hi.elim
      · exact hi.elim
    · simpa [eliminateBot, hQ, formulaConstSymbolsN] using hc
  | eq_ _ t1 t2 =>
    exact hc
  | neg A ih =>
    exact ih hc
  | conj A B ihA ihB =>
    rcases hc with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | disj A B ihA ihB =>
    rcases hc with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | impl A B ihA ihB =>
    rcases hc with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | all y A ih =>
    exact ih hc
  | ex y A ih =>
    exact ih hc
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_fv_sub {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (C : FormulaN L) (P : L.predSymbols) (v : Nat) :
    formulaFVN (eliminateBot botP hBotArity C P v) ⊆ formulaFVN C := by
-- BEGIN PROOF
  intro x hx
  induction C with
  | predN Q args =>
    by_cases hQ : Q = botP
    · simp only [eliminateBot, hQ, ↓reduceIte, formulaFVN, termFV] at hx
      rcases hx.1 with h | h
      · obtain ⟨i, hxv⟩ := h
        exact (hx.2 hxv).elim
      · obtain ⟨i, hxv⟩ := h
        exact (hx.2 hxv).elim
    · simpa [eliminateBot, hQ, formulaFVN] using hx
  | eq_ _ t1 t2 =>
    exact hx
  | neg A ih =>
    exact ih hx
  | conj A B ihA ihB =>
    rcases hx with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | disj A B ihA ihB =>
    rcases hx with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | impl A B ihA ihB =>
    rcases hx with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | all y A ih =>
    exact ⟨ih hx.1, hx.2⟩
  | ex y A ih =>
    exact ⟨ih hx.1, hx.2⟩
-- ===================================================================
-- eliminateBot conversion
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkCutFreeProvable_to_folkProvable {L : Language} {s : Sequent L}
    (h : folkCutFreeProvable s) : folkProvable s := by
  obtain ⟨t, _⟩ := h; exact ⟨t⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkProvable_cut {L : Language}
    (A : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L))
    (h1 : folkProvable { antecedent := Γ, succedent := Δ ++ [A] })
    (h2 : folkProvable { antecedent := A :: Λ, succedent := Θ }) :
    folkProvable { antecedent := Γ ++ Λ, succedent := Δ ++ Θ } := by
-- BEGIN PROOF
  obtain ⟨t1⟩ := h1; obtain ⟨t2⟩ := h2
  exact ⟨.twoPremise (.cut A Γ Δ Λ Θ) t1 t2⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkProvable_contractLeft_head {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkProvable { antecedent := A :: A :: Γ, succedent := Δ }) :
    folkProvable { antecedent := A :: Γ, succedent := Δ } := by
  obtain ⟨t⟩ := h; exact ⟨.onePremise (.contractLeft A Γ Δ) t⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkProvable_allLeft_head {L : Language}
    (t_term : Term L) (x : Nat) (A : FormulaN L)
    (Γ Δ : List (FormulaN L)) (hfree : isFreeForN t_term x A)
    (h : folkProvable { antecedent := formulaSubstN A t_term x :: Γ, succedent := Δ }) :
    folkProvable { antecedent := FormulaN.all x A :: Γ, succedent := Δ } := by
  obtain ⟨t⟩ := h; exact ⟨.onePremise (.allLeft t_term x A Γ Δ hfree) t⟩
end LCS.CutElim.Interpolation
end
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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (z : Nat) (y : Nat)
-- ATTACH-BLOCKER: section variables: helper requires front context
def stepVar_allLeft
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotBound : (FOLKStep1.allLeft t x A Γ Δ hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.allLeft t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (formulaSubstN A t x :: Γ) (Δ)) z y) (sequentSubstVar (Sequent.mk
      (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t x y z hxy hzx hfree hNoY hNoZ
  simpa [sequentSubstVar, formulaSubstN, hyx, formulaSubst_var_comm A t x y z hxy hzx hNoY] using
      FOLKStep1.allLeft (termSubst t (.var z) y) x (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree'
-- ATTACH-BLOCKER: section variables: helper requires front context
def stepVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (hNotBound : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).notBoundIn y)
      (hNotOccurs : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var e) x])) z y)
      (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hNotOccurs.2.1 (Ne.symm hze)
  simpa [sequentSubstVar, formulaSubstN, hyx, hterm,
    formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree'
-- ATTACH-BLOCKER: section variables: helper requires front context
def stepVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (hNotBound : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ) (Δ)) z y) (sequentSubstVar
      (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hNotBound
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hyx : y ≠ x := hNotBound.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hNotBound.2.2.2
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hNotOccurs.2.1 (Ne.symm hze)
  simpa [sequentSubstVar, formulaSubstN, hyx, hterm,
    formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree'
end
end LCS.CutElim.Interpolation
end

