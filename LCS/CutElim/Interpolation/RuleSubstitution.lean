import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import Attach
import LCS.CutElim.Interpolation.RuleSubstitution.ProofsStamp

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
def stepVar_exRight
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotBound : (FOLKStep1.exRight t x A Γ Δ hfree).notBoundIn y) (hNotOccurs :
      (FOLKStep1.exRight t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t x])) z y) (sequentSubstVar
      (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
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
      FOLKStep1.exRight (termSubst t (.var z) y) x (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree'

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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

@[blueprint "chap6__lemma_6_5_1"]
def folkStep1SubstVar {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (z y : Nat) (hNotBound : rule.notBoundIn y)
    (hNotOccurs : rule.varNotOccurs z) :
    FOLKStep1 (sequentSubstVar prem z y)
      (sequentSubstVar conc z y) := by
  exact transform rule z y hNotBound hNotOccurs
where
  transform {L : Language}
      {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (z y : Nat) (hNotBound : rule.notBoundIn y)
      (hNotOccurs : rule.varNotOccurs z) :
      FOLKStep1 (sequentSubstVar prem z y)
        (sequentSubstVar conc z y)  := by
    have termSubstVarEqOfNotFree : ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree : ∀ F : FormulaN L, y ∉ formulaFVN F → formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉ formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    cases rule with
    | weakenLeft A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.weakenLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | weakenRight A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.weakenRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | contractLeft A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.contractLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | contractRight A Γ Δ =>
        simpa [sequentSubstVar] using FOLKStep1.contractRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | exchangeLeft Γ A B Δ Λ =>
        simpa [sequentSubstVar] using FOLKStep1.exchangeLeft (Γ.map (fun F => formulaSubstN F (.var z) y))
            (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Δ.map (fun F => formulaSubstN F (.var z) y))
            (Λ.map (fun F => formulaSubstN F (.var z) y))
    | exchangeRight Γ Δ A B Λ =>
        simpa [sequentSubstVar] using FOLKStep1.exchangeRight (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
            (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Λ.map (fun F => formulaSubstN F (.var z) y))
    | andLeftL A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.andLeftL (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | andLeftR A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.andLeftR (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | orRightL A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.orRightL (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | orRightR A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.orRightR (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | implRight A B Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.implRight (formulaSubstN A (.var z) y)
            (formulaSubstN B (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | negLeft A Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.negLeft (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | negRight A Γ Δ =>
        simpa [sequentSubstVar, formulaSubstN] using FOLKStep1.negRight (formulaSubstN A (.var z) y)
            (Γ.map (fun F => formulaSubstN F (.var z) y))
            (Δ.map (fun F => formulaSubstN F (.var z) y))
    | allLeft t x A Γ Δ hfree =>
        exact stepVar_allLeft L z y t x A Γ Δ hfree hNotBound hNotOccurs
    | allRight e x A Γ Δ hfresh hfree =>
        exact stepVar_allRight L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree hNotBound hNotOccurs
    | exLeft e x A Γ Δ hfresh hfree =>
        exact stepVar_exLeft L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree hNotBound hNotOccurs
    | exRight t x A Γ Δ hfree =>
        exact stepVar_exRight L z y t x A Γ Δ hfree hNotBound hNotOccurs

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
variable (L : Language) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_allLeft
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotOccurs : (FOLKStep1.allLeft t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (formulaSubstN A t x :: Γ) (Δ)) z c) (sequentSubstConst
      (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t x z c hfree hNoZ
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A t x z c hzx] using
      FOLKStep1.allLeft (termSubstConst t z c) x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_allRight
    (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent
      ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ :
      List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all
      x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x A) (hNotOccurs : (FOLKStep1.allRight e x A
      Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var e) x])) z c)
      (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
    termSubstConst] using FOLKStep1.allRight e x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_exLeft
    (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent
      ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ :
      List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++
      (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x A) (hNotOccurs : (FOLKStep1.exLeft e x A Γ Δ
      hfresh hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ) (Δ)) z c)
      (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hze : z ≠ e := hNotOccurs.2.2.1
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
    termSubstConst] using FOLKStep1.exLeft e x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree'

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def stepConst_exRight
    (t : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t x A) (hNotOccurs : (FOLKStep1.exRight t x A Γ Δ hfree).varNotOccurs z)
    : FOLKStep1 (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t x])) z c) (sequentSubstConst
      (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hNotOccurs
  have hzx : z ≠ x := hNotOccurs.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hNotOccurs.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t x z c hfree hNoZ
  simpa [sequentSubstConst, formulaSubstConst, formulaSubstConst_formulaSubst_comm A t x z c hzx] using
      FOLKStep1.exRight (termSubstConst t z c) x (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree'

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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkStep1SubstConst {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (z : Nat) (c : L.constSymbols) (hNotOccurs : rule.varNotOccurs z) :
    FOLKStep1 (sequentSubstConst prem z c)
      (sequentSubstConst conc z c) := by
  exact transform rule z c hNotOccurs
where
  transform {L : Language}
      {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (z : Nat) (c : L.constSymbols) (hNotOccurs : rule.varNotOccurs z) :
      FOLKStep1 (sequentSubstConst prem z c)
        (sequentSubstConst conc z c)  := by
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      intro F hF
      change F ∈ q.antecedent.map (fun A => formulaSubstConst A z c) ++
          q.succedent.map (fun A => formulaSubstConst A z c) at hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
        exact formulaFV_formulaSubstConst G z c e hez (he G (List.mem_append.mpr (Or.inl hG)))
      · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
        exact formulaFV_formulaSubstConst G z c e hez (he G (List.mem_append.mpr (Or.inr hG)))
    cases rule with
    | weakenLeft A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.weakenLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | weakenRight A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.weakenRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | contractLeft A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.contractLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | contractRight A Γ Δ =>
        simpa [sequentSubstConst] using FOLKStep1.contractRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | exchangeLeft Γ A B Δ Λ =>
        simpa [sequentSubstConst] using FOLKStep1.exchangeLeft (Γ.map (fun F => formulaSubstConst F z c))
            (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Δ.map (fun F => formulaSubstConst F z c))
            (Λ.map (fun F => formulaSubstConst F z c))
    | exchangeRight Γ Δ A B Λ =>
        simpa [sequentSubstConst] using FOLKStep1.exchangeRight (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
            (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Λ.map (fun F => formulaSubstConst F z c))
    | andLeftL A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.andLeftL (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | andLeftR A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.andLeftR (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | orRightL A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.orRightL (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | orRightR A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.orRightR (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | implRight A B Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.implRight (formulaSubstConst A z c)
            (formulaSubstConst B z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | negLeft A Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.negLeft (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | negRight A Γ Δ =>
        simpa [sequentSubstConst, formulaSubstConst] using FOLKStep1.negRight (formulaSubstConst A z c)
            (Γ.map (fun F => formulaSubstConst F z c))
            (Δ.map (fun F => formulaSubstConst F z c))
    | allLeft t x A Γ Δ hfree =>
        exact stepConst_allLeft L z c t x A Γ Δ hfree hNotOccurs
    | allRight e x A Γ Δ hfresh hfree =>
        exact stepConst_allRight L z c sequentFreshAfterConst e x A Γ Δ hfresh hfree hNotOccurs
    | exLeft e x A Γ Δ hfresh hfree =>
        exact stepConst_exLeft L z c sequentFreshAfterConst e x A Γ Δ hfresh hfree hNotOccurs
    | exRight t x A Γ Δ hfree =>
        exact stepConst_exRight L z c t x A Γ Δ hfree hNotOccurs

@[blueprint "chap6__lemma_6_5_1"]
def folkStep2SubstVar {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) (z y : Nat) :
    FOLKStep2 (sequentSubstVar prem₁ z y)
      (sequentSubstVar prem₂ z y) (sequentSubstVar conc z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      simpa [sequentSubstVar] using
        FOLKStep2.cut
          (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y))
  | andRight A B Γ Δ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
  | orLeft A B Γ Δ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
  | implLeft A B Γ Δ Λ Θ =>
      simpa [sequentSubstVar, formulaSubstN] using
        FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y))

@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkStep2SubstConst {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) (z : Nat)
    (c : L.constSymbols) :
    FOLKStep2 (sequentSubstConst prem₁ z c)
      (sequentSubstConst prem₂ z c) (sequentSubstConst conc z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      simpa [sequentSubstConst] using
        FOLKStep2.cut
          (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c))
  | andRight A B Γ Δ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
  | orLeft A B Γ Δ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
  | implLeft A B Γ Δ Λ Θ =>
      simpa [sequentSubstConst, formulaSubstConst] using
        FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c))

-- lkBotProvable_eliminateBot
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem lkBotProvable_eliminateBot {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (P : L.predSymbols)
    (s : Sequent L) (h : lkBotProvable botP hBotArity s) :
    ∃ v, folkProvable (eliminateBotSeq botP hBotArity s P v) := sorry -- DEBT(Section 6.5.2, LK⊥: translation of an LK⊥-proof to an LK-proof with ⊥ replaced by a fresh atom; proof pending)

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
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- View an LKₑ proof as a deduction tree, retaining its inference nodes. -/
def _root_.LCS.CutElim.LKe.LKeProofTree.toDeductionTree {L : Language} :
    {s : Sequent L} → LKeProofTree s → LKeDeductionTree s
  | _, .axiom_ s _ => .leaf s
  | _, .eqAxiom hL ax => .eqAxiom hL ax
  | _, .onePremise rule t => .onePremise rule t.toDeductionTree
  | _, .twoPremise rule t₁ t₂ => .twoPremise rule t₁.toDeductionTree t₂.toDeductionTree
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- A proof viewed as a deduction tree satisfies `isProof`. -/
theorem _root_.LCS.CutElim.LKe.LKeProofTree.toDeductionTree_isProof
    {L : Language} {s : Sequent L} (T : LKeProofTree s) : T.toDeductionTree.isProof := by
  induction T with
  | axiom_ s h => exact Or.inl h
  | eqAxiom => trivial
  | onePremise rule t ih => exact ih
  | twoPremise rule t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Viewing an LKₑ proof as a deduction tree preserves `notBoundIn`. -/
theorem _root_.LCS.CutElim.LKe.LKeProofTree.toDeductionTree_notBoundIn
    {L : Language} {s : Sequent L} (T : LKeProofTree s) (v : Nat) :
    T.toDeductionTree.notBoundIn v ↔ T.notBoundIn v := by
  induction T with
  | axiom_ => rfl
  | eqAxiom => rfl
  | onePremise rule t ih => exact and_congr Iff.rfl ih
  | twoPremise rule t₁ t₂ ih₁ ih₂ => exact and_congr Iff.rfl (and_congr ih₁ ih₂)
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Viewing an LKₑ proof as a deduction tree preserves `varNotOccurs`. -/
theorem _root_.LCS.CutElim.LKe.LKeProofTree.toDeductionTree_varNotOccurs
    {L : Language} {s : Sequent L} (T : LKeProofTree s) (v : Nat) :
    T.toDeductionTree.varNotOccurs v ↔ T.varNotOccurs v := by
  induction T with
  | axiom_ => rfl
  | eqAxiom => rfl
  | onePremise rule t ih => exact and_congr Iff.rfl ih
  | twoPremise rule t₁ t₂ ih₁ ih₂ => exact and_congr Iff.rfl (and_congr ih₁ ih₂)
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
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Variable substitution preserves the `isProof` predicate on LKₑ deduction trees. -/
theorem _root_.LCS.CutElim.LKe.LKeDeductionTree.substVar_isProof
    {L : Language} {s : Sequent L} (T : LKeDeductionTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    (T.substVar z y hNotBound hNotOccurs).isProof := by
  -- REPAIR(T6-42b): proof pending
  sorry
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Constant substitution preserves the `isProof` predicate on LKₑ deduction trees. -/
theorem _root_.LCS.CutElim.LKe.LKeDeductionTree.substConst_isProof
    {L : Language} {s : Sequent L} (T : LKeDeductionTree s) (z : Nat)
    (c : L.constSymbols) (hNotOccurs : T.varNotOccurs z) (hp : T.isProof) :
    (T.substConst z c hNotOccurs).isProof := by
  -- REPAIR(T6-42b): proof pending
  sorry
/-- Variable substitution on LKₑ proofs is the proof-tree image of
substitution on their deduction trees. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def lkeProofSubstVar {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LKeProofTree (sequentSubstVar s z y) :=
  let U := T.toDeductionTree
  let hNB := (T.toDeductionTree_notBoundIn y).mpr hNotBound
  let hNO := (T.toDeductionTree_varNotOccurs z).mpr hNotOccurs
  (U.substVar z y hNB hNO).toProofTree
    (U.substVar_isProof z y hNB hNO T.toDeductionTree_isProof)
/-- Constant substitution on LKₑ proofs is the proof-tree image of
substituting a fresh variable for any constant in their deduction trees. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def lkeProofSubstConst {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LKeProofTree (sequentSubstConst s z c) :=
  let U := T.toDeductionTree
  let hNO := (T.toDeductionTree_varNotOccurs z).mpr hNotOccurs
  (U.substConst z c hNO).toProofTree
    (U.substConst_isProof z c hNO T.toDeductionTree_isProof)
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Provability-level consequences of variable and constant substitution
on LKₑ proof trees. -/
theorem lke_subst_preservation {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (y z : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    lkeProvable (sequentSubstVar s z y) ∧
      ∀ c : L.constSymbols, T.constOccurs c →
        lkeProvable (sequentSubstConst s z c) :=
  ⟨⟨lkeProofSubstVar T z y hNotBound hNotOccurs⟩,
    fun c hConstOccurs =>
      ⟨lkeProofSubstConst T z c hNotOccurs⟩⟩
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
-- ===================================================================
-- Formula symbol subset lemmas for connectives (preserved — pure formula lemmas)
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_conj_left {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN A ⊆ formulaPredSymbolsN (.conj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_conj_right {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN B ⊆ formulaPredSymbolsN (.conj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_conj_left {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN A ⊆ formulaConstSymbolsN (.conj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_conj_right {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN B ⊆ formulaConstSymbolsN (.conj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_conj_left {L : Language} (A B : FormulaN L) :
    formulaFVN A ⊆ formulaFVN (.conj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_conj_right {L : Language} (A B : FormulaN L) :
    formulaFVN B ⊆ formulaFVN (.conj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_disj_left {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN A ⊆ formulaPredSymbolsN (.disj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_disj_right {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN B ⊆ formulaPredSymbolsN (.disj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_neg {L : Language} (A : FormulaN L) :
    formulaPredSymbolsN A = formulaPredSymbolsN (.neg A) := by simp only [formulaPredSymbolsN]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_all {L : Language} (x : Nat) (A : FormulaN L) :
    formulaPredSymbolsN A = formulaPredSymbolsN (.all x A) := by simp only [formulaPredSymbolsN]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_ex {L : Language} (x : Nat) (A : FormulaN L) :
    formulaPredSymbolsN A = formulaPredSymbolsN (.ex x A) := by simp only [formulaPredSymbolsN]
-- ===================================================================
-- Substitution symbol preservation
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_formulaSubst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaPredSymbolsN (formulaSubstN A t x) = formulaPredSymbolsN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => simp [formulaSubstN, formulaPredSymbolsN]
  | eq_ _ t1 t2 => simp [formulaSubstN, formulaPredSymbolsN]
  | neg A ih => simp [formulaSubstN, formulaPredSymbolsN, ih]
  | conj A B ihA ihB => simp [formulaSubstN, formulaPredSymbolsN, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, formulaPredSymbolsN, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, formulaPredSymbolsN, ihA, ihB]
  | all y A ih =>
    simp only [formulaSubstN]
    split
    · simp [formulaPredSymbolsN, ih]
    · simp [formulaPredSymbolsN]
  | ex y A ih =>
    simp only [formulaSubstN]
    split
    · simp [formulaPredSymbolsN, ih]
    · simp [formulaPredSymbolsN]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_formulaSubst_sub {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaPredSymbolsN (formulaSubstN A t x) ⊆ formulaPredSymbolsN A :=
-- BEGIN PROOF
  fun P hP => (formulaPredSymbolsN_formulaSubst A t x ▸ hP)
-- For variable substitution, const symbols are preserved exactly
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_formulaSubst_var {L : Language}
    (A : FormulaN L) (y x : Nat) :
    formulaConstSymbolsN (formulaSubstN A (.var y) x) ⊆ formulaConstSymbolsN A := by
-- BEGIN PROOF
  intro c hc
  rcases formulaConstSymbolsN_formulaSubst A (.var y) x c hc with hA | hVar
  · exact hA
  · exact (hVar).elim
-- Combined containment lemmas for quantifier rules.
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_subst_le_all {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaPredSymbolsN (formulaSubstN A t x) ⊆ formulaPredSymbolsN (.all x A) := by
-- BEGIN PROOF
  rw [← formulaPredSymbolsN_all]; exact formulaPredSymbolsN_formulaSubst_sub A t x
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_subst_le_ex {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaPredSymbolsN (formulaSubstN A t x) ⊆ formulaPredSymbolsN (.ex x A) := by
-- BEGIN PROOF
  rw [← formulaPredSymbolsN_ex]; exact formulaPredSymbolsN_formulaSubst_sub A t x
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_subst_var_le_all {L : Language}
    (A : FormulaN L) (y x : Nat) :
    formulaConstSymbolsN (formulaSubstN A (.var y) x) ⊆ formulaConstSymbolsN (.all x A) :=
-- BEGIN PROOF
  formulaConstSymbolsN_formulaSubst_var A y x
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_subst_var_le_ex {L : Language}
    (A : FormulaN L) (y x : Nat) :
    formulaConstSymbolsN (formulaSubstN A (.var y) x) ⊆ formulaConstSymbolsN (.ex x A) :=
-- BEGIN PROOF
  formulaConstSymbolsN_formulaSubst_var A y x
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_subst_var_le_all_union {L : Language}
    (A : FormulaN L) (y x : Nat) :
    formulaFVN (formulaSubstN A (.var y) x) ⊆ formulaFVN (.all x A) ∪ Set.singleton y := by
-- BEGIN PROOF
  intro v hv
  rcases formulaFV_formulaSubst A (.var y) x v hv with ⟨hA, hne⟩ | hVar
  · exact Or.inl ⟨hA, hne⟩
  · exact Or.inr hVar
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_subst_var_le_ex_union {L : Language}
    (A : FormulaN L) (y x : Nat) :
    formulaFVN (formulaSubstN A (.var y) x) ⊆ formulaFVN (.ex x A) ∪ Set.singleton y := by
-- BEGIN PROOF
  intro v hv
  rcases formulaFV_formulaSubst A (.var y) x v hv with ⟨hA, hne⟩ | hVar
  · exact Or.inl ⟨hA, hne⟩
  · exact Or.inr hVar
-- Helper for substituting for a variable not free
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termSubst_not_free {L : Language} (t : Term L) (s : Term L) (x : Nat)
    (h : x ∉ termFV t) : termSubst t s x = t := by
-- BEGIN PROOF
  induction t with
  | var y =>
    simp only [termSubst]; split
    · rename_i heq; exact absurd (heq ▸ rfl : x ∈ termFV (Term.var x)) (heq ▸ h)
    · rfl
  | const c => rfl
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i; exact ih i (fun hmem => h ⟨i, hmem⟩)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaSubst_not_free {L : Language} (A : FormulaN L) (t : Term L) (x : Nat)
    (h : x ∉ formulaFVN A) : formulaSubstN A t x = A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i; exact termSubst_not_free (ts i) t x (fun hmem => h ⟨i, hmem⟩)
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, FormulaN.eq_.injEq]
    exact ⟨termSubst_not_free t1 t x (fun hm => h (Or.inl hm)),
           termSubst_not_free t2 t x (fun hm => h (Or.inr hm))⟩
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.conj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.disj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.impl.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | neg A ih =>
    simp only [formulaSubstN, FormulaN.neg.injEq]; exact ih h
  | all w A ih =>
    simp only [formulaSubstN]; split
    · simp only [FormulaN.all.injEq, true_and]
      exact ih (fun hm => h ⟨hm, by rename_i hne; exact (bne_iff_ne.mp hne)⟩)
    · rfl
  | ex w A ih =>
    simp only [formulaSubstN]; split
    · simp only [FormulaN.ex.injEq, true_and]
      exact ih (fun hm => h ⟨hm, by rename_i hne; exact (bne_iff_ne.mp hne)⟩)
    · rfl
-- Same-var substitution lemmas
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termSubst_same_var {L : Language}
    (t' t s : Term L) (x : Nat) :
    termSubst (termSubst t' t x) s x = termSubst t' (termSubst t s x) x := by
-- BEGIN PROOF
  induction t' with
  | var y =>
    simp only [termSubst]; split
    · rfl
    · simp only [termSubst]; split
      · rename_i h1 h2; exact absurd h2 h1
      · rfl
  | const c => simp only [termSubst]
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i; exact ih i
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaSubst_same_var {L : Language}
    (A : FormulaN L) (t s : Term L) (x : Nat) :
    formulaSubstN (formulaSubstN A t x) s x = formulaSubstN A (termSubst t s x) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i; exact termSubst_same_var _ _ _ _
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN]; congr 1 <;> exact termSubst_same_var _ _ _ _
  | conj _ _ ihA ihB => simp only [formulaSubstN]; exact congr (congrArg _ ihA) ihB
  | disj _ _ ihA ihB => simp only [formulaSubstN]; exact congr (congrArg _ ihA) ihB
  | impl _ _ ihA ihB => simp only [formulaSubstN]; exact congr (congrArg _ ihA) ihB
  | neg _ ih => simp only [formulaSubstN]; exact congrArg _ ih
  | all y _ ih =>
    simp only [formulaSubstN]
    by_cases hxy : x = y
    · subst hxy; simp [formulaSubstN, bne_self_eq_false]
    · have hbne : (x != y) = true := bne_iff_ne.mpr hxy
      simp only [hbne, ↓reduceIte, formulaSubstN]
      exact congrArg _ ih
  | ex y _ ih =>
    simp only [formulaSubstN]
    by_cases hxy : x = y
    · subst hxy; simp [formulaSubstN, bne_self_eq_false]
    · have hbne : (x != y) = true := bne_iff_ne.mpr hxy
      simp only [hbne, ↓reduceIte, formulaSubstN]
      exact congrArg _ ih
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem isFreeFor_termSubst_same_var {L : Language}
    (A : FormulaN L) (t : Term L) (x z : Nat)
    (hfree : isFreeForN t x A) (hNoZ : ¬ formulaBVN A z) :
    isFreeForN (termSubst t (.var z) x) x A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => trivial
  | eq_ _ t1 t2 => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | neg A ih => exact ih hfree hNoZ
  | all w A ih =>
    simp only [isFreeForN] at hfree ⊢
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right
      have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      exact ⟨termFV_termSubst_var t x z w (Ne.symm hzw) hwtv,
             ih hff (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    simp only [isFreeForN] at hfree ⊢
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right
      have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      exact ⟨termFV_termSubst_var t x z w (Ne.symm hzw) hwtv,
             ih hff (fun h => hNoZ (Or.inl h))⟩
-- Cons/snoc replace helpers for symbol containment
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaPredSymbols_cons_replace {L : Language}
    {X Y : FormulaN L} {rest tail : List (FormulaN L)}
    (hSub : formulaPredSymbolsN X ⊆ formulaPredSymbolsN Y) :
    listFormulaPredSymbols ((X :: rest) ++ tail) ⊆
    listFormulaPredSymbols ((Y :: rest) ++ tail) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · rcases List.mem_cons.mp h with heq | h'
    · subst heq; exact ⟨Y, List.mem_append_left _ (List.Mem.head _), hSub z hFs⟩
    · exact ⟨F, List.mem_append_left _ (List.Mem.tail _ h'), hFs⟩
  · exact ⟨F, List.mem_append_right _ h, hFs⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaConstSymbols_cons_replace {L : Language}
    {X Y : FormulaN L} {rest tail : List (FormulaN L)}
    (hSub : formulaConstSymbolsN X ⊆ formulaConstSymbolsN Y) :
    listFormulaConstSymbols ((X :: rest) ++ tail) ⊆
    listFormulaConstSymbols ((Y :: rest) ++ tail) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · rcases List.mem_cons.mp h with heq | h'
    · subst heq; exact ⟨Y, List.mem_append_left _ (List.Mem.head _), hSub z hFs⟩
    · exact ⟨F, List.mem_append_left _ (List.Mem.tail _ h'), hFs⟩
  · exact ⟨F, List.mem_append_right _ h, hFs⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaFV_cons_replace {L : Language}
    {X Y : FormulaN L} {rest tail : List (FormulaN L)}
    (hSub : formulaFVN X ⊆ formulaFVN Y) :
    listFormulaFV ((X :: rest) ++ tail) ⊆
    listFormulaFV ((Y :: rest) ++ tail) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · rcases List.mem_cons.mp h with heq | h'
    · subst heq; exact ⟨Y, List.mem_append_left _ (List.Mem.head _), hSub z hFs⟩
    · exact ⟨F, List.mem_append_left _ (List.Mem.tail _ h'), hFs⟩
  · exact ⟨F, List.mem_append_right _ h, hFs⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaPredSymbols_snoc_replace {L : Language}
    {X Y : FormulaN L} {head tail : List (FormulaN L)}
    (hSub : formulaPredSymbolsN X ⊆ formulaPredSymbolsN Y) :
    listFormulaPredSymbols (head ++ (tail ++ [X])) ⊆
    listFormulaPredSymbols (head ++ (tail ++ [Y])) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · exact ⟨F, List.mem_append_left _ h, hFs⟩
  · rcases List.mem_append.mp h with h' | h'
    · exact ⟨F, List.mem_append_right _ (List.mem_append_left _ h'), hFs⟩
    · rcases List.mem_cons.mp h' with heq | h''
      · subst heq; exact ⟨Y, List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)), hSub z hFs⟩
      · simp at h''
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaConstSymbols_snoc_replace {L : Language}
    {X Y : FormulaN L} {head tail : List (FormulaN L)}
    (hSub : formulaConstSymbolsN X ⊆ formulaConstSymbolsN Y) :
    listFormulaConstSymbols (head ++ (tail ++ [X])) ⊆
    listFormulaConstSymbols (head ++ (tail ++ [Y])) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · exact ⟨F, List.mem_append_left _ h, hFs⟩
  · rcases List.mem_append.mp h with h' | h'
    · exact ⟨F, List.mem_append_right _ (List.mem_append_left _ h'), hFs⟩
    · rcases List.mem_cons.mp h' with heq | h''
      · subst heq; exact ⟨Y, List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)), hSub z hFs⟩
      · simp at h''
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaFV_snoc_replace {L : Language}
    {X Y : FormulaN L} {head tail : List (FormulaN L)}
    (hSub : formulaFVN X ⊆ formulaFVN Y) :
    listFormulaFV (head ++ (tail ++ [X])) ⊆
    listFormulaFV (head ++ (tail ++ [Y])) := by
-- BEGIN PROOF
  intro z ⟨F, hFm, hFs⟩
  rcases List.mem_append.mp hFm with h | h
  · exact ⟨F, List.mem_append_left _ h, hFs⟩
  · rcases List.mem_append.mp h with h' | h'
    · exact ⟨F, List.mem_append_right _ (List.mem_append_left _ h'), hFs⟩
    · rcases List.mem_cons.mp h' with heq | h''
      · subst heq; exact ⟨Y, List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)), hSub z hFs⟩
      · simp at h''
-- FV replace with fresh variable helpers
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaFV_snoc_replace_fresh {L : Language}
    {X Y : FormulaN L} {head tail other : List (FormulaN L)} {y : Nat}
    (hSub : formulaFVN X ⊆ formulaFVN Y ∪ Set.singleton y)
    (hFresh : ∀ F ∈ other, y ∉ formulaFVN F) :
    ∀ v, (listFormulaFV (head ++ (tail ++ [X])) ∩ listFormulaFV other) v →
         (listFormulaFV (head ++ (tail ++ [Y])) ∩ listFormulaFV other) v := by
-- BEGIN PROOF
  intro v ⟨⟨F, hFm, hFv⟩, hR⟩
  constructor
  · rcases List.mem_append.mp hFm with h | h
    · exact ⟨F, List.mem_append_left _ h, hFv⟩
    · rcases List.mem_append.mp h with h' | h'
      · exact ⟨F, List.mem_append_right _ (List.mem_append_left _ h'), hFv⟩
      · rcases List.mem_cons.mp h' with heq | h''
        · subst heq
          rcases hSub v hFv with hY | hSing
          · exact ⟨Y, List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)), hY⟩
          · exfalso
            obtain ⟨G, hGm, hGv⟩ := hR
            exact hFresh G hGm (hSing ▸ hGv)
        · simp at h''
  · exact hR
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaFV_cons_replace_fresh {L : Language}
    {X Y : FormulaN L} {rest tail other : List (FormulaN L)} {y : Nat}
    (hSub : formulaFVN X ⊆ formulaFVN Y ∪ Set.singleton y)
    (hFresh : ∀ F ∈ other, y ∉ formulaFVN F) :
    ∀ v, (listFormulaFV ((X :: rest) ++ tail) ∩ listFormulaFV other) v →
         (listFormulaFV ((Y :: rest) ++ tail) ∩ listFormulaFV other) v := by
-- BEGIN PROOF
  intro v ⟨⟨F, hFm, hFv⟩, hR⟩
  constructor
  · rcases List.mem_append.mp hFm with h | h
    · rcases List.mem_cons.mp h with heq | h'
      · subst heq
        rcases hSub v hFv with hY | hSing
        · exact ⟨Y, List.mem_append_left _ (List.Mem.head _), hY⟩
        · exfalso
          obtain ⟨G, hGm, hGv⟩ := hR
          exact hFresh G hGm (hSing ▸ hGv)
      · exact ⟨F, List.mem_append_left _ (List.Mem.tail _ h'), hFv⟩
    · exact ⟨F, List.mem_append_right _ h, hFv⟩
  · exact hR
-- IsInterpolant symbol monotonicity helpers
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem isInterpolant_symbol_mono_right {L : Language} {s : Sequent L}
    {p : SequentPartition s} {C : FormulaN L}
    {l : List (FormulaN L)}
    (hPred : listFormulaPredSymbols l ⊆ listFormulaPredSymbols (p.gamma1 ++ p.delta1))
    (hConst : listFormulaConstSymbols l ⊆ listFormulaConstSymbols (p.gamma1 ++ p.delta1))
    (hFV : listFormulaFV l ⊆ listFormulaFV (p.gamma1 ++ p.delta1))
    (hPC : formulaPredSymbolsN C ⊆ listFormulaPredSymbols l ∩ listFormulaPredSymbols (p.gamma2 ++ p.delta2))
    (hCC : formulaConstSymbolsN C ⊆ listFormulaConstSymbols l ∩ listFormulaConstSymbols (p.gamma2 ++ p.delta2))
    (hFC : formulaFVN C ⊆ listFormulaFV l ∩ listFormulaFV (p.gamma2 ++ p.delta2)) :
    (formulaPredSymbolsN C ⊆ listFormulaPredSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaPredSymbols (p.gamma2 ++ p.delta2)) ∧
    (formulaConstSymbolsN C ⊆ listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaConstSymbols (p.gamma2 ++ p.delta2)) ∧
    (formulaFVN C ⊆ listFormulaFV (p.gamma1 ++ p.delta1) ∩ listFormulaFV (p.gamma2 ++ p.delta2)) :=
-- BEGIN PROOF
  ⟨fun x hx => inter_mono_right hPred x (hPC x hx),
   fun x hx => inter_mono_right hConst x (hCC x hx),
   fun x hx => inter_mono_right hFV x (hFC x hx)⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem isInterpolant_symbol_mono_left {L : Language} {s : Sequent L}
    {p : SequentPartition s} {C : FormulaN L}
    {l : List (FormulaN L)}
    (hPred : listFormulaPredSymbols l ⊆ listFormulaPredSymbols (p.gamma2 ++ p.delta2))
    (hConst : listFormulaConstSymbols l ⊆ listFormulaConstSymbols (p.gamma2 ++ p.delta2))
    (hFV : listFormulaFV l ⊆ listFormulaFV (p.gamma2 ++ p.delta2))
    (hPC : formulaPredSymbolsN C ⊆ listFormulaPredSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaPredSymbols l)
    (hCC : formulaConstSymbolsN C ⊆ listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaConstSymbols l)
    (hFC : formulaFVN C ⊆ listFormulaFV (p.gamma1 ++ p.delta1) ∩ listFormulaFV l) :
    (formulaPredSymbolsN C ⊆ listFormulaPredSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaPredSymbols (p.gamma2 ++ p.delta2)) ∧
    (formulaConstSymbolsN C ⊆ listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩ listFormulaConstSymbols (p.gamma2 ++ p.delta2)) ∧
    (formulaFVN C ⊆ listFormulaFV (p.gamma1 ++ p.delta1) ∩ listFormulaFV (p.gamma2 ++ p.delta2)) :=
-- BEGIN PROOF
  ⟨fun x hx => inter_mono_left hPred x (hPC x hx),
   fun x hx => inter_mono_left hConst x (hCC x hx),
   fun x hx => inter_mono_left hFV x (hFC x hx)⟩
-- ===================================================================
-- Additional connective symbol subset lemmas
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_disj_left {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN A ⊆ formulaConstSymbolsN (.disj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_disj_right {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN B ⊆ formulaConstSymbolsN (.disj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_disj_left {L : Language} (A B : FormulaN L) :
    formulaFVN A ⊆ formulaFVN (.disj A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_disj_right {L : Language} (A B : FormulaN L) :
    formulaFVN B ⊆ formulaFVN (.disj A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_impl_left {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN A ⊆ formulaPredSymbolsN (.impl A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_impl_right {L : Language} (A B : FormulaN L) :
    formulaPredSymbolsN B ⊆ formulaPredSymbolsN (.impl A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_impl_left {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN A ⊆ formulaConstSymbolsN (.impl A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_impl_right {L : Language} (A B : FormulaN L) :
    formulaConstSymbolsN B ⊆ formulaConstSymbolsN (.impl A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_impl_left {L : Language} (A B : FormulaN L) :
    formulaFVN A ⊆ formulaFVN (.impl A B) := fun x hx => Or.inl hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_impl_right {L : Language} (A B : FormulaN L) :
    formulaFVN B ⊆ formulaFVN (.impl A B) := fun x hx => Or.inr hx
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_neg {L : Language} (A : FormulaN L) :
    formulaConstSymbolsN A = formulaConstSymbolsN (.neg A) := by simp only [formulaConstSymbolsN]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_neg {L : Language} (A : FormulaN L) :
    formulaFVN A = formulaFVN (.neg A) := by rfl
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_all {L : Language} (x : Nat) (A : FormulaN L) :
    formulaConstSymbolsN A = formulaConstSymbolsN (.all x A) := by simp only [formulaConstSymbolsN]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_ex {L : Language} (x : Nat) (A : FormulaN L) :
    formulaConstSymbolsN A = formulaConstSymbolsN (.ex x A) := by simp only [formulaConstSymbolsN]
-- ===================================================================
-- Monotonicity helpers (formula-level sub)
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem inter_mono_both {α : Type} {A A' B B' : Set α}
    (hAA' : A ⊆ A') (hBB' : B ⊆ B') : A ∩ B ⊆ A' ∩ B' :=
-- BEGIN PROOF
  fun x hx => ⟨hAA' x hx.1, hBB' x hx.2⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaPredSymbols_formula_sub {L : Language}
    {l l' : List (FormulaN L)}
    (h : ∀ F, F ∈ l → ∃ G ∈ l', formulaPredSymbolsN F ⊆ formulaPredSymbolsN G) :
    listFormulaPredSymbols l ⊆ listFormulaPredSymbols l' := by
-- BEGIN PROOF
  intro x ⟨F, hFm, hFp⟩
  obtain ⟨G, hGm, hGp⟩ := h F hFm
  exact ⟨G, hGm, hGp x hFp⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaConstSymbols_formula_sub {L : Language}
    {l l' : List (FormulaN L)}
    (h : ∀ F, F ∈ l → ∃ G ∈ l', formulaConstSymbolsN F ⊆ formulaConstSymbolsN G) :
    listFormulaConstSymbols l ⊆ listFormulaConstSymbols l' := by
-- BEGIN PROOF
  intro x ⟨F, hFm, hFc⟩
  obtain ⟨G, hGm, hGc⟩ := h F hFm
  exact ⟨G, hGm, hGc x hFc⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem listFormulaFV_formula_sub {L : Language}
    {l l' : List (FormulaN L)}
    (h : ∀ F, F ∈ l → ∃ G ∈ l', formulaFVN F ⊆ formulaFVN G) :
    listFormulaFV l ⊆ listFormulaFV l' := by
-- BEGIN PROOF
  intro x ⟨F, hFm, hFv⟩
  obtain ⟨G, hGm, hGv⟩ := h F hFm
  exact ⟨G, hGm, hGv x hFv⟩
-- ===================================================================
-- eliminateBot infrastructure
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_formulaSubst_comm {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (t : Term L) (x : Nat) (P : L.predSymbols) (v : Nat)
    (hv : v ∉ termFV t) :
    eliminateBot botP hBotArity (formulaSubstN A t x) P v =
      formulaSubstN (eliminateBot botP hBotArity A P v) t x := sorry -- DEBT(Section 6.5.2, LK⊥: translation of an LK⊥-proof to an LK-proof with ⊥ replaced by a fresh atom; proof pending)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBotList_append {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (l1 l2 : List (FormulaN L)) (P : L.predSymbols) (v : Nat) :
    eliminateBotList botP hBotArity (l1 ++ l2) P v =
      eliminateBotList botP hBotArity l1 P v ++ eliminateBotList botP hBotArity l2 P v := by
-- BEGIN PROOF
  simp [eliminateBotList, List.map_append]
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBotList_singleton {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (A : FormulaN L) (P : L.predSymbols) (v : Nat) :
    eliminateBotList botP hBotArity [A] P v = [eliminateBot botP hBotArity A P v] := rfl
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBotList_cons {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (A : FormulaN L) (l : List (FormulaN L)) (P : L.predSymbols) (v : Nat) :
    eliminateBotList botP hBotArity (A :: l) P v =
      eliminateBot botP hBotArity A P v :: eliminateBotList botP hBotArity l P v := rfl
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_isFreeFor {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (A : FormulaN L)
    (t : Term L) (x v : Nat) (P : L.predSymbols)
    (hfree : isFreeForN t x A) (hv : v ∉ termFV t) :
    isFreeForN t x (eliminateBot botP hBotArity A P v) := sorry -- DEBT(Section 6.5.2, LK⊥: translation of an LK⊥-proof to an LK-proof with ⊥ replaced by a fresh atom; proof pending)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem eliminateBot_preserves_eigenfresh {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (F : FormulaN L) (P : L.predSymbols) (v y : Nat)
    (hfresh : y ∉ formulaFVN F) :
    y ∉ formulaFVN (eliminateBot botP hBotArity F P v) := by
-- BEGIN PROOF
  intro hcontra
  exact hfresh
    (@eliminateBot_fv_sub L botP hBotArity F P v y hcontra)
-- lkBotWellFormed_eliminateBot_folkProvable (adapted to indexed trees)
-- ATTACH-BLOCKER: section variables: helper requires front context
set_option maxHeartbeats 1200000 in
theorem lkBotWellFormed_eliminateBot_folkProvable {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (P : L.predSymbols) (v : Nat)
    {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s) :
    folkProvable (eliminateBotSeq botP hBotArity s P v) := sorry -- DEBT(Section 6.5.2, LK⊥: translation of an LK⊥-proof to an LK-proof with ⊥ replaced by a fresh atom; proof pending)
-- ===================================================================
-- VarFresh infrastructure
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem foldl_max_init_le (init : Nat) (l : List Nat) :
    init ≤ l.foldl Nat.max init := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd t ih => exact Nat.le_trans (Nat.le_max_left init hd) (ih _)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem foldl_max_mem_le (l : List Nat) (init : Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl Nat.max init := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => simp at hx
  | cons hd t ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_init_le _ _)
    · exact ih (Nat.max init hd) ht
-- ATTACH-BLOCKER: section variables: helper requires front context
def termMaxVar {L : Language} : Term L → Nat
  | .var i => i
  | .const _ => 0
  | .func _ ts => (List.ofFn fun i => termMaxVar (ts i)).foldl Nat.max 0
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termFV_bounded {L : Language} (t : Term L) (v : Nat) (hv : termFV t v) :
    v ≤ termMaxVar t := by
-- BEGIN PROOF
  induction t with
  | var i => change v = i at hv; subst hv; exact Nat.le_refl _
  | const _ => change False at hv; exact absurd hv id
  | func _ ts ih =>
    change ∃ i, termFV (ts i) v at hv; obtain ⟨i, hi⟩ := hv
    exact Nat.le_trans (ih i hi) (foldl_max_mem_le _ 0 _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termFV_gt_maxVar {L : Language} (t : Term L) (v : Nat) (hv : v > termMaxVar t) :
    v ∉ termFV t :=
-- BEGIN PROOF
  fun h => Nat.not_lt.mpr (termFV_bounded t v h) hv
-- ===================================================================
-- Max var in tree
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
def formulaAllMaxVar {L : Language} : FormulaN L → Nat
  | .predN _ ts => (List.ofFn fun i => termMaxVar (ts i)).foldl Nat.max 0
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .conj A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .disj A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .impl A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .neg A => formulaAllMaxVar A
  | .all x A => Nat.max x (formulaAllMaxVar A)
  | .ex x A => Nat.max x (formulaAllMaxVar A)
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaAllMaxVar_gt_no_fv {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v > formulaAllMaxVar A) : v ∉ formulaFVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ ts =>
    intro h; obtain ⟨i, hi⟩ := h
    exact Nat.not_lt.mpr (termFV_bounded (ts i) v hi)
      (Nat.lt_of_le_of_lt (foldl_max_mem_le _ 0 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) hv)
  | eq_ _ t1 t2 =>
    intro h; rcases h with h1 | h2
    · exact Nat.not_lt.mpr (termFV_bounded t1 v h1)
        (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv)
    · exact Nat.not_lt.mpr (termFV_bounded t2 v h2)
        (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv)
  | conj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | disj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | impl A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | neg A ih => exact ih hv
  | all x A ih =>
    intro ⟨hA, _⟩; exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
  | ex x A ih =>
    intro ⟨hA, _⟩; exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaAllMaxVar_gt_no_bv {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v > formulaAllMaxVar A) : v ∉ formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => intro h; exact h
  | eq_ _ _ => intro h; exact h
  | conj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | disj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | impl A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | neg A ih => exact ih hv
  | all x A ih =>
    intro h; rcases h with hA | hx
    · exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
    · subst hx; exact Nat.not_lt.mpr (Nat.le_max_left _ _) hv
  | ex x A ih =>
    intro h; rcases h with hA | hx
    · exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
    · subst hx; exact Nat.not_lt.mpr (Nat.le_max_left _ _) hv
-- ATTACH-BLOCKER: section variables: helper requires front context
def listFormulaAllMaxVar {L : Language} (fs : List (FormulaN L)) : Nat :=
  (fs.map formulaAllMaxVar).foldl Nat.max 0
-- ATTACH-BLOCKER: section variables: helper requires front context
def sequentAllMaxVar {L : Language} (s : Sequent L) : Nat :=
  Nat.max (listFormulaAllMaxVar s.antecedent) (listFormulaAllMaxVar s.succedent)
-- ===================================================================
-- Term symbol lists and sequential substitution
-- ===================================================================
-- ATTACH-BLOCKER: section variables: helper requires front context
def termConstList {L : Language} : Term L → List L.constSymbols
  | .var _ => []
  | .const c => [c]
  | .func _ ts => (List.ofFn fun i => termConstList (ts i)).flatten
-- ATTACH-BLOCKER: section variables: helper requires front context
def termFVList {L : Language} : Term L → List Nat
  | .var x => [x]
  | .const _ => []
  | .func _ ts => (List.ofFn fun i => termFVList (ts i)).flatten
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termConstList_mem {L : Language} (t : Term L) (c : L.constSymbols) :
    c ∈ termConstList t ↔ termConstSymbols t c := by
-- BEGIN PROOF
  induction t with
  | var _ =>
    constructor
    · intro h; simp [termConstList] at h
    · intro h; exact absurd h id
  | const d =>
    constructor
    · intro h; simp only [termConstList, List.mem_singleton] at h; exact h
    · intro h; simp only [termConstList, List.mem_singleton]; exact h
  | func f ts ih =>
    simp only [termConstList, List.mem_flatten, List.mem_ofFn, termConstSymbols]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hm⟩; exact ⟨i, (ih i).mp hm⟩
    · rintro ⟨i, hi⟩; exact ⟨_, ⟨i, rfl⟩, (ih i).mpr hi⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem termFVList_mem {L : Language} (t : Term L) (v : Nat) :
    v ∈ termFVList t ↔ termFV t v := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp only [termFVList, List.mem_singleton]
    show v = x ↔ Set.singleton x v
    exact ⟨fun h => h, fun h => h⟩
  | const _ =>
    constructor
    · intro h; simp [termFVList] at h
    · intro h; exact absurd h id
  | func f ts ih =>
    simp only [termFVList, List.mem_flatten, List.mem_ofFn]
    show (∃ l, (∃ i, termFVList (ts i) = l) ∧ v ∈ l) ↔ ∃ i, termFV (ts i) v
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hm⟩; exact ⟨i, (ih i).mp hm⟩
    · rintro ⟨i, hi⟩; exact ⟨_, ⟨i, rfl⟩, (ih i).mpr hi⟩
-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def formulaSubstConsts {L : Language}
    (F : FormulaN L) (cs : List L.constSymbols) (zs : List Nat) : FormulaN L :=
  match cs, zs with
  | [], _ => F
  | _, [] => F
  | c :: cs', z :: zs' => formulaSubstConsts (formulaSubstConst F z c) cs' zs'
-- ATTACH-BLOCKER: section variables: helper requires front context
def formulaSubstVars {L : Language}
    (F : FormulaN L) (vs : List Nat) (zs : List Nat) : FormulaN L :=
  match vs, zs with
  | [], _ => F
  | _, [] => F
  | v :: vs', z :: zs' => formulaSubstVars (formulaSubstN F (.var z) v) vs' zs'
@[blueprint "chap6__definition_6_5_1"]
def FormulaN.allList {L : Language} (vars : List Nat) (F : FormulaN L) : FormulaN L :=
  vars.foldr FormulaN.all F
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaPredSymbolsN_allList {L : Language} (vars : List Nat) (F : FormulaN L) :
    formulaPredSymbolsN (FormulaN.allList vars F) = formulaPredSymbolsN F := by
-- BEGIN PROOF
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    simp only [FormulaN.allList, List.foldr_cons]
    rw [← formulaPredSymbolsN_all v]; exact ih
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaConstSymbolsN_allList {L : Language} (vars : List Nat) (F : FormulaN L) :
    formulaConstSymbolsN (FormulaN.allList vars F) = formulaConstSymbolsN F := by
-- BEGIN PROOF
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    simp only [FormulaN.allList, List.foldr_cons]
    rw [← formulaConstSymbolsN_all v]; exact ih
-- ATTACH-BLOCKER: section variables: helper requires front context
theorem formulaFV_allList_iff {L : Language} (vars : List Nat) (F : FormulaN L) (v : Nat) :
    formulaFVN (FormulaN.allList vars F) v ↔ formulaFVN F v ∧ v ∉ vars := by
-- BEGIN PROOF
  induction vars with
  | nil =>
    simp only [FormulaN.allList, List.foldr_nil, List.not_mem_nil, and_true, not_false_eq_true]
  | cons x xs ih =>
    constructor
    · intro hv
      change (formulaFVN (List.foldr FormulaN.all F xs) v ∧ ¬ Set.singleton x v) at hv
      have hxs := ih.mp hv.1
      exact ⟨hxs.1, fun h => by simp [List.mem_cons] at h; exact h.elim (fun heq => hv.2 heq) (fun hm => hxs.2 hm)⟩
    · intro ⟨hF, hNotIn⟩
      show formulaFVN (List.foldr FormulaN.all F xs) v ∧ ¬ Set.singleton x v
      exact ⟨ih.mpr ⟨hF, fun hm => hNotIn (List.mem_cons.mpr (Or.inr hm))⟩,
             fun heq => hNotIn (List.mem_cons.mpr (Or.inl heq))⟩
end LCS.CutElim.Interpolation
end

