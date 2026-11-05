import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair
import LCS.CutElim.Interpolation.QuantifierCases
import LCS.CutElim.Interpolation.KeyLemma

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
namespace CraigFreshBot

/-- Pointwise lowering for contexts. -/
def freshLowerList {L : Language} (R : FormulaN L)
    (fs : List (FormulaN (FreshBotLanguage L))) : List (FormulaN L) :=
  fs.map (freshLowerFormula R)

/-- Pointwise lowering of both sides of a sequent. -/
def freshLowerSequent {L : Language} (R : FormulaN L)
    (s : Sequent (FreshBotLanguage L)) : Sequent L :=
  { antecedent := freshLowerList R s.antecedent
    succedent := freshLowerList R s.succedent }

@[simp]
theorem freshLowerTerm_lift {L : Language} (t : Term L) :
    freshLowerTerm (freshLiftTerm t) = t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [freshLiftTerm, freshLowerTerm]
    congr 1
    funext i
    exact ih i

@[simp]
theorem freshLowerFormula_lift {L : Language}
    (R A : FormulaN L) :
    freshLowerFormula R (freshLiftFormula A) = A := by
  induction A with
  | predN P ts =>
    simp only [freshLiftFormula, freshLowerFormula]
    congr 1
    funext i
    exact freshLowerTerm_lift (ts i)
  | eq_ _ t₁ t₂ =>
    simp only [freshLiftFormula, freshLowerFormula, freshLowerTerm_lift]
  | neg A ih => simp only [freshLiftFormula, freshLowerFormula, ih]
  | conj A B ihA ihB =>
    simp only [freshLiftFormula, freshLowerFormula, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [freshLiftFormula, freshLowerFormula, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [freshLiftFormula, freshLowerFormula, ihA, ihB]
  | all x A ih => simp only [freshLiftFormula, freshLowerFormula, ih]
  | ex x A ih => simp only [freshLiftFormula, freshLowerFormula, ih]

@[simp]
theorem freshLowerFormula_freshBot {L : Language} (R : FormulaN L) :
    freshLowerFormula R
      (botFormula (freshBot (L := L)) (freshBot_arity (L := L))) = R :=
  rfl

@[simp]
theorem freshLowerList_lift {L : Language}
    (R : FormulaN L) (fs : List (FormulaN L)) :
    freshLowerList R (freshLiftList fs) = fs := by
  induction fs with
  | nil => rfl
  | cons A fs ih =>
    change
      freshLowerFormula R (freshLiftFormula A) ::
          freshLowerList R (freshLiftList fs) =
        A :: fs
    rw [freshLowerFormula_lift, ih]

@[simp]
theorem freshLowerSequent_lift {L : Language}
    (R : FormulaN L) (s : Sequent L) :
    freshLowerSequent R (freshLiftSequent s) = s := by
  cases s
  simp only [freshLiftSequent, freshLowerSequent, freshLowerList_lift]

theorem freshLiftTerm_subst {L : Language}
    (u t : Term L) (x : Nat) :
    freshLiftTerm (termSubst u t x) =
      termSubst (freshLiftTerm u) (freshLiftTerm t) x := by
  induction u with
  | var y => simp only [termSubst, freshLiftTerm]; split <;> rfl
  | const c => rfl
  | func f ts ih =>
    simp only [termSubst, freshLiftTerm]
    congr 1
    funext i
    exact ih i

theorem freshLowerTerm_subst {L : Language}
    (u t : Term (FreshBotLanguage L)) (x : Nat) :
    freshLowerTerm (termSubst u t x) =
      termSubst (freshLowerTerm u) (freshLowerTerm t) x := by
  induction u with
  | var y => simp only [termSubst, freshLowerTerm]; split <;> rfl
  | const c => rfl
  | func f ts ih =>
    simp only [termSubst, freshLowerTerm]
    congr 1
    funext i
    exact ih i

@[simp]
theorem freshLiftTerm_fv {L : Language} (t : Term L) :
    termFV (freshLiftTerm t) = termFV t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [freshLiftTerm, termFV]
    congr
    funext i
    exact ih i

@[simp]
theorem freshLowerTerm_fv {L : Language}
    (t : Term (FreshBotLanguage L)) :
    termFV (freshLowerTerm t) = termFV t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [freshLowerTerm, termFV]
    congr
    funext i
    exact ih i

@[simp]
theorem freshLiftTerm_constSymbols {L : Language} (t : Term L) :
    termConstSymbols (freshLiftTerm t) = termConstSymbols t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    funext c
    apply propext
    simp only [freshLiftTerm, termConstSymbols]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [ih i] using hi
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [ih i] using hi

@[simp]
theorem freshLowerTerm_constSymbols {L : Language}
    (t : Term (FreshBotLanguage L)) :
    termConstSymbols (freshLowerTerm t) = termConstSymbols t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    funext c
    apply propext
    simp only [freshLowerTerm, termConstSymbols]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [ih i] using hi
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [ih i] using hi

theorem freshLiftFormula_subst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    freshLiftFormula (formulaSubstN A t x) =
      formulaSubstN (freshLiftFormula A) (freshLiftTerm t) x := by
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, freshLiftFormula]
    congr 1
    funext i
    exact freshLiftTerm_subst (ts i) t x
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstN, freshLiftFormula, freshLiftTerm_subst]
  | neg A ih => simp only [formulaSubstN, freshLiftFormula, ih]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, freshLiftFormula, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [formulaSubstN, freshLiftFormula, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [formulaSubstN, freshLiftFormula, ihA, ihB]
  | all y A ih =>
    by_cases hxy : x != y
    · simp [formulaSubstN, freshLiftFormula, hxy, ih]
    · simp [formulaSubstN, freshLiftFormula, hxy]
  | ex y A ih =>
    by_cases hxy : x != y
    · simp [formulaSubstN, freshLiftFormula, hxy, ih]
    · simp [formulaSubstN, freshLiftFormula, hxy]

@[simp]
theorem freshLiftFormula_fv {L : Language} (A : FormulaN L) :
    formulaFVN (freshLiftFormula A) = formulaFVN A := by
  induction A with
  | predN P ts =>
    simp only [freshLiftFormula, formulaFVN]
    congr
    funext i
    exact freshLiftTerm_fv (ts i)
  | eq_ _ t₁ t₂ =>
    simp only [freshLiftFormula, formulaFVN, freshLiftTerm_fv]
  | neg A ih => simp only [freshLiftFormula, formulaFVN, ih]
  | conj A B ihA ihB =>
    simp only [freshLiftFormula, formulaFVN, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [freshLiftFormula, formulaFVN, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [freshLiftFormula, formulaFVN, ihA, ihB]
  | all x A ih => simp only [freshLiftFormula, formulaFVN, ih]
  | ex x A ih => simp only [freshLiftFormula, formulaFVN, ih]

@[simp]
theorem freshLiftFormula_constSymbols {L : Language} (A : FormulaN L) :
    formulaConstSymbolsN (freshLiftFormula A) =
      formulaConstSymbolsN A := by
  induction A with
  | predN P ts =>
    funext c
    apply propext
    simp only [freshLiftFormula, formulaConstSymbolsN]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [freshLiftTerm_constSymbols] using hi
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [freshLiftTerm_constSymbols] using hi
  | eq_ _ t₁ t₂ =>
    simp only [freshLiftFormula, formulaConstSymbolsN,
      freshLiftTerm_constSymbols]
    rfl
  | neg A ih => simp only [freshLiftFormula, formulaConstSymbolsN, ih]; rfl
  | conj A B ihA ihB =>
    simp only [freshLiftFormula, formulaConstSymbolsN, ihA, ihB]
    rfl
  | disj A B ihA ihB =>
    simp only [freshLiftFormula, formulaConstSymbolsN, ihA, ihB]
    rfl
  | impl A B ihA ihB =>
    simp only [freshLiftFormula, formulaConstSymbolsN, ihA, ihB]
    rfl
  | all x A ih => simp only [freshLiftFormula, formulaConstSymbolsN, ih]; rfl
  | ex x A ih => simp only [freshLiftFormula, formulaConstSymbolsN, ih]; rfl

@[simp]
theorem freshLiftFormula_predSymbols_inl {L : Language}
    (A : FormulaN L) (Q : L.predSymbols) :
    formulaPredSymbolsN (freshLiftFormula A) (.inl Q) ↔
      formulaPredSymbolsN A Q := by
  induction A with
  | predN P ts =>
    simp only [freshLiftFormula, formulaPredSymbolsN]
    constructor
    · exact Sum.inl.inj
    · exact congrArg Sum.inl
  | eq_ _ t₁ t₂ =>
    simp only [freshLiftFormula, formulaPredSymbolsN, Set.empty]
  | neg A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih
  | conj A B ihA ihB =>
    change
      formulaPredSymbolsN (freshLiftFormula A) (.inl Q) ∨
          formulaPredSymbolsN (freshLiftFormula B) (.inl Q) ↔
        formulaPredSymbolsN A Q ∨ formulaPredSymbolsN B Q
    exact or_congr ihA ihB
  | disj A B ihA ihB =>
    change
      formulaPredSymbolsN (freshLiftFormula A) (.inl Q) ∨
          formulaPredSymbolsN (freshLiftFormula B) (.inl Q) ↔
        formulaPredSymbolsN A Q ∨ formulaPredSymbolsN B Q
    exact or_congr ihA ihB
  | impl A B ihA ihB =>
    change
      formulaPredSymbolsN (freshLiftFormula A) (.inl Q) ∨
          formulaPredSymbolsN (freshLiftFormula B) (.inl Q) ↔
        formulaPredSymbolsN A Q ∨ formulaPredSymbolsN B Q
    exact or_congr ihA ihB
  | all x A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih
  | ex x A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih

@[simp]
theorem freshLiftFormula_freshBot {L : Language} (A : FormulaN L) :
    ¬ formulaPredSymbolsN (freshLiftFormula A) (freshBot (L := L)) := by
  induction A with
  | predN P ts => simp [freshLiftFormula, formulaPredSymbolsN, freshBot]
  | eq_ _ t₁ t₂ =>
    simp only [freshLiftFormula, formulaPredSymbolsN, Set.empty, not_false_eq_true]
  | neg A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih
  | conj A B ihA ihB =>
    change ¬(formulaPredSymbolsN (freshLiftFormula A) freshBot ∨
      formulaPredSymbolsN (freshLiftFormula B) freshBot)
    exact not_or.mpr ⟨ihA, ihB⟩
  | disj A B ihA ihB =>
    change ¬(formulaPredSymbolsN (freshLiftFormula A) freshBot ∨
      formulaPredSymbolsN (freshLiftFormula B) freshBot)
    exact not_or.mpr ⟨ihA, ihB⟩
  | impl A B ihA ihB =>
    change ¬(formulaPredSymbolsN (freshLiftFormula A) freshBot ∨
      formulaPredSymbolsN (freshLiftFormula B) freshBot)
    exact not_or.mpr ⟨ihA, ihB⟩
  | all x A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih
  | ex x A ih => simpa only [freshLiftFormula, formulaPredSymbolsN] using ih

@[simp]
theorem freshLiftFormula_noEq {L : Language} (A : FormulaN L) :
    formulaNoEq (freshLiftFormula A) ↔ formulaNoEq A := by
  induction A with
  | predN P ts => rfl
  | eq_ hL t₁ t₂ => rfl
  | neg A ih => simpa only [freshLiftFormula, formulaNoEq] using ih
  | conj A B ihA ihB =>
    simpa only [freshLiftFormula, formulaNoEq] using and_congr ihA ihB
  | disj A B ihA ihB =>
    simpa only [freshLiftFormula, formulaNoEq] using and_congr ihA ihB
  | impl A B ihA ihB =>
    simpa only [freshLiftFormula, formulaNoEq] using and_congr ihA ihB
  | all x A ih => simpa only [freshLiftFormula, formulaNoEq] using ih
  | ex x A ih => simpa only [freshLiftFormula, formulaNoEq] using ih

@[simp]
theorem freshLiftFormula_isFreeFor {L : Language}
    (t : Term L) (x : Nat) (A : FormulaN L) :
    isFreeForN (freshLiftTerm t) x (freshLiftFormula A) ↔
      isFreeForN t x A := by
  induction A with
  | predN P ts => rfl
  | eq_ hL t₁ t₂ => rfl
  | neg A ih => simpa only [freshLiftFormula, isFreeForN] using ih
  | conj A B ihA ihB =>
    simpa only [freshLiftFormula, isFreeForN] using and_congr ihA ihB
  | disj A B ihA ihB =>
    simpa only [freshLiftFormula, isFreeForN] using and_congr ihA ihB
  | impl A B ihA ihB =>
    simpa only [freshLiftFormula, isFreeForN] using and_congr ihA ihB
  | all y A ih =>
    simp only [freshLiftFormula, isFreeForN, freshLiftTerm_fv, ih]
  | ex y A ih =>
    simp only [freshLiftFormula, isFreeForN, freshLiftTerm_fv, ih]

@[simp]
theorem freshLiftList_predSymbols_inl {L : Language}
    (fs : List (FormulaN L)) (Q : L.predSymbols) :
    listFormulaPredSymbols (freshLiftList fs) (.inl Q) ↔
      listFormulaPredSymbols fs Q := by
  constructor
  · rintro ⟨A, hA, hQ⟩
    simp only [freshLiftList] at hA
    rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
    exact ⟨B, hB, (freshLiftFormula_predSymbols_inl B Q).mp hQ⟩
  · rintro ⟨A, hA, hQ⟩
    exact ⟨freshLiftFormula A,
      List.mem_map.mpr ⟨A, hA, rfl⟩,
      (freshLiftFormula_predSymbols_inl A Q).mpr hQ⟩

@[simp]
theorem freshLiftList_freshBot {L : Language}
    (fs : List (FormulaN L)) :
    ¬ listFormulaPredSymbols (freshLiftList fs) (freshBot (L := L)) := by
  rintro ⟨A, hA, hBot⟩
  simp only [freshLiftList] at hA
  rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
  exact freshLiftFormula_freshBot B hBot

@[simp]
theorem freshLiftList_constSymbols {L : Language}
    (fs : List (FormulaN L)) :
    listFormulaConstSymbols (freshLiftList fs) =
      listFormulaConstSymbols fs := by
  funext c
  apply propext
  constructor
  · rintro ⟨A, hA, hc⟩
    simp only [freshLiftList] at hA
    rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
    exact ⟨B, hB, by
      simpa only [freshLiftFormula_constSymbols] using hc⟩
  · rintro ⟨A, hA, hc⟩
    exact ⟨freshLiftFormula A,
      List.mem_map.mpr ⟨A, hA, rfl⟩,
      by simpa only [freshLiftFormula_constSymbols] using hc⟩

@[simp]
theorem freshLiftList_fv {L : Language}
    (fs : List (FormulaN L)) :
    listFormulaFV (freshLiftList fs) = listFormulaFV fs := by
  funext v
  apply propext
  constructor
  · rintro ⟨A, hA, hv⟩
    simp only [freshLiftList] at hA
    rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
    exact ⟨B, hB, by simpa only [freshLiftFormula_fv] using hv⟩
  · rintro ⟨A, hA, hv⟩
    exact ⟨freshLiftFormula A,
      List.mem_map.mpr ⟨A, hA, rfl⟩,
      by simpa only [freshLiftFormula_fv] using hv⟩

@[simp]
theorem freshLiftList_noEq {L : Language}
    (fs : List (FormulaN L)) :
    (∀ A ∈ freshLiftList fs, formulaNoEq A) ↔
      ∀ A ∈ fs, formulaNoEq A := by
  constructor
  · intro h A hA
    exact (freshLiftFormula_noEq A).mp
      (h (freshLiftFormula A) (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · intro h A hA
    simp only [freshLiftList] at hA
    rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
    exact (freshLiftFormula_noEq B).mpr (h B hB)

-- ===================================================================
-- Internal Craig helper: lifting indexed LK derivations
-- ===================================================================

/-- Lifting preserves the exact axiom sequent, rather than merely producing
an extension-language axiom with an unrelated conclusion. -/
theorem freshLift_isFOLKAxiom {L : Language} (s : Sequent L)
    (h : isFOLKAxiom s) :
    isFOLKAxiom (freshLiftSequent s) := by
  rcases h with ⟨A, hΓ, hΔ⟩
  refine ⟨freshLiftFormula A, ?_, ?_⟩
  · simp only [freshLiftSequent, hΓ, freshLiftList,
      List.map_cons, List.map_nil]
  · simp only [freshLiftSequent, hΔ, freshLiftList,
      List.map_cons, List.map_nil]

end CraigFreshBot
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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot
section
variable (L : Language)

def freshLift_allRight
    (y : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var
      y) x A)
    : FOLKStep1 (freshLiftSequent (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var y) x]))) (freshLiftSequent
      (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))) := by
  have hfresh' : ∀ F ∈ (Sequent.mk (freshLiftList Γ) (freshLiftList Δ ++
              [FormulaN.all x (freshLiftFormula A)])).antecedent ++
          (Sequent.mk (freshLiftList Γ) (freshLiftList Δ ++ [FormulaN.all x (freshLiftFormula A)])).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hF' : F ∈ freshLiftList ((Sequent.mk Γ (Δ ++ [FormulaN.all x A])).antecedent ++ (Sequent.mk Γ
            (Δ ++ [FormulaN.all x A])).succedent) := by
      simpa only [freshLiftList, freshLiftFormula, List.map_append, List.map_cons, List.map_nil] using hF
    simp only [freshLiftList] at hF'
    rcases List.mem_map.mp hF' with ⟨G, hG, rfl⟩
    simpa only [freshLiftFormula_fv] using hfresh G hG
  have hfreeFor' : isFreeForN (Term.var y : Term (FreshBotLanguage L)) x (freshLiftFormula A) := by
    simpa only [freshLiftTerm] using (freshLiftFormula_isFreeFor (Term.var y) x A).mpr hfreeFor
  simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
    freshLiftFormula_subst, List.map_append, List.map_cons,
    List.map_nil, freshLiftTerm] using
    (FOLKStep1.allRight y x (freshLiftFormula A) (freshLiftList Γ) (freshLiftList Δ) hfresh' hfreeFor')

def freshLift_exLeft
    (y : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y)
      x A)
    : FOLKStep1 (freshLiftSequent (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) (Δ))) (freshLiftSequent
      (Sequent.mk (FormulaN.ex x A :: Γ) (Δ))) := by
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (freshLiftFormula A) :: freshLiftList Γ)
            (freshLiftList Δ)).antecedent ++
          (Sequent.mk (FormulaN.ex x (freshLiftFormula A) :: freshLiftList Γ) (freshLiftList Δ)).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hF' : F ∈ freshLiftList ((Sequent.mk (FormulaN.ex x A :: Γ) Δ).antecedent ++
           (Sequent.mk (FormulaN.ex x A :: Γ) Δ).succedent) := by
      simpa only [freshLiftList, freshLiftFormula, List.map_append, List.map_cons] using hF
    simp only [freshLiftList] at hF'
    rcases List.mem_map.mp hF' with ⟨G, hG, rfl⟩
    simpa only [freshLiftFormula_fv] using hfresh G hG
  have hfreeFor' : isFreeForN (Term.var y : Term (FreshBotLanguage L)) x (freshLiftFormula A) := by
    simpa only [freshLiftTerm] using (freshLiftFormula_isFreeFor (Term.var y) x A).mpr hfreeFor
  simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
    freshLiftFormula_subst, List.map_cons, freshLiftTerm] using
    (FOLKStep1.exLeft y x (freshLiftFormula A) (freshLiftList Γ) (freshLiftList Δ) hfresh' hfreeFor')

end
end CraigFreshBot
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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot

/-- Lift every indexed one-premise LK rule to the fresh-bottom language.
The premise and conclusion indices are exactly the pointwise lifts of the
source indices. -/
def freshLift_folkStep1 {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) :
    FOLKStep1 (freshLiftSequent prem) (freshLiftSequent conc) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList,
      List.map_cons] using
      (FOLKStep1.weakenLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | weakenRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.weakenRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | contractLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList,
      List.map_cons] using
      (FOLKStep1.contractLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | contractRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.contractRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | exchangeLeft Γ A B Δ Λ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeLeft (freshLiftList Γ)
        (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Δ) (freshLiftList Λ))
  | exchangeRight Γ Δ A B Λ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeRight (freshLiftList Γ) (freshLiftList Δ)
        (freshLiftFormula A) (freshLiftFormula B) (freshLiftList Λ))
  | andLeftL A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_cons] using
      (FOLKStep1.andLeftL (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | andLeftR A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_cons] using
      (FOLKStep1.andLeftR (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | orRightL A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightL (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | orRightR A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightR (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | implRight A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.implRight (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | negLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | negRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | allLeft t x A Γ Δ hfree =>
    have hfree' :
        isFreeForN (freshLiftTerm t) x (freshLiftFormula A) :=
      (freshLiftFormula_isFreeFor t x A).mpr hfree
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      freshLiftFormula_subst, List.map_cons] using
      (FOLKStep1.allLeft (freshLiftTerm t) x (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ) hfree')
  | allRight y x A Γ Δ hfresh hfreeFor =>
    exact freshLift_allRight L y x A Γ Δ hfresh hfreeFor
  | exLeft y x A Γ Δ hfresh hfreeFor =>
    exact freshLift_exLeft L y x A Γ Δ hfresh hfreeFor
  | exRight t x A Γ Δ hfree =>
    have hfree' :
        isFreeForN (freshLiftTerm t) x (freshLiftFormula A) :=
      (freshLiftFormula_isFreeFor t x A).mpr hfree
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      freshLiftFormula_subst, List.map_append, List.map_cons,
      List.map_nil] using
      (FOLKStep1.exRight (freshLiftTerm t) x (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ) hfree')

private def folkStep2NoCut {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) : Prop :=
  match rule with
  | .cut .. => False
  | _ => True

def reindexFOLKStep2 {L : Language}
    {prem₁ prem₂ conc prem₁' prem₂' conc' : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (hprem₁ : prem₁ = prem₁') (hprem₂ : prem₂ = prem₂')
    (hconc : conc = conc') :
    FOLKStep2 prem₁' prem₂' conc' := by
  cases hprem₁
  cases hprem₂
  cases hconc
  exact rule

private theorem reindexFOLKStep2_noCut {L : Language}
    {prem₁ prem₂ conc prem₁' prem₂' conc' : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (hprem₁ : prem₁ = prem₁') (hprem₂ : prem₂ = prem₂')
    (hconc : conc = conc') :
    folkStep2NoCut (reindexFOLKStep2 rule hprem₁ hprem₂ hconc) ↔
      folkStep2NoCut rule := by
  cases hprem₁
  cases hprem₂
  cases hconc
  exact Iff.rfl

/-- Lift every indexed two-premise LK rule to the fresh-bottom language,
including cut. All three sequent indices are translated exactly. -/
def freshLift_folkStep2 {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2 (freshLiftSequent prem₁) (freshLiftSequent prem₂)
      (freshLiftSequent conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    let lifted := FOLKStep2.cut (freshLiftFormula A)
      (freshLiftList Γ) (freshLiftList Δ)
      (freshLiftList Λ) (freshLiftList Θ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, List.map_append])
  | andRight A B Γ Δ =>
    let lifted := FOLKStep2.andRight
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_append, List.map_cons, List.map_nil])
  | orLeft A B Γ Δ =>
    let lifted := FOLKStep2.orLeft
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_cons])
  | implLeft A B Γ Δ Λ Θ =>
    let lifted := FOLKStep2.implLeft
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
      (freshLiftList Λ) (freshLiftList Θ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_append, List.map_cons])

private theorem freshLift_folkStep2_noCut {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    folkStep2NoCut (freshLift_folkStep2 rule) ↔
      folkStep2NoCut rule := by
  cases rule <;>
    dsimp only [freshLift_folkStep2] <;>
    refine (reindexFOLKStep2_noCut _ _ _ _).trans ?_ <;>
    rfl

private theorem folkProofTree_twoPremise_isCutFree {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (t₁ : FOLKProofTree prem₁) (t₂ : FOLKProofTree prem₂) :
    (FOLKProofTree.twoPremise rule t₁ t₂).isCutFree ↔
      folkStep2NoCut rule ∧ t₁.isCutFree ∧ t₂.isCutFree := by
  cases rule <;> rfl

/-- Structural lifting of indexed LK proof trees. Every recursive constructor
uses the correspondingly lifted indexed rule, so the result has exactly the
lifted source conclusion. -/
def freshLift_folkProofTree {L : Language} :
    {s : Sequent L} → FOLKProofTree s →
      FOLKProofTree (freshLiftSequent s)
  | _, .axiom_ s h =>
      .axiom_ (freshLiftSequent s) (freshLift_isFOLKAxiom s h)
  | _, .onePremise rule t =>
      .onePremise (freshLift_folkStep1 rule)
        (freshLift_folkProofTree t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise (freshLift_folkStep2 rule)
        (freshLift_folkProofTree t₁) (freshLift_folkProofTree t₂)

/-- The conclusion projection of the lifted proof tree is exactly the lifted
conclusion projection of the source tree. -/
@[simp]
theorem freshLift_folkProofTree_conclusion {L : Language}
    {s : Sequent L} (t : FOLKProofTree s) :
    (freshLift_folkProofTree t).conclusion =
      freshLiftSequent t.conclusion :=
  rfl

/-- Structural lifting preserves and reflects absence of cut constructors. -/
theorem freshLift_folkProofTree_isCutFree {L : Language}
    {s : Sequent L} (t : FOLKProofTree s) :
    (freshLift_folkProofTree t).isCutFree ↔ t.isCutFree := by
  induction t with
  | axiom_ s h =>
    simp only [freshLift_folkProofTree, FOLKProofTree.isCutFree]
  | onePremise rule t ih =>
    simpa only [freshLift_folkProofTree, FOLKProofTree.isCutFree] using ih
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    simp only [freshLift_folkProofTree]
    rw [folkProofTree_twoPremise_isCutFree,
      folkProofTree_twoPremise_isCutFree]
    exact and_congr (freshLift_folkStep2_noCut rule)
      (and_congr ih₁ ih₂)

/-- Cut-free provability transports from the source language to its
fresh-bottom extension with the exact lifted sequent as conclusion. -/
theorem freshLift_folkCutFreeProvable {L : Language}
    (s : Sequent L) (h : folkCutFreeProvable s) :
    folkCutFreeProvable (freshLiftSequent s) := by
  rcases h with ⟨t, hcf⟩
  exact ⟨freshLift_folkProofTree t,
    (freshLift_folkProofTree_isCutFree t).mpr hcf⟩

theorem freshLowerFormula_subst {L : Language}
    (R : FormulaN L) (A : FormulaN (FreshBotLanguage L))
    (t : Term (FreshBotLanguage L)) (x : Nat)
    (hR : formulaSubstN R (freshLowerTerm t) x = R) :
    freshLowerFormula R (formulaSubstN A t x) =
      formulaSubstN (freshLowerFormula R A) (freshLowerTerm t) x := by
  induction A with
  | predN P ts =>
    cases P with
    | inl P =>
      simp only [formulaSubstN, freshLowerFormula]
      congr 1
      funext i
      exact freshLowerTerm_subst (ts i) t x
    | inr u =>
      cases u
      simp only [formulaSubstN, freshLowerFormula]
      exact hR.symm
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstN, freshLowerFormula, freshLowerTerm_subst]
  | neg A ih => simp only [formulaSubstN, freshLowerFormula, ih]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, freshLowerFormula, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [formulaSubstN, freshLowerFormula, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [formulaSubstN, freshLowerFormula, ihA, ihB]
  | all y A ih =>
    by_cases hxy : x != y
    · simp [formulaSubstN, freshLowerFormula, hxy, ih]
    · simp [formulaSubstN, freshLowerFormula, hxy]
  | ex y A ih =>
    by_cases hxy : x != y
    · simp [formulaSubstN, freshLowerFormula, hxy, ih]
    · simp [formulaSubstN, freshLowerFormula, hxy]

theorem freshLowerFormula_isFreeFor {L : Language}
    (R : FormulaN L) (t : Term (FreshBotLanguage L)) (x : Nat)
    (A : FormulaN (FreshBotLanguage L))
    (hR : isFreeForN (freshLowerTerm t) x R) :
    isFreeForN (freshLowerTerm t) x (freshLowerFormula R A) ↔
      isFreeForN t x A := by
  induction A with
  | predN P ts =>
    cases P with
    | inl P => rfl
    | inr u =>
      cases u
      simp only [freshLowerFormula, isFreeForN, hR]
  | eq_ hL t₁ t₂ => rfl
  | neg A ih => simpa only [freshLowerFormula, isFreeForN] using ih
  | conj A B ihA ihB =>
    simpa only [freshLowerFormula, isFreeForN] using and_congr ihA ihB
  | disj A B ihA ihB =>
    simpa only [freshLowerFormula, isFreeForN] using and_congr ihA ihB
  | impl A B ihA ihB =>
    simpa only [freshLowerFormula, isFreeForN] using and_congr ihA ihB
  | all y A ih =>
    simp only [freshLowerFormula, isFreeForN, freshLowerTerm_fv, ih]
  | ex y A ih =>
    simp only [freshLowerFormula, isFreeForN, freshLowerTerm_fv, ih]

private theorem replacementOccurrence_or
    {a b freshA freshB replacement : Prop} :
    (a ∨ freshA ∧ replacement) ∨ (b ∨ freshB ∧ replacement) ↔
      (a ∨ b) ∨ (freshA ∨ freshB) ∧ replacement := by
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ha | ⟨hfa, hr⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inr ⟨Or.inl hfa, hr⟩
    · rcases h with hb | ⟨hfb, hr⟩
      · exact Or.inl (Or.inr hb)
      · exact Or.inr ⟨Or.inr hfb, hr⟩
  · intro h
    rcases h with h | ⟨h, hr⟩
    · rcases h with ha | hb
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl hb)
    · rcases h with hfa | hfb
      · exact Or.inl (Or.inr ⟨hfa, hr⟩)
      · exact Or.inr (Or.inr ⟨hfb, hr⟩)

theorem freshLowerFormula_predSymbols {L : Language}
    (R : FormulaN L) (A : FormulaN (FreshBotLanguage L))
    (Q : L.predSymbols) :
    formulaPredSymbolsN (freshLowerFormula R A) Q ↔
      formulaPredSymbolsN A (.inl Q) ∨
        (formulaPredSymbolsN A (freshBot (L := L)) ∧
          formulaPredSymbolsN R Q) := by
  induction A with
  | predN P ts =>
    cases P with
    | inl P =>
      simp only [freshLowerFormula, formulaPredSymbolsN, freshBot]
      constructor
      · intro h
        exact Or.inl (congrArg Sum.inl h)
      · intro h
        rcases h with h | ⟨h, _⟩
        · exact Sum.inl.inj h
        · cases h
    | inr u =>
      cases u
      simp only [freshLowerFormula, formulaPredSymbolsN, freshBot]
      constructor
      · intro h
        exact Or.inr ⟨rfl, h⟩
      · intro h
        rcases h with h | ⟨_, h⟩
        · cases h
        · exact h
  | eq_ hL t₁ t₂ =>
    simp only [freshLowerFormula, formulaPredSymbolsN, Set.empty, false_and,
      or_false, iff_self]
  | neg A ih => simpa only [freshLowerFormula, formulaPredSymbolsN] using ih
  | conj A B ihA ihB =>
    change
      (formulaPredSymbolsN (freshLowerFormula R A) Q ∨
          formulaPredSymbolsN (freshLowerFormula R B) Q) ↔
        (formulaPredSymbolsN A (.inl Q) ∨
            formulaPredSymbolsN B (.inl Q)) ∨
          (formulaPredSymbolsN A freshBot ∨
              formulaPredSymbolsN B freshBot) ∧
            formulaPredSymbolsN R Q
    rw [ihA, ihB]
    exact replacementOccurrence_or
  | disj A B ihA ihB =>
    change
      (formulaPredSymbolsN (freshLowerFormula R A) Q ∨
          formulaPredSymbolsN (freshLowerFormula R B) Q) ↔
        (formulaPredSymbolsN A (.inl Q) ∨
            formulaPredSymbolsN B (.inl Q)) ∨
          (formulaPredSymbolsN A freshBot ∨
              formulaPredSymbolsN B freshBot) ∧
            formulaPredSymbolsN R Q
    rw [ihA, ihB]
    exact replacementOccurrence_or
  | impl A B ihA ihB =>
    change
      (formulaPredSymbolsN (freshLowerFormula R A) Q ∨
          formulaPredSymbolsN (freshLowerFormula R B) Q) ↔
        (formulaPredSymbolsN A (.inl Q) ∨
            formulaPredSymbolsN B (.inl Q)) ∨
          (formulaPredSymbolsN A freshBot ∨
              formulaPredSymbolsN B freshBot) ∧
            formulaPredSymbolsN R Q
    rw [ihA, ihB]
    exact replacementOccurrence_or
  | all x A ih =>
    simpa only [freshLowerFormula, formulaPredSymbolsN] using ih
  | ex x A ih =>
    simpa only [freshLowerFormula, formulaPredSymbolsN] using ih

theorem freshLowerFormula_constSymbols {L : Language}
    (R : FormulaN L) (A : FormulaN (FreshBotLanguage L))
    (c : L.constSymbols) :
    formulaConstSymbolsN (freshLowerFormula R A) c →
      formulaConstSymbolsN A c ∨ formulaConstSymbolsN R c := by
  intro hc
  induction A with
  | predN P ts =>
    cases P with
    | inl P =>
      simp only [freshLowerFormula, formulaConstSymbolsN] at hc ⊢
      rcases hc with ⟨i, hi⟩
      have hi' : termConstSymbols (ts i) c := by
        simpa only [freshLowerTerm_constSymbols] using hi
      exact Or.inl ⟨i, hi'⟩
    | inr u =>
      cases u
      exact Or.inr hc
  | eq_ hL t₁ t₂ =>
    simp only [freshLowerFormula, formulaConstSymbolsN] at hc ⊢
    rcases hc with h | h
    · have h' : termConstSymbols t₁ c := by
        simpa only [freshLowerTerm_constSymbols] using h
      exact Or.inl (Or.inl h')
    · have h' : termConstSymbols t₂ c := by
        simpa only [freshLowerTerm_constSymbols] using h
      exact Or.inl (Or.inr h')
  | neg A ih => exact ih hc
  | conj A B ihA ihB =>
    rcases hc with hc | hc
    · rcases ihA hc with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hc with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | disj A B ihA ihB =>
    rcases hc with hc | hc
    · rcases ihA hc with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hc with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | impl A B ihA ihB =>
    rcases hc with hc | hc
    · rcases ihA hc with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hc with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | all x A ih => exact ih hc
  | ex x A ih => exact ih hc

theorem freshLowerFormula_fv {L : Language}
    (R : FormulaN L) (A : FormulaN (FreshBotLanguage L)) :
    formulaFVN (freshLowerFormula R A) ⊆
      formulaFVN A ∪ formulaFVN R := by
  intro v hv
  induction A with
  | predN P ts =>
    cases P with
    | inl P =>
      simp only [freshLowerFormula, formulaFVN] at hv ⊢
      rcases hv with ⟨i, hi⟩
      have hi' : termFV (ts i) v := by
        simpa only [freshLowerTerm_fv] using hi
      exact Or.inl ⟨i, hi'⟩
    | inr u =>
      cases u
      exact Or.inr hv
  | eq_ hL t₁ t₂ =>
    simp only [freshLowerFormula, formulaFVN] at hv ⊢
    rcases hv with h | h
    · have h' : termFV t₁ v := by
        simpa only [freshLowerTerm_fv] using h
      exact Or.inl (Or.inl h')
    · have h' : termFV t₂ v := by
        simpa only [freshLowerTerm_fv] using h
      exact Or.inl (Or.inr h')
  | neg A ih => exact ih hv
  | conj A B ihA ihB =>
    rcases hv with hv | hv
    · rcases ihA hv with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hv with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | disj A B ihA ihB =>
    rcases hv with hv | hv
    · rcases ihA hv with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hv with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | impl A B ihA ihB =>
    rcases hv with hv | hv
    · rcases ihA hv with hA | hR
      · exact Or.inl (Or.inl hA)
      · exact Or.inr hR
    · rcases ihB hv with hB | hR
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hR
  | all x A ih =>
    rcases hv with ⟨hv, hvx⟩
    rcases ih hv with hA | hR
    · exact Or.inl ⟨hA, hvx⟩
    · exact Or.inr hR
  | ex x A ih =>
    rcases hv with ⟨hv, hvx⟩
    rcases ih hv with hA | hR
    · exact Or.inl ⟨hA, hvx⟩
    · exact Or.inr hR

theorem freshLowerFormula_noEq {L : Language}
    (R : FormulaN L) (A : FormulaN (FreshBotLanguage L))
    (hR : formulaNoEq R) :
    formulaNoEq (freshLowerFormula R A) ↔ formulaNoEq A := by
  induction A with
  | predN P ts =>
    cases P with
    | inl P => rfl
    | inr u =>
      cases u
      simp only [freshLowerFormula, formulaNoEq, hR]
  | eq_ hL t₁ t₂ => rfl
  | neg A ih => simpa only [freshLowerFormula, formulaNoEq] using ih
  | conj A B ihA ihB =>
    simpa only [freshLowerFormula, formulaNoEq] using and_congr ihA ihB
  | disj A B ihA ihB =>
    simpa only [freshLowerFormula, formulaNoEq] using and_congr ihA ihB
  | impl A B ihA ihB =>
    simpa only [freshLowerFormula, formulaNoEq] using and_congr ihA ihB
  | all x A ih => simpa only [freshLowerFormula, formulaNoEq] using ih
  | ex x A ih => simpa only [freshLowerFormula, formulaNoEq] using ih

-- ===================================================================
-- Craig fresh-bottom step 3/5: shared contradiction and lowering laws
-- ===================================================================

/-- Gallier's closed contradiction built from an arbitrary shared predicate:
`∀v (P(v, ..., v) ∧ ¬P(v, ..., v))`. Every argument of `P` is the chosen
variable `v`; the outer quantifier closes all of those occurrences. -/
def sharedPredFalse {L : Language} (P : L.predSymbols) (v : Nat) :
    FormulaN L :=
  FormulaN.all v
    (FormulaN.falsum (FormulaN.predN P (fun _ => Term.var v)))

/-- The shared contradiction contains exactly the predicate `P`. -/
@[simp]
theorem sharedPredFalse_predSymbols {L : Language}
    (P Q : L.predSymbols) (v : Nat) :
    formulaPredSymbolsN (sharedPredFalse P v) Q ↔ Q = P := by
  simp only [sharedPredFalse, FormulaN.falsum, formulaPredSymbolsN]
  exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

/-- The shared contradiction introduces no constant symbols. -/
@[simp]
theorem sharedPredFalse_constSymbols {L : Language}
    (P : L.predSymbols) (v : Nat) (c : L.constSymbols) :
    ¬ formulaConstSymbolsN (sharedPredFalse P v) c := by
  intro h
  change
    (∃ _ : Fin (L.predArity P), False) ∨
      (∃ _ : Fin (L.predArity P), False) at h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact h

/-- The outer universal quantifier binds every variable occurrence in the
shared contradiction. -/
@[simp]
theorem sharedPredFalse_fv {L : Language}
    (P : L.predSymbols) (v x : Nat) :
    ¬ formulaFVN (sharedPredFalse P v) x := by
  intro h
  change
    (((∃ _ : Fin (L.predArity P), x = v) ∨
        (∃ _ : Fin (L.predArity P), x = v)) ∧
      ¬x = v) at h
  rcases h with ⟨h, hne⟩
  rcases h with ⟨_, hxv⟩ | ⟨_, hxv⟩
  · exact hne hxv
  · exact hne hxv

/-- The shared contradiction is a sentence. -/
theorem sharedPredFalse_closed {L : Language}
    (P : L.predSymbols) (v : Nat) :
    FormulaN.isClosed (sharedPredFalse P v) := by
  unfold FormulaN.isClosed
  ext x
  exact ⟨fun hx => (sharedPredFalse_fv P v x hx).elim, fun hx => hx.elim⟩

/-- The shared contradiction contains no equality atom, independently of
whether the ambient language provides equality. -/
@[simp]
theorem sharedPredFalse_noEq {L : Language}
    (P : L.predSymbols) (v : Nat) :
    formulaNoEq (sharedPredFalse P v) := by
  simp only [sharedPredFalse, FormulaN.falsum, formulaNoEq]
  exact ⟨trivial, trivial⟩

/-- Substitution cannot change the closed shared contradiction. -/
@[simp]
theorem sharedPredFalse_subst {L : Language}
    (P : L.predSymbols) (v : Nat) (t : Term L) (x : Nat) :
    formulaSubstN (sharedPredFalse P v) t x =
      sharedPredFalse P v := by
  by_cases hxv : x != v
  · have hvx : v ≠ x := by
      intro h
      subst x
      simp at hxv
    simp [sharedPredFalse, FormulaN.falsum, formulaSubstN, termSubst,
      hxv, hvx]
  · simp [sharedPredFalse, formulaSubstN, hxv]

/-- Exact free-for condition for the shared contradiction. The second
disjunct is the side condition used when replaying quantified LK rules. -/
@[simp]
theorem sharedPredFalse_isFreeFor {L : Language}
    (P : L.predSymbols) (v : Nat) (t : Term L) (x : Nat) :
    isFreeForN t x (sharedPredFalse P v) ↔
      x = v ∨ v ∉ termFV t := by
  simp only [sharedPredFalse, FormulaN.falsum, isFreeForN, and_self,
    and_true]

/-- A term avoiding the chosen variable is free for every variable in the
shared contradiction. -/
theorem sharedPredFalse_isFreeFor_of_not_fv {L : Language}
    (P : L.predSymbols) (v : Nat) (t : Term L) (x : Nat)
    (hv : v ∉ termFV t) :
    isFreeForN t x (sharedPredFalse P v) :=
  (sharedPredFalse_isFreeFor P v t x).mpr (Or.inr hv)

/-- A concrete ordinary indexed LK refutation of the shared contradiction.
The derivation starts at `P(v, ..., v) → P(v, ..., v)`, moves the right-hand
atom across as a negation, rebuilds the conjunction on the left, contracts,
and finally introduces the universal quantifier. -/
def sharedPredFalseRefutation {L : Language}
    (P : L.predSymbols) (v : Nat) :
    FOLKProofTree
      (Sequent.mk [sharedPredFalse P v] []) := by
  let atom : FormulaN L := FormulaN.predN P (fun _ => Term.var v)
  let contra : FormulaN L := FormulaN.falsum atom
  have ax : FOLKProofTree (Sequent.mk [atom] [atom]) :=
    .axiom_ _ ⟨atom, rfl, rfl⟩
  have negL : FOLKProofTree (Sequent.mk [FormulaN.neg atom, atom] []) :=
    .onePremise (.negLeft atom [atom] []) ax
  have swap₁ : FOLKProofTree (Sequent.mk [atom, FormulaN.neg atom] []) :=
    .onePremise
      (.exchangeLeft [] (FormulaN.neg atom) atom [] []) negL
  have conjL₁ :
      FOLKProofTree
        (Sequent.mk [contra, FormulaN.neg atom] []) :=
    .onePremise
      (.andLeftL atom (FormulaN.neg atom) [FormulaN.neg atom] []) swap₁
  have swap₂ :
      FOLKProofTree
        (Sequent.mk [FormulaN.neg atom, contra] []) :=
    .onePremise
      (.exchangeLeft [] contra (FormulaN.neg atom) [] []) conjL₁
  have conjL₂ : FOLKProofTree (Sequent.mk [contra, contra] []) :=
    .onePremise
      (.andLeftR atom (FormulaN.neg atom) [contra] []) swap₂
  have contract : FOLKProofTree (Sequent.mk [contra] []) :=
    .onePremise (.contractLeft contra [] []) conjL₂
  have hfree : isFreeForN (Term.var v) v contra := by
    simp only [contra, isFreeForN]
    exact ⟨trivial, trivial⟩
  have subst :
      FOLKProofTree
        (Sequent.mk [formulaSubstN contra (Term.var v) v] []) := by
    simpa only [formulaSubstN_var_self] using contract
  change FOLKProofTree (Sequent.mk [FormulaN.all v contra] [])
  exact FOLKProofTree.onePremise
    (.allLeft (Term.var v) v contra [] [] hfree) subst

/-- Gallier's shared contradiction is refutable in ordinary indexed LK. -/
theorem sharedPredFalse_refutable {L : Language}
    (P : L.predSymbols) (v : Nat) :
    folkProvable (Sequent.mk [sharedPredFalse P v] []) :=
  ⟨sharedPredFalseRefutation P v⟩

/-- Predicate occurrence after lowering with Gallier's shared contradiction:
an occurrence comes either from an old predicate in the extended formula, or
from replacing a fresh-bottom occurrence, in which case it is exactly `P`. -/
theorem freshLowerFormula_sharedPredFalse_predSymbols {L : Language}
    (P Q : L.predSymbols) (v : Nat)
    (A : FormulaN (FreshBotLanguage L)) :
    formulaPredSymbolsN
        (freshLowerFormula (sharedPredFalse P v) A) Q ↔
      formulaPredSymbolsN A (.inl Q) ∨
        (formulaPredSymbolsN A (freshBot (L := L)) ∧ Q = P) := by
  rw [freshLowerFormula_predSymbols]
  simp only [sharedPredFalse_predSymbols]

/-- Lowering with the shared contradiction introduces no constants. -/
theorem freshLowerFormula_sharedPredFalse_constSymbols {L : Language}
    (P : L.predSymbols) (v : Nat)
    (A : FormulaN (FreshBotLanguage L)) (c : L.constSymbols) :
    formulaConstSymbolsN
        (freshLowerFormula (sharedPredFalse P v) A) c →
      formulaConstSymbolsN A c := by
  intro hc
  rcases freshLowerFormula_constSymbols
      (sharedPredFalse P v) A c hc with hA | hFalse
  · exact hA
  · exact (sharedPredFalse_constSymbols P v c hFalse).elim

/-- Lowering with the closed shared contradiction introduces no free
variables. This is the direction required by eigenvariable replay. -/
theorem freshLowerFormula_sharedPredFalse_fv {L : Language}
    (P : L.predSymbols) (v : Nat)
    (A : FormulaN (FreshBotLanguage L)) :
    formulaFVN (freshLowerFormula (sharedPredFalse P v) A) ⊆
      formulaFVN A := by
  intro x hx
  rcases freshLowerFormula_fv (sharedPredFalse P v) A x hx with
    hA | hFalse
  · exact hA
  · exact (sharedPredFalse_fv P v x hFalse).elim

/-- Lowering with the equality-free shared contradiction preserves the
absence of equality exactly. -/
@[simp]
theorem freshLowerFormula_sharedPredFalse_noEq {L : Language}
    (P : L.predSymbols) (v : Nat)
    (A : FormulaN (FreshBotLanguage L)) :
    formulaNoEq (freshLowerFormula (sharedPredFalse P v) A) ↔
      formulaNoEq A :=
  freshLowerFormula_noEq (sharedPredFalse P v) A
    (sharedPredFalse_noEq P v)

/-- Formula lowering with the closed shared contradiction commutes with
substitution without an additional side condition. -/
theorem freshLowerFormula_sharedPredFalse_subst {L : Language}
    (P : L.predSymbols) (v : Nat)
    (A : FormulaN (FreshBotLanguage L))
    (t : Term (FreshBotLanguage L)) (x : Nat) :
    freshLowerFormula (sharedPredFalse P v) (formulaSubstN A t x) =
      formulaSubstN
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerTerm t) x :=
  freshLowerFormula_subst (sharedPredFalse P v) A t x
    (sharedPredFalse_subst P v (freshLowerTerm t) x)

/-- Under the proof-wide freshness condition on `v`, lowering preserves the
free-for side condition of quantified LK rules exactly. -/
theorem freshLowerFormula_sharedPredFalse_isFreeFor {L : Language}
    (P : L.predSymbols) (v : Nat)
    (t : Term (FreshBotLanguage L)) (x : Nat)
    (A : FormulaN (FreshBotLanguage L))
    (hv : v ∉ termFV t) :
    isFreeForN (freshLowerTerm t) x
        (freshLowerFormula (sharedPredFalse P v) A) ↔
      isFreeForN t x A := by
  apply freshLowerFormula_isFreeFor
  apply sharedPredFalse_isFreeFor_of_not_fv
  simpa only [freshLowerTerm_fv] using hv

-- ===================================================================
-- Craig fresh-bottom step 4/5: lowering indexed LK⊥ derivations
-- ===================================================================

/-- Lowering an ordinary LK axiom in the extended language gives an
ordinary LK axiom with exactly the lowered sequent as conclusion. -/
theorem freshLower_isFOLKAxiom_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    (s : Sequent (FreshBotLanguage L))
    (h : isFOLKAxiom s) :
    isFOLKAxiom
      (freshLowerSequent (sharedPredFalse P v) s) := by
  rcases h with ⟨A, hΓ, hΔ⟩
  refine ⟨freshLowerFormula (sharedPredFalse P v) A, ?_, ?_⟩
  · simp only [freshLowerSequent, hΓ, freshLowerList,
      List.map_cons, List.map_nil]
  · simp only [freshLowerSequent, hΔ, freshLowerList,
      List.map_cons, List.map_nil]

/-- A fresh eigenvariable for an extended-language sequent stays fresh after
lowering with the closed shared contradiction. -/
theorem freshLowerSequent_sharedPredFalse_eigenfresh {L : Language}
    (P : L.predSymbols) (v y : Nat)
    (s : Sequent (FreshBotLanguage L))
    (hfresh : ∀ F ∈ s.antecedent ++ s.succedent,
      y ∉ formulaFVN F) :
    ∀ F ∈
        (freshLowerSequent (sharedPredFalse P v) s).antecedent ++
          (freshLowerSequent (sharedPredFalse P v) s).succedent,
      y ∉ formulaFVN F := by
  intro F hF
  change
    F ∈
      s.antecedent.map
          (freshLowerFormula (sharedPredFalse P v)) ++
        s.succedent.map
          (freshLowerFormula (sharedPredFalse P v)) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨A, hA, rfl⟩
    intro hy
    exact
      hfresh A (List.mem_append.mpr (Or.inl hA))
        (freshLowerFormula_sharedPredFalse_fv P v A y hy)
  · rcases List.mem_map.mp hF with ⟨A, hA, rfl⟩
    intro hy
    exact
      hfresh A (List.mem_append.mpr (Or.inr hA))
        (freshLowerFormula_sharedPredFalse_fv P v A y hy)

end CraigFreshBot
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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot
section
variable (L : Language) (P : L.predSymbols) (v : Nat)

def freshLower_allLeft
    (t : Term (FreshBotLanguage L)) (x : Nat) (A : FormulaN (FreshBotLanguage L)) (Γ : List (FormulaN
      (FreshBotLanguage L))) (Δ : List (FormulaN (FreshBotLanguage L))) (hfree : isFreeForN t x A) (hvar :
      (FOLKStep1.allLeft t x A Γ Δ hfree).varNotOccurs v)
    : FOLKStep1 (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (formulaSubstN A t x :: Γ) (Δ)))
      (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (FormulaN.all x A :: Γ) (Δ))) := by
  simp only [FOLKStep1.varNotOccurs] at hvar
  have hfree' : isFreeForN (freshLowerTerm t) x (freshLowerFormula (sharedPredFalse P v) A) :=
    (freshLowerFormula_sharedPredFalse_isFreeFor P v t x A hvar.2.2.1).mpr hfree
  simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
    freshLowerFormula_sharedPredFalse_subst, List.map_cons] using
    (FOLKStep1.allLeft (freshLowerTerm t) x (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ) hfree')

def freshLower_allRight
    (y : Nat) (x : Nat) (A : FormulaN (FreshBotLanguage L)) (Γ : List (FormulaN (FreshBotLanguage L))) (Δ :
      List (FormulaN (FreshBotLanguage L))) (hfresh : ∀ (F : FormulaN (FreshBotLanguage L)), F ∈ (Γ) ++ (Δ ++
      [FormulaN.all x A]) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x A) (hvar :
      (FOLKStep1.allRight y x A Γ Δ hfresh hfreeFor).varNotOccurs v)
    : FOLKStep1 (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var y)
      x]))) (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))) := by
  simp only [FOLKStep1.varNotOccurs] at hvar
  have hv : v ∉ termFV (Term.var y : Term (FreshBotLanguage L)) := by
    change v ≠ y
    exact hvar.2.2.1
  have hfreeFor' : isFreeForN (Term.var y : Term L) x (freshLowerFormula (sharedPredFalse P v) A) := by
    simpa only [freshLowerTerm] using (freshLowerFormula_sharedPredFalse_isFreeFor
        P v (Term.var y) x A hv).mpr hfreeFor
  have hfresh' : ∀ F ∈ (Sequent.mk (freshLowerList (sharedPredFalse P v) Γ)
            (freshLowerList (sharedPredFalse P v) Δ ++ [FormulaN.all x
                (freshLowerFormula (sharedPredFalse P v) A)])).antecedent ++
            (Sequent.mk (freshLowerList (sharedPredFalse P v) Γ) (freshLowerList (sharedPredFalse P v) Δ ++
                [FormulaN.all x (freshLowerFormula (sharedPredFalse P v) A)])).succedent,
        y ∉ formulaFVN F := by
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      freshLowerSequent_sharedPredFalse_eigenfresh P v y (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) hfresh
  simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
    freshLowerFormula_sharedPredFalse_subst, List.map_append,
    List.map_cons, List.map_nil, freshLowerTerm] using
    (FOLKStep1.allRight y x (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      hfresh' hfreeFor')

def freshLower_exLeft
    (y : Nat) (x : Nat) (A : FormulaN (FreshBotLanguage L)) (Γ : List (FormulaN (FreshBotLanguage L))) (Δ :
      List (FormulaN (FreshBotLanguage L))) (hfresh : ∀ (F : FormulaN (FreshBotLanguage L)), F ∈ (FormulaN.ex
      x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x A) (hvar : (FOLKStep1.exLeft
      y x A Γ Δ hfresh hfreeFor).varNotOccurs v)
    : FOLKStep1 (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ)
      (Δ))) (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (FormulaN.ex x A :: Γ) (Δ))) := by
  simp only [FOLKStep1.varNotOccurs] at hvar
  have hv : v ∉ termFV (Term.var y : Term (FreshBotLanguage L)) := by
    change v ≠ y
    exact hvar.2.2.1
  have hfreeFor' : isFreeForN (Term.var y : Term L) x (freshLowerFormula (sharedPredFalse P v) A) := by
    simpa only [freshLowerTerm] using (freshLowerFormula_sharedPredFalse_isFreeFor
        P v (Term.var y) x A hv).mpr hfreeFor
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (freshLowerFormula (sharedPredFalse P v) A) ::
              freshLowerList (sharedPredFalse P v) Γ)
            (freshLowerList (sharedPredFalse P v) Δ)).antecedent ++
            (Sequent.mk (FormulaN.ex x (freshLowerFormula (sharedPredFalse P v) A) ::
                freshLowerList (sharedPredFalse P v) Γ)
              (freshLowerList (sharedPredFalse P v) Δ)).succedent,
        y ∉ formulaFVN F := by
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula, List.map_append, List.map_cons] using
      freshLowerSequent_sharedPredFalse_eigenfresh P v y (Sequent.mk (FormulaN.ex x A :: Γ) Δ) hfresh
  simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
    freshLowerFormula_sharedPredFalse_subst, List.map_cons,
    freshLowerTerm] using
    (FOLKStep1.exLeft y x (freshLowerFormula (sharedPredFalse P v) A) (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      hfresh' hfreeFor')

def freshLower_exRight
    (t : Term (FreshBotLanguage L)) (x : Nat) (A : FormulaN (FreshBotLanguage L)) (Γ : List (FormulaN
      (FreshBotLanguage L))) (Δ : List (FormulaN (FreshBotLanguage L))) (hfree : isFreeForN t x A) (hvar :
      (FOLKStep1.exRight t x A Γ Δ hfree).varNotOccurs v)
    : FOLKStep1 (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t x])))
      (freshLowerSequent (sharedPredFalse P v) (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A]))) := by
  simp only [FOLKStep1.varNotOccurs] at hvar
  have hfree' : isFreeForN (freshLowerTerm t) x (freshLowerFormula (sharedPredFalse P v) A) :=
    (freshLowerFormula_sharedPredFalse_isFreeFor P v t x A hvar.2.2.1).mpr hfree
  simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
    freshLowerFormula_sharedPredFalse_subst, List.map_append,
    List.map_cons, List.map_nil] using
    (FOLKStep1.exRight (freshLowerTerm t) x (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ) hfree')

end
end CraigFreshBot
end LCS.CutElim.Interpolation
end

