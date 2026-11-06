import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Interpolants

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

/-- The source language with one genuinely fresh nullary predicate adjoined.
Function and constant symbols, all of their arities, and equality are unchanged. -/
def FreshBotLanguage (L : Language) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := L.constSymbols
  predSymbols := Sum L.predSymbols Unit
  predArity
    | .inl P => L.predArity P
    | .inr _ => 0
  hasEquality := L.hasEquality

/-- The newly adjoined predicate symbol. -/
def freshBot {L : Language} : (FreshBotLanguage L).predSymbols :=
  .inr ()

@[simp]
theorem freshBot_arity {L : Language} :
    (FreshBotLanguage L).predArity (freshBot (L := L)) = 0 :=
  rfl

@[simp]
theorem freshLanguage_withoutEquality {L : Language} :
    (FreshBotLanguage L).withoutEquality ↔ L.withoutEquality :=
  Iff.rfl

/-- Terms lift structurally because the extension changes no term-forming
symbols. -/
def freshLiftTerm {L : Language} : Term L → Term (FreshBotLanguage L)
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func f (fun i => freshLiftTerm (ts i))

/-- Formula lifting injects every old predicate through `Sum.inl`. -/
def freshLiftFormula {L : Language} :
    FormulaN L → FormulaN (FreshBotLanguage L)
  | .predN P ts => .predN (.inl P) (fun i => freshLiftTerm (ts i))
  | .eq_ hL t₁ t₂ => .eq_ hL (freshLiftTerm t₁) (freshLiftTerm t₂)
  | .neg A => .neg (freshLiftFormula A)
  | .conj A B => .conj (freshLiftFormula A) (freshLiftFormula B)
  | .disj A B => .disj (freshLiftFormula A) (freshLiftFormula B)
  | .impl A B => .impl (freshLiftFormula A) (freshLiftFormula B)
  | .all x A => .all x (freshLiftFormula A)
  | .ex x A => .ex x (freshLiftFormula A)

/-- Pointwise formula lifting for contexts. -/
def freshLiftList {L : Language}
    (fs : List (FormulaN L)) : List (FormulaN (FreshBotLanguage L)) :=
  fs.map freshLiftFormula

/-- Pointwise lifting of both sides of a sequent. -/
def freshLiftSequent {L : Language}
    (s : Sequent L) : Sequent (FreshBotLanguage L) :=
  { antecedent := freshLiftList s.antecedent
    succedent := freshLiftList s.succedent }

/-- Terms lower uniquely because the fresh extension has no new term-forming
symbols. -/
def freshLowerTerm {L : Language} : Term (FreshBotLanguage L) → Term L
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func f (fun i => freshLowerTerm (ts i))

/-- Lower a formula back to the source language, replacing each occurrence of
the fresh nullary predicate by `R`. -/
def freshLowerFormula {L : Language} (R : FormulaN L) :
    FormulaN (FreshBotLanguage L) → FormulaN L
  | .predN (.inl P) ts =>
      .predN P (fun i => freshLowerTerm (ts i))
  | .predN (.inr _) _ => R
  | .eq_ hL t₁ t₂ => .eq_ hL (freshLowerTerm t₁) (freshLowerTerm t₂)
  | .neg A => .neg (freshLowerFormula R A)
  | .conj A B => .conj (freshLowerFormula R A) (freshLowerFormula R B)
  | .disj A B => .disj (freshLowerFormula R A) (freshLowerFormula R B)
  | .impl A B => .impl (freshLowerFormula R A) (freshLowerFormula R B)
  | .all x A => .all x (freshLowerFormula R A)
  | .ex x A => .ex x (freshLowerFormula R A)

end CraigFreshBot
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

end CraigFreshBot
end LCS.CutElim.Interpolation
end
