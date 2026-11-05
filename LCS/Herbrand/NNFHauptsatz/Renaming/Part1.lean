import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.SharpenedHauptsatz

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz

/-- Uniformly rename term variables and formula binders. -/
def formulaVarMapN {L : Language} (ρ : Nat → Nat) :
    FormulaN L → FormulaN L
  | .predN P ts => .predN P (fun i => termVarMap ρ (ts i))
  | .eq_ hL t₁ t₂ => .eq_ hL (termVarMap ρ t₁) (termVarMap ρ t₂)
  | .neg A => .neg (formulaVarMapN ρ A)
  | .conj A B => .conj (formulaVarMapN ρ A) (formulaVarMapN ρ B)
  | .disj A B => .disj (formulaVarMapN ρ A) (formulaVarMapN ρ B)
  | .impl A B => .impl (formulaVarMapN ρ A) (formulaVarMapN ρ B)
  | .all x A => .all (ρ x) (formulaVarMapN ρ A)
  | .ex x A => .ex (ρ x) (formulaVarMapN ρ A)

/-- Pointwise variable renaming of a finite formula context. -/
noncomputable def formulaFinsetVarMapN {L : Language}
    (ρ : Nat → Nat) (S : LCS.Finset (FormulaN L)) :
    LCS.Finset (FormulaN L) :=
  LCS.Finset.image (formulaVarMapN ρ) S

/-- Free variables of a renamed term are exactly images of source free
variables. -/
theorem termFV_termVarMap_iff {L : Language}
    (ρ : Nat → Nat) (t : Term L) (z : Nat) :
    z ∈ termFV (termVarMap ρ t) ↔
      ∃ x, x ∈ termFV t ∧ ρ x = z := by
  induction t with
  | var x =>
      simp only [termVarMap, termFV]
      constructor
      · intro hz
        exact ⟨x, rfl, hz.symm⟩
      · rintro ⟨y, hy, hρy⟩
        subst y
        exact hρy.symm
  | const c =>
      simp only [termVarMap, termFV]
      constructor
      · intro hz
        exact hz.elim
      · rintro ⟨x, hx, _⟩
        exact hx.elim
  | func f ts ih =>
      simp only [termVarMap, termFV]
      constructor
      · rintro ⟨i, hi⟩
        rcases (ih i).mp hi with ⟨x, hx, hρx⟩
        exact ⟨x, ⟨i, hx⟩, hρx⟩
      · rintro ⟨x, ⟨i, hx⟩, hρx⟩
        exact ⟨i, (ih i).mpr ⟨x, hx, hρx⟩⟩

/-- At a renamed source variable, term-FV membership reflects exactly when
the renaming is injective. -/
theorem termFV_termVarMap_image_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (t : Term L) (x : Nat) :
    ρ x ∈ termFV (termVarMap ρ t) ↔ x ∈ termFV t := by
  rw [termFV_termVarMap_iff]
  constructor
  · rintro ⟨y, hy, hEq⟩
    simpa [hρ hEq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Uniform term renaming is injective whenever its variable map is. -/
theorem termVarMap_injective {L : Language} {ρ : Nat → Nat}
    (hρ : Function.Injective ρ) :
    Function.Injective (termVarMap (L := L) ρ) := by
  intro t
  induction t with
  | var x =>
      intro u h
      cases u with
      | var y =>
          exact congrArg Term.var (hρ (Term.var.inj h))
      | const => cases h
      | func => cases h
  | const c =>
      intro u h
      cases u with
      | var => cases h
      | const d =>
          exact congrArg Term.const (Term.const.inj h)
      | func => cases h
  | func f ts ih =>
      intro u h
      cases u with
      | var => cases h
      | const => cases h
      | func g us =>
          have hfg : f = g := (Term.func.inj h).1
          subst g
          congr 1
          funext i
          apply ih i
          have hargs :
              (fun i => termVarMap ρ (ts i)) =
                (fun i => termVarMap ρ (us i)) :=
            eq_of_heq (Term.func.inj h).2
          exact congrFun hargs i

/-- Uniform formula renaming is injective whenever its variable map is. -/
theorem formulaVarMapN_injective {L : Language} {ρ : Nat → Nat}
    (hρ : Function.Injective ρ) :
    Function.Injective (formulaVarMapN (L := L) ρ) := by
  intro A
  induction A with
  | predN P ts =>
      intro B h
      cases B with
      | predN Q us =>
          have hPQ : P = Q := (FormulaN.predN.inj h).1
          subst Q
          congr 1
          funext i
          apply termVarMap_injective hρ
          have hargs :
              (fun i => termVarMap ρ (ts i)) =
                (fun i => termVarMap ρ (us i)) :=
            eq_of_heq (FormulaN.predN.inj h).2
          exact congrFun hargs i
      | eq_ => cases h
      | neg => cases h
      | conj => cases h
      | disj => cases h
      | impl => cases h
      | all => cases h
      | ex => cases h
  | eq_ _ t₁ t₂ =>
      intro B h
      cases B with
      | predN => cases h
      | eq_ _ u₁ u₂ =>
          have ht := FormulaN.eq_.inj h
          rw [termVarMap_injective hρ ht.1,
            termVarMap_injective hρ ht.2]
      | neg => cases h
      | conj => cases h
      | disj => cases h
      | impl => cases h
      | all => cases h
      | ex => cases h
  | neg A ih =>
      intro B h
      cases B with
      | neg B => rw [ih (FormulaN.neg.inj h)]
      | _ => cases h
  | conj A B ihA ihB =>
      intro C h
      cases C with
      | conj C D =>
          have h' := FormulaN.conj.inj h
          rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | disj A B ihA ihB =>
      intro C h
      cases C with
      | disj C D =>
          have h' := FormulaN.disj.inj h
          rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | impl A B ihA ihB =>
      intro C h
      cases C with
      | impl C D =>
          have h' := FormulaN.impl.inj h
          rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | all x A ih =>
      intro B h
      cases B with
      | all y B =>
          have h' := FormulaN.all.inj h
          rw [hρ h'.1, ih h'.2]
      | _ => cases h
  | ex x A ih =>
      intro B h
      cases B with
      | ex y B =>
          have h' := FormulaN.ex.inj h
          rw [hρ h'.1, ih h'.2]
      | _ => cases h

/-- Renaming does not alter whether a formula is atomic. -/
theorem formulaVarMapN_isAtomic {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L) :
    (formulaVarMapN ρ A).isAtomic = A.isAtomic := by
  cases A <;> rfl

/-- Bound variables of a renamed formula are exactly images of source bound
variables. -/
theorem formulaBVN_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L) (z : Nat) :
    z ∈ formulaBVN (formulaVarMapN ρ A) ↔
      ∃ x, x ∈ formulaBVN A ∧ ρ x = z := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · intro hz
        exact hz.elim
      · rintro ⟨x, hx, _⟩
        exact hx.elim
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · intro hz
        exact hz.elim
      · rintro ⟨x, hx, _⟩
        exact hx.elim
  | neg A ih =>
      simpa only [formulaVarMapN, formulaBVN] using ih
  | conj A B ihA ihB =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | disj A B ihA ihB =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | impl A B ihA ihB =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | all y A ih =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · rintro (hz | hz)
        · rcases ih.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · exact ⟨y, Or.inr rfl, hz.symm⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ih.mpr ⟨x, hx, hρx⟩)
        · subst x
          exact Or.inr hρx.symm
  | ex y A ih =>
      simp only [formulaVarMapN, formulaBVN]
      constructor
      · rintro (hz | hz)
        · rcases ih.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · exact ⟨y, Or.inr rfl, hz.symm⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ih.mpr ⟨x, hx, hρx⟩)
        · subst x
          exact Or.inr hρx.symm

/-- At a renamed source variable, formula-BV membership reflects exactly. -/
theorem formulaBVN_formulaVarMapN_image_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) (x : Nat) :
    ρ x ∈ formulaBVN (formulaVarMapN ρ A) ↔ x ∈ formulaBVN A := by
  rw [formulaBVN_formulaVarMapN_iff]
  constructor
  · rintro ⟨y, hy, hEq⟩
    simpa [hρ hEq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Free variables of a uniformly renamed formula are exactly images of
source free variables.  Injectivity is needed at quantifier subtraction. -/
theorem formulaFVN_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) (z : Nat) :
    z ∈ formulaFVN (formulaVarMapN ρ A) ↔
      ∃ x, x ∈ formulaFVN A ∧ ρ x = z := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro ⟨i, hi⟩
        rcases (termFV_termVarMap_iff ρ (ts i) z).mp hi with
          ⟨x, hx, hρx⟩
        exact ⟨x, ⟨i, hx⟩, hρx⟩
      · rintro ⟨x, ⟨i, hx⟩, hρx⟩
        exact ⟨i, (termFV_termVarMap_iff ρ (ts i) z).mpr
          ⟨x, hx, hρx⟩⟩
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro (hz | hz)
        · rcases (termFV_termVarMap_iff ρ t₁ z).mp hz with
            ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases (termFV_termVarMap_iff ρ t₂ z).mp hz with
            ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl ((termFV_termVarMap_iff ρ t₁ z).mpr
            ⟨x, hx, hρx⟩)
        · exact Or.inr ((termFV_termVarMap_iff ρ t₂ z).mpr
            ⟨x, hx, hρx⟩)
  | neg A ih =>
      simpa only [formulaVarMapN, formulaFVN] using ih
  | conj A B ihA ihB =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | disj A B ihA ihB =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | impl A B ihA ihB =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | all y A ih =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro ⟨hz, hzy⟩
        rcases ih.mp hz with ⟨x, hx, hρx⟩
        refine ⟨x, ⟨hx, ?_⟩, hρx⟩
        intro hxy
        subst x
        exact hzy hρx.symm
      · rintro ⟨x, ⟨hx, hxy⟩, hρx⟩
        refine ⟨ih.mpr ⟨x, hx, hρx⟩, ?_⟩
        intro hzy
        exact hxy (hρ (hρx.trans hzy))
  | ex y A ih =>
      simp only [formulaVarMapN, formulaFVN]
      constructor
      · rintro ⟨hz, hzy⟩
        rcases ih.mp hz with ⟨x, hx, hρx⟩
        refine ⟨x, ⟨hx, ?_⟩, hρx⟩
        intro hxy
        subst x
        exact hzy hρx.symm
      · rintro ⟨x, ⟨hx, hxy⟩, hρx⟩
        refine ⟨ih.mpr ⟨x, hx, hρx⟩, ?_⟩
        intro hzy
        exact hxy (hρ (hρx.trans hzy))

/-- At a renamed source variable, formula-FV membership reflects exactly. -/
theorem formulaFVN_formulaVarMapN_image_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) (x : Nat) :
    ρ x ∈ formulaFVN (formulaVarMapN ρ A) ↔ x ∈ formulaFVN A := by
  rw [formulaFVN_formulaVarMapN_iff ρ hρ]
  constructor
  · rintro ⟨y, hy, hEq⟩
    simpa [hρ hEq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- `termVariables` agrees with the earlier term-FV definition. -/
theorem termVariables_eq_termFV {L : Language} (t : Term L) :
    termVariables t = termFV t := by
  funext z
  apply propext
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f ts ih =>
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mpr hi⟩

/-- All variables of a renamed formula are exactly images of source
variables. -/
theorem formulaAllVariables_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L) (z : Nat) :
    z ∈ formulaAllVariables (formulaVarMapN ρ A) ↔
      ∃ x, x ∈ formulaAllVariables A ∧ ρ x = z := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro ⟨i, hi⟩
        have hi' : z ∈ termFV (termVarMap ρ (ts i)) := by
          rw [← termVariables_eq_termFV]
          exact hi
        rcases (termFV_termVarMap_iff ρ (ts i) z).mp hi' with
          ⟨x, hx, hρx⟩
        have hx' : x ∈ termVariables (ts i) := by
          rw [termVariables_eq_termFV]
          exact hx
        exact ⟨x, ⟨i, hx'⟩, hρx⟩
      · rintro ⟨x, ⟨i, hx⟩, hρx⟩
        have hx' : x ∈ termFV (ts i) := by
          rw [← termVariables_eq_termFV]
          exact hx
        have hz' : z ∈ termFV (termVarMap ρ (ts i)) :=
          (termFV_termVarMap_iff ρ (ts i) z).mpr ⟨x, hx', hρx⟩
        refine ⟨i, ?_⟩
        change z ∈ termVariables (termVarMap ρ (ts i))
        rwa [termVariables_eq_termFV]
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · have hz' : z ∈ termFV (termVarMap ρ t₁) := by
            rw [← termVariables_eq_termFV]
            exact hz
          rcases (termFV_termVarMap_iff ρ t₁ z).mp hz' with
            ⟨x, hx, hρx⟩
          have hx' : x ∈ termVariables t₁ := by
            rw [termVariables_eq_termFV]
            exact hx
          exact ⟨x, Or.inl hx', hρx⟩
        · have hz' : z ∈ termFV (termVarMap ρ t₂) := by
            rw [← termVariables_eq_termFV]
            exact hz
          rcases (termFV_termVarMap_iff ρ t₂ z).mp hz' with
            ⟨x, hx, hρx⟩
          have hx' : x ∈ termVariables t₂ := by
            rw [termVariables_eq_termFV]
            exact hx
          exact ⟨x, Or.inr hx', hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · apply Or.inl
          rw [termVariables_eq_termFV]
          apply (termFV_termVarMap_iff ρ t₁ z).mpr
          refine ⟨x, ?_, hρx⟩
          rw [← termVariables_eq_termFV]
          exact hx
        · apply Or.inr
          rw [termVariables_eq_termFV]
          apply (termFV_termVarMap_iff ρ t₂ z).mpr
          refine ⟨x, ?_, hρx⟩
          rw [← termVariables_eq_termFV]
          exact hx
  | neg A ih =>
      simpa only [formulaVarMapN, formulaAllVariables] using ih
  | conj A B ihA ihB =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | disj A B ihA ihB =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | impl A B ihA ihB =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · rcases ihA.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inl hx, hρx⟩
        · rcases ihB.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · exact Or.inl (ihA.mpr ⟨x, hx, hρx⟩)
        · exact Or.inr (ihB.mpr ⟨x, hx, hρx⟩)
  | all y A ih =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · exact ⟨y, Or.inl rfl, hz.symm⟩
        · rcases ih.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · subst x
          exact Or.inl hρx.symm
        · exact Or.inr (ih.mpr ⟨x, hx, hρx⟩)
  | ex y A ih =>
      simp only [formulaVarMapN, formulaAllVariables]
      constructor
      · rintro (hz | hz)
        · exact ⟨y, Or.inl rfl, hz.symm⟩
        · rcases ih.mp hz with ⟨x, hx, hρx⟩
          exact ⟨x, Or.inr hx, hρx⟩
      · rintro ⟨x, hx | hx, hρx⟩
        · subst x
          exact Or.inl hρx.symm
        · exact Or.inr (ih.mpr ⟨x, hx, hρx⟩)

/-- At a renamed source variable, all-variable membership reflects exactly. -/
theorem formulaAllVariables_formulaVarMapN_image_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) (x : Nat) :
    ρ x ∈ formulaAllVariables (formulaVarMapN ρ A) ↔
      x ∈ formulaAllVariables A := by
  rw [formulaAllVariables_formulaVarMapN_iff]
  constructor
  · rintro ⟨y, hy, hEq⟩
    simpa [hρ hEq] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Uniform renaming commutes with term substitution when variable equality
is reflected by the renaming. -/
theorem termVarMap_termSubst {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (s t : Term L) (x : Nat) :
    termVarMap ρ (termSubst s t x) =
      termSubst (termVarMap ρ s) (termVarMap ρ t) (ρ x) := by
  induction s with
  | var y =>
      simp only [termSubst, termVarMap]
      by_cases hyx : y = x
      · subst y
        simp
      · have hρyx : ρ y ≠ ρ x := fun h => hyx (hρ h)
        simp [hyx, hρyx]
        rfl
  | const c =>
      rfl
  | func f ts ih =>
      simp only [termSubst, termVarMap]
      congr 1
      funext i
      exact ih i

/-- Uniform renaming commutes with capture-avoiding formula substitution. -/
theorem formulaVarMapN_formulaSubstN {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaVarMapN ρ (formulaSubstN A t x) =
      formulaSubstN (formulaVarMapN ρ A) (termVarMap ρ t) (ρ x) := by
  induction A with
  | predN P ts =>
      simp only [formulaSubstN, formulaVarMapN]
      congr 1
      funext i
      exact termVarMap_termSubst ρ hρ (ts i) t x
  | eq_ hL t₁ t₂ =>
      simp only [formulaSubstN, formulaVarMapN]
      rw [termVarMap_termSubst ρ hρ t₁ t x,
        termVarMap_termSubst ρ hρ t₂ t x]
  | neg A ih =>
      simp only [formulaSubstN, formulaVarMapN, ih]
  | conj A B ihA ihB =>
      simp only [formulaSubstN, formulaVarMapN, ihA, ihB]
  | disj A B ihA ihB =>
      simp only [formulaSubstN, formulaVarMapN, ihA, ihB]
  | impl A B ihA ihB =>
      simp only [formulaSubstN, formulaVarMapN, ihA, ihB]
  | all y A ih =>
      by_cases hxy : x = y
      · subst y
        simp [formulaSubstN, formulaVarMapN]
      · have hρxy : ρ x ≠ ρ y := fun h => hxy (hρ h)
        simp [formulaSubstN, formulaVarMapN, hxy, hρxy, ih]
  | ex y A ih =>
      by_cases hxy : x = y
      · subst y
        simp [formulaSubstN, formulaVarMapN]
      · have hρxy : ρ x ≠ ρ y := fun h => hxy (hρ h)
        simp [formulaSubstN, formulaVarMapN, hxy, hρxy, ih]

/-- The free-for side condition is invariant under injective uniform
renaming. -/
theorem isFreeForN_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (t : Term L) (x : Nat) (A : FormulaN L) :
    isFreeForN (termVarMap ρ t) (ρ x) (formulaVarMapN ρ A) ↔
      isFreeForN t x A := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, isFreeForN]
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, isFreeForN]
  | neg A ih =>
      simpa only [formulaVarMapN, isFreeForN] using ih
  | conj A B ihA ihB =>
      simpa only [formulaVarMapN, isFreeForN] using and_congr ihA ihB
  | disj A B ihA ihB =>
      simpa only [formulaVarMapN, isFreeForN] using and_congr ihA ihB
  | impl A B ihA ihB =>
      simpa only [formulaVarMapN, isFreeForN] using and_congr ihA ihB
  | all y A ih =>
      simp only [formulaVarMapN, isFreeForN]
      constructor
      · rintro (hxy | ⟨hFresh, hFree⟩)
        · exact Or.inl (hρ hxy)
        · refine Or.inr ⟨?_, ih.mp hFree⟩
          intro hy
          exact hFresh ((termFV_termVarMap_image_iff ρ hρ t y).mpr hy)
      · rintro (hxy | ⟨hFresh, hFree⟩)
        · exact Or.inl (congrArg ρ hxy)
        · refine Or.inr ⟨?_, ih.mpr hFree⟩
          intro hρy
          exact hFresh ((termFV_termVarMap_image_iff ρ hρ t y).mp hρy)
  | ex y A ih =>
      simp only [formulaVarMapN, isFreeForN]
      constructor
      · rintro (hxy | ⟨hFresh, hFree⟩)
        · exact Or.inl (hρ hxy)
        · refine Or.inr ⟨?_, ih.mp hFree⟩
          intro hy
          exact hFresh ((termFV_termVarMap_image_iff ρ hρ t y).mpr hy)
      · rintro (hxy | ⟨hFresh, hFree⟩)
        · exact Or.inl (congrArg ρ hxy)
        · refine Or.inr ⟨?_, ih.mpr hFree⟩
          intro hρy
          exact hFresh ((termFV_termVarMap_image_iff ρ hρ t y).mp hρy)

/-- Disjointness of bound-variable sets is invariant under injective
uniform renaming. -/
private theorem boundVariableDisjoint_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A B : FormulaN L) :
    (∀ z, ¬ (z ∈ formulaBVN (formulaVarMapN ρ A) ∧
      z ∈ formulaBVN (formulaVarMapN ρ B))) ↔
    ∀ x, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B) := by
  constructor
  · intro h x hx
    exact h (ρ x) ⟨
      (formulaBVN_formulaVarMapN_image_iff ρ hρ A x).mpr hx.1,
      (formulaBVN_formulaVarMapN_image_iff ρ hρ B x).mpr hx.2⟩
  · intro h z hz
    rcases (formulaBVN_formulaVarMapN_iff ρ A z).mp hz.1 with
      ⟨x, hxA, hρx⟩
    rcases (formulaBVN_formulaVarMapN_iff ρ B z).mp hz.2 with
      ⟨y, hyB, hρy⟩
    have hxy : x = y := hρ (hρx.trans hρy.symm)
    subst y
    exact h x ⟨hxA, hyB⟩

/-- Freshness of bound variables from free variables is invariant under
injective uniform renaming. -/
theorem boundVarsFresh_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) :
    boundVarsFresh (formulaVarMapN ρ A) ↔ boundVarsFresh A := by
  unfold boundVarsFresh
  constructor
  · intro h x hx
    exact h (ρ x) ⟨
      (formulaFVN_formulaVarMapN_image_iff ρ hρ A x).mpr hx.1,
      (formulaBVN_formulaVarMapN_image_iff ρ hρ A x).mpr hx.2⟩
  · intro h z hz
    rcases (formulaFVN_formulaVarMapN_iff ρ hρ A z).mp hz.1 with
      ⟨x, hxF, hρx⟩
    rcases (formulaBVN_formulaVarMapN_iff ρ A z).mp hz.2 with
      ⟨y, hyB, hρy⟩
    have hxy : x = y := hρ (hρx.trans hρy.symm)
    subst y
    exact h x ⟨hxF, hyB⟩

/-- Pairwise distinct quantifier bindings are invariant under injective
uniform renaming. -/
theorem distinctQuantifierBindings_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) :
    distinctQuantifierBindings (formulaVarMapN ρ A) ↔
      distinctQuantifierBindings A := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, distinctQuantifierBindings]
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, distinctQuantifierBindings]
  | neg A ih =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using ih
  | conj A B ihA ihB =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using
        and_congr ihA
          (and_congr ihB
            (boundVariableDisjoint_formulaVarMapN_iff ρ hρ A B))
  | disj A B ihA ihB =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using
        and_congr ihA
          (and_congr ihB
            (boundVariableDisjoint_formulaVarMapN_iff ρ hρ A B))
  | impl A B ihA ihB =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using
        and_congr ihA
          (and_congr ihB
            (boundVariableDisjoint_formulaVarMapN_iff ρ hρ A B))
  | all y A ih =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using
        and_congr ih
          (not_congr (formulaBVN_formulaVarMapN_image_iff ρ hρ A y))
  | ex y A ih =>
      simpa only [formulaVarMapN, distinctQuantifierBindings] using
        and_congr ih
          (not_congr (formulaBVN_formulaVarMapN_image_iff ρ hρ A y))

/-- Rectification is invariant under injective uniform renaming. -/
theorem isRectified_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L) :
    isRectified (formulaVarMapN ρ A) ↔ isRectified A := by
  unfold isRectified
  exact and_congr
    (boundVarsFresh_formulaVarMapN_iff ρ hρ A)
    (distinctQuantifierBindings_formulaVarMapN_iff ρ hρ A)

/-- Membership in a renamed finite context is existential image
membership. -/
theorem mem_formulaFinsetVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (S : LCS.Finset (FormulaN L)) (B : FormulaN L) :
    B ∈ formulaFinsetVarMapN ρ S ↔
      ∃ A ∈ S, formulaVarMapN ρ A = B := by
  exact LCS.Finset.mem_image

/-- For injective renaming, membership of a mapped formula reflects source
membership. -/
theorem formulaVarMapN_mem_formulaFinsetVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (S : LCS.Finset (FormulaN L)) (A : FormulaN L) :
    formulaVarMapN ρ A ∈ formulaFinsetVarMapN ρ S ↔ A ∈ S := by
  rw [mem_formulaFinsetVarMapN_iff]
  constructor
  · rintro ⟨B, hB, hEq⟩
    have hBA : B = A := formulaVarMapN_injective hρ hEq
    simpa [hBA] using hB
  · intro hA
    exact ⟨A, hA, rfl⟩

/-- Renaming the empty finite context is empty. -/
theorem formulaFinsetVarMapN_empty {L : Language}
    (ρ : Nat → Nat) :
    formulaFinsetVarMapN ρ
      (LCS.Finset.empty : LCS.Finset (FormulaN L)) =
        LCS.Finset.empty := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro hB
    rcases (mem_formulaFinsetVarMapN_iff ρ
      (LCS.Finset.empty : LCS.Finset (FormulaN L)) B).mp hB with
      ⟨A, hA, _⟩
    exact (LCS.Finset.not_mem_empty hA).elim
  · intro hB
    exact (LCS.Finset.not_mem_empty hB).elim

/-- Uniform renaming commutes with finite-context insertion. -/
theorem formulaFinsetVarMapN_insert {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L)
    (S : LCS.Finset (FormulaN L)) :
    formulaFinsetVarMapN ρ (LCS.Finset.insert A S) =
      LCS.Finset.insert (formulaVarMapN ρ A)
        (formulaFinsetVarMapN ρ S) := by
  exact LCS.Finset.image_insert _ A S

/-- Instance-aware form of `formulaFinsetVarMapN_insert`.  The custom
`LCS.Finset.insert` retains its `DecidableEq` argument in the term, whereas
`formulaFinsetVarMapN` is noncomputable and therefore uses a classical
instance internally.  Extensionality makes the insertion law available for
the caller's explicit instance, as required by indexed proof constructors. -/
theorem formulaFinsetVarMapN_insert_with_instance {L : Language}
    [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (A : FormulaN L)
    (S : LCS.Finset (FormulaN L)) :
    formulaFinsetVarMapN ρ (LCS.Finset.insert A S) =
      LCS.Finset.insert (formulaVarMapN ρ A)
        (formulaFinsetVarMapN ρ S) := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro hB
    rcases (mem_formulaFinsetVarMapN_iff ρ
      (LCS.Finset.insert A S) B).mp hB with ⟨C, hC, hMap⟩
    rcases LCS.Finset.mem_insert.mp hC with hCA | hCS
    · subst C
      exact LCS.Finset.mem_insert.mpr (Or.inl hMap.symm)
    · exact LCS.Finset.mem_insert.mpr
        (Or.inr ((mem_formulaFinsetVarMapN_iff ρ S B).mpr
          ⟨C, hCS, hMap⟩))
  · intro hB
    rcases LCS.Finset.mem_insert.mp hB with hBA | hBS
    · exact (mem_formulaFinsetVarMapN_iff ρ
        (LCS.Finset.insert A S) B).mpr
        ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), hBA.symm⟩
    · rcases (mem_formulaFinsetVarMapN_iff ρ S B).mp hBS with
        ⟨C, hCS, hMap⟩
      exact (mem_formulaFinsetVarMapN_iff ρ
        (LCS.Finset.insert A S) B).mpr
        ⟨C, LCS.Finset.mem_insert.mpr (Or.inr hCS), hMap⟩

/-- Uniform renaming commutes with finite-context union. -/
theorem formulaFinsetVarMapN_union {L : Language}
    (ρ : Nat → Nat) (S T : LCS.Finset (FormulaN L)) :
    formulaFinsetVarMapN ρ (LCS.Finset.union S T) =
      LCS.Finset.union
        (formulaFinsetVarMapN ρ S) (formulaFinsetVarMapN ρ T) := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro hB
    rcases (mem_formulaFinsetVarMapN_iff ρ
      (LCS.Finset.union S T) B).mp hB with ⟨A, hA, hEq⟩
    rcases LCS.Finset.mem_union.mp hA with hA | hA
    · apply LCS.Finset.mem_union.mpr
      exact Or.inl ((mem_formulaFinsetVarMapN_iff ρ S B).mpr
        ⟨A, hA, hEq⟩)
    · apply LCS.Finset.mem_union.mpr
      exact Or.inr ((mem_formulaFinsetVarMapN_iff ρ T B).mpr
        ⟨A, hA, hEq⟩)
  · intro hB
    rcases LCS.Finset.mem_union.mp hB with hB | hB
    · rcases (mem_formulaFinsetVarMapN_iff ρ S B).mp hB with
        ⟨A, hA, hEq⟩
      apply (mem_formulaFinsetVarMapN_iff ρ
        (LCS.Finset.union S T) B).mpr
      exact ⟨A, LCS.Finset.mem_union.mpr (Or.inl hA), hEq⟩
    · rcases (mem_formulaFinsetVarMapN_iff ρ T B).mp hB with
        ⟨A, hA, hEq⟩
      apply (mem_formulaFinsetVarMapN_iff ρ
        (LCS.Finset.union S T) B).mpr
      exact ⟨A, LCS.Finset.mem_union.mpr (Or.inr hA), hEq⟩

/-- Pointwise finite-context renaming is injective when formula renaming
is injective. -/
theorem formulaFinsetVarMapN_injective {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ) :
    Function.Injective
      (formulaFinsetVarMapN (L := L) ρ) := by
  intro S T hST
  apply LCS.Finset.ext
  intro A
  constructor
  · intro hA
    apply (formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ T A).mp
    rw [← hST]
    exact (formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ S A).mpr hA
  · intro hA
    apply (formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ S A).mp
    rw [hST]
    exact (formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ T A).mpr hA

/-- The standing pointwise rectification invariant is preserved and
reflected on both sides of a renamed finite sequent. -/
theorem AllRectified_formulaFinsetVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (Γ Δ : LCS.Finset (FormulaN L)) :
    AllRectified
      (formulaFinsetVarMapN ρ Γ, formulaFinsetVarMapN ρ Δ) ↔
        AllRectified (Γ, Δ) := by
  unfold AllRectified
  constructor
  · rintro ⟨hΓ, hΔ⟩
    constructor
    · intro A hA
      apply (isRectified_formulaVarMapN_iff ρ hρ A).mp
      exact hΓ (formulaVarMapN ρ A)
        ((formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ Γ A).mpr hA)
    · intro A hA
      apply (isRectified_formulaVarMapN_iff ρ hρ A).mp
      exact hΔ (formulaVarMapN ρ A)
        ((formulaVarMapN_mem_formulaFinsetVarMapN_iff ρ hρ Δ A).mpr hA)
  · rintro ⟨hΓ, hΔ⟩
    constructor
    · intro B hB
      rcases (mem_formulaFinsetVarMapN_iff ρ Γ B).mp hB with
        ⟨A, hA, rfl⟩
      exact (isRectified_formulaVarMapN_iff ρ hρ A).mpr (hΓ A hA)
    · intro B hB
      rcases (mem_formulaFinsetVarMapN_iff ρ Δ B).mp hB with
        ⟨A, hA, rfl⟩
      exact (isRectified_formulaVarMapN_iff ρ hρ A).mpr (hΔ A hA)

/-- A term is unchanged when the renaming fixes each variable that occurs
in it. -/
private theorem termVarMap_eq_self_of_fixed {L : Language}
    (ρ : Nat → Nat) (t : Term L)
    (hFixed : ∀ x, x ∈ termVariables t → ρ x = x) :
    termVarMap ρ t = t := by
  induction t with
  | var x =>
      simp only [termVarMap]
      rw [hFixed x rfl]
  | const c =>
      rfl
  | func f ts ih =>
      simp only [termVarMap]
      congr 1
      funext i
      apply ih i
      intro x hx
      exact hFixed x ⟨i, hx⟩

/-- A formula is unchanged when the renaming fixes every free or bound
variable that occurs in it. -/
theorem formulaVarMapN_eq_self_of_fixed {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L)
    (hFixed : ∀ x, x ∈ formulaAllVariables A → ρ x = x) :
    formulaVarMapN ρ A = A := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN]
      congr 1
      funext i
      apply termVarMap_eq_self_of_fixed
      intro x hx
      exact hFixed x ⟨i, hx⟩
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN]
      rw [termVarMap_eq_self_of_fixed ρ t₁
          (fun x hx => hFixed x (Or.inl hx)),
        termVarMap_eq_self_of_fixed ρ t₂
          (fun x hx => hFixed x (Or.inr hx))]
  | neg A ih =>
      simp only [formulaVarMapN]
      rw [ih hFixed]
  | conj A B ihA ihB =>
      simp only [formulaVarMapN]
      rw [ihA (fun x hx => hFixed x (Or.inl hx)),
        ihB (fun x hx => hFixed x (Or.inr hx))]
  | disj A B ihA ihB =>
      simp only [formulaVarMapN]
      rw [ihA (fun x hx => hFixed x (Or.inl hx)),
        ihB (fun x hx => hFixed x (Or.inr hx))]
  | impl A B ihA ihB =>
      simp only [formulaVarMapN]
      rw [ihA (fun x hx => hFixed x (Or.inl hx)),
        ihB (fun x hx => hFixed x (Or.inr hx))]
  | all y A ih =>
      simp only [formulaVarMapN]
      rw [hFixed y (Or.inl rfl),
        ih (fun x hx => hFixed x (Or.inr hx))]
  | ex y A ih =>
      simp only [formulaVarMapN]
      rw [hFixed y (Or.inl rfl),
        ih (fun x hx => hFixed x (Or.inr hx))]

/-- A finite context is unchanged when the renaming fixes every variable of
every member. -/
theorem formulaFinsetVarMapN_eq_self_of_fixed {L : Language}
    (ρ : Nat → Nat) (S : LCS.Finset (FormulaN L))
    (hFixed :
      ∀ A ∈ S, ∀ x, x ∈ formulaAllVariables A → ρ x = x) :
    formulaFinsetVarMapN ρ S = S := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro hB
    rcases (mem_formulaFinsetVarMapN_iff ρ S B).mp hB with
      ⟨A, hA, hEq⟩
    have hAfix :
        formulaVarMapN ρ A = A :=
      formulaVarMapN_eq_self_of_fixed ρ A (hFixed A hA)
    rw [hAfix] at hEq
    exact hEq ▸ hA
  · intro hB
    exact (mem_formulaFinsetVarMapN_iff ρ S B).mpr
      ⟨B, hB, formulaVarMapN_eq_self_of_fixed ρ B (hFixed B hB)⟩

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz
namespace MaxQuantifierOccurrence

/-- Transport a proof-relevant maximal-quantifier occurrence through uniform
variable renaming, preserving its left/right address. -/
def varMap {L : Language} (ρ : Nat → Nat) :
    {A : FormulaN L} → MaxQuantifierOccurrence A →
      MaxQuantifierOccurrence (formulaVarMapN ρ A)
  | _, .all x B =>
      .all (ρ x) (formulaVarMapN ρ B)
  | _, .ex x B =>
      .ex (ρ x) (formulaVarMapN ρ B)
  | _, .conjLeft occurrence B =>
      .conjLeft (varMap ρ occurrence) (formulaVarMapN ρ B)
  | _, .conjRight A occurrence =>
      .conjRight (formulaVarMapN ρ A) (varMap ρ occurrence)
  | _, .disjLeft occurrence B =>
      .disjLeft (varMap ρ occurrence) (formulaVarMapN ρ B)
  | _, .disjRight A occurrence =>
      .disjRight (formulaVarMapN ρ A) (varMap ρ occurrence)

/-- Transporting an occurrence renames exactly its selected formula. -/
theorem selected_varMap {L : Language} (ρ : Nat → Nat)
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A) :
    (varMap ρ occurrence).selected =
      formulaVarMapN ρ occurrence.selected := by
  induction occurrence with
  | all x B =>
      rfl
  | ex x B =>
      rfl
  | conjLeft occurrence B ih =>
      exact ih
  | conjRight A occurrence ih =>
      exact ih
  | disjLeft occurrence B ih =>
      exact ih
  | disjRight A occurrence ih =>
      exact ih

/-- Transporting an occurrence preserves its branch address. -/
theorem address_varMap {L : Language} (ρ : Nat → Nat)
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A) :
    (varMap ρ occurrence).address = occurrence.address := by
  induction occurrence with
  | all x B =>
      rfl
  | ex x B =>
      rfl
  | conjLeft occurrence B ih =>
      exact congrArg (MaxQuantifierOccurrenceStep.left :: ·) ih
  | conjRight A occurrence ih =>
      exact congrArg (MaxQuantifierOccurrenceStep.right :: ·) ih
  | disjLeft occurrence B ih =>
      exact congrArg (MaxQuantifierOccurrenceStep.left :: ·) ih
  | disjRight A occurrence ih =>
      exact congrArg (MaxQuantifierOccurrenceStep.right :: ·) ih

/-- Occurrence-selected replacement commutes with uniform renaming. -/
theorem replace_varMap {L : Language} (ρ : Nat → Nat)
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A)
    (C : FormulaN L) :
    formulaVarMapN ρ (occurrence.replace C) =
      (varMap ρ occurrence).replace (formulaVarMapN ρ C) := by
  induction occurrence with
  | all x B =>
      rfl
  | ex x B =>
      rfl
  | conjLeft occurrence B ih =>
      simp only [replace, varMap, formulaVarMapN]
      rw [ih]
  | conjRight A occurrence ih =>
      simp only [replace, varMap, formulaVarMapN]
      rw [ih]
  | disjLeft occurrence B ih =>
      simp only [replace, varMap, formulaVarMapN]
      rw [ih]
  | disjRight A occurrence ih =>
      simp only [replace, varMap, formulaVarMapN]
      rw [ih]

end MaxQuantifierOccurrence
end LCS.Herbrand.NNFHauptsatz
end

