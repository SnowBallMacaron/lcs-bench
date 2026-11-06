import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.FreshVariables
import LCS.CutElim.Interpolation.Craig.Lifting

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
namespace CraigFreshBot

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lower every indexed one-premise LK rule from the fresh-bottom language.
The proof-wide freshness fact is used only for the instantiating terms of
quantifier rules; the replacement formula is closed, so eigenvariable
freshness is preserved directly. -/
def freshLower_folkStep1_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {prem conc : Sequent (FreshBotLanguage L)}
    (rule : FOLKStep1 prem conc)
    (hvar : rule.varNotOccurs v) :
    FOLKStep1
      (freshLowerSequent (sharedPredFalse P v) prem)
      (freshLowerSequent (sharedPredFalse P v) conc) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList,
      List.map_cons] using
      (FOLKStep1.weakenLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | weakenRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.weakenRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | contractLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList,
      List.map_cons] using
      (FOLKStep1.contractLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | contractRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.contractRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | exchangeLeft Γ A B Δ Λ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeLeft
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Δ)
        (freshLowerList (sharedPredFalse P v) Λ))
  | exchangeRight Γ Δ A B Λ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeRight
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ)
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Λ))
  | andLeftL A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_cons] using
      (FOLKStep1.andLeftL
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | andLeftR A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_cons] using
      (FOLKStep1.andLeftR
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | orRightL A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightL
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | orRightR A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightR
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | implRight A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.implRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | negLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | negRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | allLeft t x A Γ Δ hfree =>
    exact freshLower_allLeft L P v t x A Γ Δ hfree hvar
  | allRight y x A Γ Δ hfresh hfreeFor =>
    exact freshLower_allRight L P v y x A Γ Δ hfresh hfreeFor hvar
  | exLeft y x A Γ Δ hfresh hfreeFor =>
    exact freshLower_exLeft L P v y x A Γ Δ hfresh hfreeFor hvar
  | exRight t x A Γ Δ hfree =>
    exact freshLower_exRight L P v t x A Γ Δ hfree hvar

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lower every indexed two-premise LK rule from the fresh-bottom language.
No extra freshness premise is needed because these rules carry no
instantiating terms or eigenvariable side conditions. -/
def freshLower_folkStep2_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {prem₁ prem₂ conc : Sequent (FreshBotLanguage L)}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2
      (freshLowerSequent (sharedPredFalse P v) prem₁)
      (freshLowerSequent (sharedPredFalse P v) prem₂)
      (freshLowerSequent (sharedPredFalse P v) conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    let lowered := FOLKStep2.cut
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      (freshLowerList (sharedPredFalse P v) Λ)
      (freshLowerList (sharedPredFalse P v) Θ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, List.map_append])
  | andRight A B Γ Δ =>
    let lowered := FOLKStep2.andRight
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_append, List.map_cons, List.map_nil])
  | orLeft A B Γ Δ =>
    let lowered := FOLKStep2.orLeft
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_cons])
  | implLeft A B Γ Δ Λ Θ =>
    let lowered := FOLKStep2.implLeft
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      (freshLowerList (sharedPredFalse P v) Λ)
      (freshLowerList (sharedPredFalse P v) Θ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_append, List.map_cons])

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Structural lowering of an indexed LK⊥ proof tree in the fresh-bottom
language. Ordinary axiom leaves remain exact axioms, the distinguished
bottom leaf becomes `sharedPredFalseRefutation`, and every internal rule is
replayed with its exact lowered indices. -/
noncomputable def freshLower_folkBotProofTree_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {s : Sequent (FreshBotLanguage L)}
    (T : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s)
    (hvar : T.varNotOccurs v) :
    FOLKProofTree
      (freshLowerSequent (sharedPredFalse P v) s) := by
  let rec transform
      {q : Sequent (FreshBotLanguage L)}
      (U : FOLKBotProofTree
        (freshBot (L := L)) (freshBot_arity (L := L)) q)
      (hU : U.varNotOccurs v) :
      FOLKProofTree
        (freshLowerSequent (sharedPredFalse P v) q) :=
    match U with
    | .axiom_ q hax => by
      by_cases hFolk : isFOLKAxiom q
      · exact FOLKProofTree.axiom_ _
          (freshLower_isFOLKAxiom_sharedPredFalse P v q hFolk)
      · have hBot := hax.resolve_left hFolk
        simpa only [freshLowerSequent, freshLowerList, hBot.1, hBot.2,
          List.map_cons, List.map_nil, freshLowerFormula_freshBot] using
          sharedPredFalseRefutation P v
    | .onePremise rule t => by
      simp only [FOLKBotProofTree.varNotOccurs] at hU
      exact FOLKProofTree.onePremise
        (freshLower_folkStep1_sharedPredFalse P v rule hU.1)
        (transform t hU.2)
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKBotProofTree.varNotOccurs] at hU
      exact FOLKProofTree.twoPremise
        (freshLower_folkStep2_sharedPredFalse P v rule)
        (transform t₁ hU.2.1) (transform t₂ hU.2.2)
  exact transform T hvar

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Choose one variable absent from both LK⊥ proof trees and lower both
trees using the same shared contradiction. This synchronization is what
keeps the two proof obligations about one and the same lowered interpolant. -/
theorem freshLower_folkBotProofTree_pair_sharedPredFalse
    {L : Language} (P : L.predSymbols)
    {s₁ s₂ : Sequent (FreshBotLanguage L)}
    (T₁ : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s₁)
    (T₂ : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s₂) :
    ∃ v,
      folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₁) ∧
        folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₂) := by
  let v :=
    Nat.max (folkBotProofAllMaxVar T₁)
      (folkBotProofAllMaxVar T₂) + 1
  have hv₁ : v > folkBotProofAllMaxVar T₁ := by
    dsimp only [v]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hv₂ : v > folkBotProofAllMaxVar T₂ := by
    dsimp only [v]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  have hvar₁ : T₁.varNotOccurs v :=
    T₁.varNotOccurs_of_gt v hv₁
  have hvar₂ : T₂.varNotOccurs v :=
    T₂.varNotOccurs_of_gt v hv₂
  exact
    ⟨v,
      ⟨freshLower_folkBotProofTree_sharedPredFalse P v T₁ hvar₁⟩,
      ⟨freshLower_folkBotProofTree_sharedPredFalse P v T₂ hvar₂⟩⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Provability-level synchronized wrapper: unpack two fresh-bottom LK⊥
derivations, choose one proof-wide fresh variable for the pair, and lower
both derivations with the same shared contradiction. -/
theorem freshLower_lkBotProvable_pair_sharedPredFalse
    {L : Language} (P : L.predSymbols)
    {s₁ s₂ : Sequent (FreshBotLanguage L)}
    (h₁ : lkBotProvable
      (freshBot (L := L)) (freshBot_arity (L := L)) s₁)
    (h₂ : lkBotProvable
      (freshBot (L := L)) (freshBot_arity (L := L)) s₂) :
    ∃ v,
      folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₁) ∧
        folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₂) := by
  rcases h₁ with ⟨T₁⟩
  rcases h₂ with ⟨T₂⟩
  exact freshLower_folkBotProofTree_pair_sharedPredFalse P T₁ T₂

end CraigFreshBot
end LCS.CutElim.Interpolation
end
