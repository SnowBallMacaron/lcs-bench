import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- A formula whose free variables are all binder-protected is fixed
by normalization. -/
private theorem closeFormulaAt_eq_self {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hBound : ∀ x, x ∈ formulaFVN A → x ∈ bound) :
    closeFormulaAt seed eigenMap bound A = A := by
  induction A generalizing bound with
  | predN P ts =>
      simp only [closeFormulaAt, FormulaN.predN.injEq,
        heq_eq_eq, true_and]
      funext i
      apply closeBaseTermAt_eq_self seed eigenMap bound
      intro x hx
      apply hBound x
      exact ⟨i, hx⟩
  | eq_ hEq lhs rhs =>
      simp only [closeFormulaAt, FormulaN.eq_.injEq,
        heq_eq_eq, true_and]
      constructor
      · apply closeBaseTermAt_eq_self seed eigenMap bound
        intro x hx
        exact hBound x (Or.inl hx)
      · apply closeBaseTermAt_eq_self seed eigenMap bound
        intro x hx
        exact hBound x (Or.inr hx)
  | neg A ih =>
      exact congrArg FormulaN.neg (ih bound hBound)
  | conj A B ihA ihB =>
      apply congrArg₂_local FormulaN.conj
      · apply ihA bound
        intro x hx
        exact hBound x (Or.inl hx)
      · apply ihB bound
        intro x hx
        exact hBound x (Or.inr hx)
  | disj A B ihA ihB =>
      apply congrArg₂_local FormulaN.disj
      · apply ihA bound
        intro x hx
        exact hBound x (Or.inl hx)
      · apply ihB bound
        intro x hx
        exact hBound x (Or.inr hx)
  | impl A B ihA ihB =>
      apply congrArg₂_local FormulaN.impl
      · apply ihA bound
        intro x hx
        exact hBound x (Or.inl hx)
      · apply ihB bound
        intro x hx
        exact hBound x (Or.inr hx)
  | all x A ih =>
      apply congrArg (FormulaN.all x)
      apply ih (x :: bound)
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · have hyFree : y ∈ formulaFVN (.all x A) := by
          simpa [formulaFVN, hyx] using hy
        simp [hyx, hBound y hyFree]
  | ex x A ih =>
      apply congrArg (FormulaN.ex x)
      apply ih (x :: bound)
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · have hyFree : y ∈ formulaFVN (.ex x A) := by
          simpa [formulaFVN, hyx] using hy
        simp [hyx, hBound y hyFree]

/-- A closed formula is fixed by capture-aware normalization. -/
private theorem closeFormula_eq_self_of_isClosed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (hClosed : FormulaN.isClosed A) :
    closeFormula seed eigenMap A = A := by
  apply closeFormulaAt_eq_self seed eigenMap [] A
  intro x hx
  unfold FormulaN.isClosed at hClosed
  rw [hClosed] at hx
  exact hx.elim

/-- Every free variable retained by formula normalization is protected
by the surrounding binder list. -/
private theorem closeFormulaAt_fv_bound {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L) :
    ∀ y, y ∈ formulaFVN
        (closeFormulaAt seed eigenMap bound A) →
      y ∈ bound := by
  induction A generalizing bound with
  | predN P ts =>
      intro y hy
      simp only [closeFormulaAt, formulaFVN] at hy
      obtain ⟨i, hi⟩ := hy
      exact closeBaseTermAt_fv_bound
        seed eigenMap bound (ts i) y hi
  | eq_ hEq lhs rhs =>
      intro y hy
      rcases hy with hy | hy
      · exact closeBaseTermAt_fv_bound
          seed eigenMap bound lhs y hy
      · exact closeBaseTermAt_fv_bound
          seed eigenMap bound rhs y hy
  | neg A ih =>
      exact ih bound
  | conj A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact ihA bound y hy
      · exact ihB bound y hy
  | disj A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact ihA bound y hy
      · exact ihB bound y hy
  | impl A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact ihA bound y hy
      · exact ihB bound y hy
  | all x A ih =>
      intro y hy
      have hyNe : y ≠ x := by
        intro hyx
        subst y
        exact hy.2 rfl
      exact
        (List.mem_cons.mp
          (ih (x :: bound) y hy.1)).resolve_left hyNe
  | ex x A ih =>
      intro y hy
      have hyNe : y ≠ x := by
        intro hyx
        subst y
        exact hy.2 rfl
      exact
        (List.mem_cons.mp
          (ih (x :: bound) y hy.1)).resolve_left hyNe

/-- Formula normalization only removes free variables; every retained
free variable came from the source formula. -/
private theorem closeFormulaAt_fv_source {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L) :
    ∀ y, y ∈ formulaFVN
        (closeFormulaAt seed eigenMap bound A) →
      y ∈ formulaFVN A := by
  induction A generalizing bound with
  | predN P ts =>
      intro y hy
      simp only [closeFormulaAt, formulaFVN] at hy
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, closeBaseTermAt_fv_source
        seed eigenMap bound (ts i) y hi⟩
  | eq_ hEq lhs rhs =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (closeBaseTermAt_fv_source
          seed eigenMap bound lhs y hy)
      · exact Or.inr (closeBaseTermAt_fv_source
          seed eigenMap bound rhs y hy)
  | neg A ih =>
      exact ih bound
  | conj A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (ihA bound y hy)
      · exact Or.inr (ihB bound y hy)
  | disj A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (ihA bound y hy)
      · exact Or.inr (ihB bound y hy)
  | impl A B ihA ihB =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (ihA bound y hy)
      · exact Or.inr (ihB bound y hy)
  | all x A ih =>
      intro y hy
      exact ⟨ih (x :: bound) y hy.1, hy.2⟩
  | ex x A ih =>
      intro y hy
      exact ⟨ih (x :: bound) y hy.1, hy.2⟩

/-- Capture-aware normalization preserves the exact set of bound
variables. -/
private theorem closeFormulaAt_formulaBVN {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L) :
    formulaBVN (closeFormulaAt seed eigenMap bound A) =
      formulaBVN A := by
  induction A generalizing bound with
  | predN _ _ =>
      rfl
  | eq_ _ _ _ =>
      rfl
  | neg A ih =>
      exact ih bound
  | conj A B ihA ihB =>
      simp only [closeFormulaAt, formulaBVN]
      rw [ihA bound, ihB bound]
  | disj A B ihA ihB =>
      simp only [closeFormulaAt, formulaBVN]
      rw [ihA bound, ihB bound]
  | impl A B ihA ihB =>
      simp only [closeFormulaAt, formulaBVN]
      rw [ihA bound, ihB bound]
  | all x A ih =>
      simp only [closeFormulaAt, formulaBVN]
      rw [ih (x :: bound)]
  | ex x A ih =>
      simp only [closeFormulaAt, formulaBVN]
      rw [ih (x :: bound)]

/-- Closing all free variables works for quantified formulae as well
as quantifier-free formulae. -/
private theorem closeFormula_isClosed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) :
    FormulaN.isClosed (closeFormula seed eigenMap A) := by
  unfold FormulaN.isClosed closeFormula
  ext y
  constructor
  · intro hy
    have hBound :=
      closeFormulaAt_fv_bound seed eigenMap [] A y hy
    exact (List.not_mem_nil hBound).elim
  · intro hy
    exact hy.elim

/-- Formula normalization changes terms only and therefore preserves
atomicity. -/
private theorem closeFormulaAt_isAtomic {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hAtom : A.isAtomic) :
    (closeFormulaAt seed eigenMap bound A).isAtomic := by
  cases A <;>
    simp_all [FormulaN.isAtomic, closeFormulaAt]

/-- Formula normalization preserves quantifier-freeness. -/
private theorem closeFormulaAt_isQuantifierFree {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree
      (closeFormulaAt seed eigenMap bound A) := by
  induction A generalizing bound with
  | predN _ _ =>
      exact trivial
  | eq_ _ _ _ =>
      exact trivial
  | neg A ih =>
      exact ih bound hQF
  | conj A B ihA ihB =>
      exact ⟨ihA bound hQF.1, ihB bound hQF.2⟩
  | disj A B ihA ihB =>
      exact ⟨ihA bound hQF.1, ihB bound hQF.2⟩
  | impl A B ihA ihB =>
      exact ⟨ihA bound hQF.1, ihB bound hQF.2⟩
  | all _ _ _ =>
      exact hQF.elim
  | ex _ _ _ =>
      exact hQF.elim

private theorem closeFormula_isQuantifierFree {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree
      (closeFormula seed eigenMap A) :=
  closeFormulaAt_isQuantifierFree
    seed eigenMap [] A hQF

/-- Formula normalization preserves negation normal form. -/
private theorem closeFormulaAt_isNNF {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hNNF : A.isNNF) :
    (closeFormulaAt seed eigenMap bound A).isNNF := by
  induction A generalizing bound with
  | predN _ _ =>
      exact trivial
  | eq_ _ _ _ =>
      exact trivial
  | neg A ih =>
      cases A with
      | predN _ _ =>
          exact trivial
      | eq_ _ _ _ =>
          exact trivial
      | neg _ =>
          exact hNNF.elim
      | conj _ _ =>
          exact hNNF.elim
      | disj _ _ =>
          exact hNNF.elim
      | impl _ _ =>
          exact hNNF.elim
      | all _ _ =>
          exact hNNF.elim
      | ex _ _ =>
          exact hNNF.elim
  | conj A B ihA ihB =>
      exact ⟨ihA bound hNNF.1, ihB bound hNNF.2⟩
  | disj A B ihA ihB =>
      exact ⟨ihA bound hNNF.1, ihB bound hNNF.2⟩
  | impl _ _ _ _ =>
      exact hNNF.elim
  | all x A ih =>
      exact ih (x :: bound) hNNF
  | ex x A ih =>
      exact ih (x :: bound) hNNF

private theorem closeFormula_isNNF {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (hNNF : A.isNNF) :
    (closeFormula seed eigenMap A).isNNF :=
  closeFormulaAt_isNNF seed eigenMap [] A hNNF

/-- Capture-aware normalization preserves structural Skolem-normal
form shape. -/
private theorem closeFormulaAt_isSkolemNormalFormShape
    {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hShape : isSkolemNormalFormShape A) :
    isSkolemNormalFormShape
      (closeFormulaAt seed eigenMap bound A) := by
  induction A generalizing bound with
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg A _ =>
      exact closeFormulaAt_isAtomic
        seed eigenMap bound A hShape
  | conj A B ihA ihB =>
      exact
        ⟨ihA bound hShape.1, ihB bound hShape.2⟩
  | disj A B ihA ihB =>
      exact
        ⟨ihA bound hShape.1, ihB bound hShape.2⟩
  | impl _ _ _ _ =>
      exact hShape.elim
  | all x A ih =>
      exact ih (x :: bound) hShape
  | ex _ _ _ =>
      exact hShape.elim

/-- Distinct quantifier bindings are unchanged because normalization
does not change binders or their connective positions. -/
private theorem closeFormulaAt_distinctQuantifierBindings
    {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hDistinct : distinctQuantifierBindings A) :
    distinctQuantifierBindings
      (closeFormulaAt seed eigenMap bound A) := by
  induction A generalizing bound with
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg A ih =>
      exact ih bound hDistinct
  | conj A B ihA ihB =>
      refine
        ⟨ihA bound hDistinct.1,
          ihB bound hDistinct.2.1, ?_⟩
      intro x hx
      apply hDistinct.2.2 x
      rw [closeFormulaAt_formulaBVN
            seed eigenMap bound A,
          closeFormulaAt_formulaBVN
            seed eigenMap bound B] at hx
      exact hx
  | disj A B ihA ihB =>
      refine
        ⟨ihA bound hDistinct.1,
          ihB bound hDistinct.2.1, ?_⟩
      intro x hx
      apply hDistinct.2.2 x
      rw [closeFormulaAt_formulaBVN
            seed eigenMap bound A,
          closeFormulaAt_formulaBVN
            seed eigenMap bound B] at hx
      exact hx
  | impl A B ihA ihB =>
      refine
        ⟨ihA bound hDistinct.1,
          ihB bound hDistinct.2.1, ?_⟩
      intro x hx
      apply hDistinct.2.2 x
      rw [closeFormulaAt_formulaBVN
            seed eigenMap bound A,
          closeFormulaAt_formulaBVN
            seed eigenMap bound B] at hx
      exact hx
  | all x A ih =>
      refine ⟨ih (x :: bound) hDistinct.1, ?_⟩
      rw [closeFormulaAt_formulaBVN
        seed eigenMap (x :: bound) A]
      exact hDistinct.2
  | ex x A ih =>
      refine ⟨ih (x :: bound) hDistinct.1, ?_⟩
      rw [closeFormulaAt_formulaBVN
        seed eigenMap (x :: bound) A]
      exact hDistinct.2

/-- Rectification is preserved: normalization can only remove free
variables, and it leaves every binder unchanged. -/
private theorem closeFormulaAt_isRectified {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L)
    (hRect : isRectified A) :
    isRectified (closeFormulaAt seed eigenMap bound A) := by
  constructor
  · intro x hx
    apply hRect.1 x
    refine
      ⟨closeFormulaAt_fv_source
          seed eigenMap bound A x hx.1, ?_⟩
    rw [← closeFormulaAt_formulaBVN
      seed eigenMap bound A]
    exact hx.2
  · exact closeFormulaAt_distinctQuantifierBindings
      seed eigenMap bound A hRect.2

private theorem closeFormula_isRectified {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (hRect : isRectified A) :
    isRectified (closeFormula seed eigenMap A) :=
  closeFormulaAt_isRectified
    seed eigenMap [] A hRect

/-- Protecting one additional variable absent from a term does not
change that term's normalization. -/
private theorem closeBaseTermAt_cons_of_not_mem {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (u : Term L) (y : Nat)
    (hy : y ∉ termFV u) :
    closeBaseTermAt seed eigenMap (y :: bound) u =
      closeBaseTermAt seed eigenMap bound u := by
  induction u with
  | var x =>
      have hyx : y ≠ x := by
        intro h
        subst y
        exact hy (by simp [termFV])
      have hxy : x ≠ y := fun h => hyx h.symm
      simp [closeBaseTermAt, hxy]
  | const _ =>
      rfl
  | func f ts ih =>
      simp only [closeBaseTermAt, Term.func.injEq,
        heq_eq_eq, true_and]
      funext i
      apply ih i
      intro hi
      apply hy
      exact ⟨i, hi⟩

/-- Capture-aware term normalization commutes with substitution when
the substituted variable is not already binder-protected. -/
private theorem closeBaseTermAt_termSubst {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (u t : Term L) (x : Nat)
    (hxBound : x ∉ bound) :
    closeBaseTermAt seed eigenMap bound (termSubst u t x) =
      termSubst
        (closeBaseTermAt seed eigenMap (x :: bound) u)
        (closeBaseTermAt seed eigenMap bound t) x := by
  induction u with
  | var y =>
      by_cases hyx : y = x
      · subst y
        simp [termSubst, closeBaseTermAt, hxBound]
      · simp only [termSubst, if_neg hyx]
        rw [closeBaseTermAt_cons_of_not_mem
          seed eigenMap bound (.var y) x (by
            intro hx
            have hxy : x = y := by
              simpa [termFV] using hx
            exact hyx hxy.symm)]
        have hxFree :
            x ∉ termFV
              (closeBaseTermAt seed eigenMap bound (.var y)) := by
          intro hx
          exact hxBound
            (closeBaseTermAt_fv_bound
              seed eigenMap bound (.var y) x hx)
        exact
          (termSubst_not_free
            (closeBaseTermAt seed eigenMap bound (.var y))
            (closeBaseTermAt seed eigenMap bound t)
            x hxFree).symm
  | const _ =>
      rfl
  | func f ts ih =>
      simp only [termSubst, closeBaseTermAt,
        Term.func.injEq, heq_eq_eq, true_and]
      funext i
      exact ih i

/-- Capture-aware formula normalization commutes with a free-for
substitution.  The source variable is protected while the body is
normalized, and the rule term is closed using the current prefix map. -/
private theorem closeFormulaAt_formulaSubstN {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (A : FormulaN L) (t : Term L) (x : Nat)
    (hxBound : x ∉ bound)
    (hFree : isFreeForN t x A) :
    closeFormulaAt seed eigenMap bound (formulaSubstN A t x) =
      formulaSubstN
        (closeFormulaAt seed eigenMap (x :: bound) A)
        (closeBaseTermAt seed eigenMap bound t) x := by
  induction A generalizing bound with
  | predN P ts =>
      simp only [formulaSubstN, closeFormulaAt,
        FormulaN.predN.injEq, heq_eq_eq, true_and]
      funext i
      exact closeBaseTermAt_termSubst
        seed eigenMap bound (ts i) t x hxBound
  | eq_ hEq lhs rhs =>
      simp only [formulaSubstN, closeFormulaAt,
        FormulaN.eq_.injEq, heq_eq_eq, true_and]
      exact
        ⟨closeBaseTermAt_termSubst
            seed eigenMap bound lhs t x hxBound,
          closeBaseTermAt_termSubst
            seed eigenMap bound rhs t x hxBound⟩
  | neg A ih =>
      exact congrArg FormulaN.neg
        (ih bound hxBound hFree)
  | conj A B ihA ihB =>
      exact congrArg₂_local FormulaN.conj
        (ihA bound hxBound hFree.1)
        (ihB bound hxBound hFree.2)
  | disj A B ihA ihB =>
      exact congrArg₂_local FormulaN.disj
        (ihA bound hxBound hFree.1)
        (ihB bound hxBound hFree.2)
  | impl A B ihA ihB =>
      exact congrArg₂_local FormulaN.impl
        (ihA bound hxBound hFree.1)
        (ihB bound hxBound hFree.2)
  | all y A ih =>
      by_cases hxy : x = y
      · subst y
        simp only [formulaSubstN, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, closeFormulaAt]
        apply congrArg (FormulaN.all x)
        apply closeFormulaAt_congr
        intro z
        simp
      · have hxyBool : (x != y) = true := by
          simp [hxy]
        have hFreeBody :
            y ∉ termFV t ∧ isFreeForN t x A := by
          simpa [isFreeForN, hxy] using hFree
        have hxBound' : x ∉ y :: bound := by
          simp [hxy, hxBound]
        simp only [formulaSubstN, hxyBool, ↓reduceIte,
          closeFormulaAt]
        apply congrArg (FormulaN.all y)
        rw [ih (y :: bound) hxBound' hFreeBody.2]
        rw [closeBaseTermAt_cons_of_not_mem
          seed eigenMap bound t y hFreeBody.1]
        apply congrArg₂_local (fun body term =>
          formulaSubstN body term x)
        · apply closeFormulaAt_congr
          intro z
          simp [or_left_comm]
        · rfl
  | ex y A ih =>
      by_cases hxy : x = y
      · subst y
        simp only [formulaSubstN, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, closeFormulaAt]
        apply congrArg (FormulaN.ex x)
        apply closeFormulaAt_congr
        intro z
        simp
      · have hxyBool : (x != y) = true := by
          simp [hxy]
        have hFreeBody :
            y ∉ termFV t ∧ isFreeForN t x A := by
          simpa [isFreeForN, hxy] using hFree
        have hxBound' : x ∉ y :: bound := by
          simp [hxy, hxBound]
        simp only [formulaSubstN, hxyBool, ↓reduceIte,
          closeFormulaAt]
        apply congrArg (FormulaN.ex y)
        rw [ih (y :: bound) hxBound' hFreeBody.2]
        rw [closeBaseTermAt_cons_of_not_mem
          seed eigenMap bound t y hFreeBody.1]
        apply congrArg₂_local (fun body term =>
          formulaSubstN body term x)
        · apply closeFormulaAt_congr
          intro z
          simp [or_left_comm]
        · rfl

/-- Standalone form of the formula-substitution commutation law. -/
private theorem closeFormula_formulaSubstN {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hFree : isFreeForN t x A) :
    closeFormula seed eigenMap (formulaSubstN A t x) =
      formulaSubstN
        (closeFormulaAt seed eigenMap [x] A)
        (closeSkolemTermWithSeed seed eigenMap t) x := by
  exact closeFormulaAt_formulaSubstN
    seed eigenMap [] A t x (by simp) hFree

/-- A closed term is free for every variable in every formula. -/
private theorem isFreeForN_of_isClosed_local {L : Language}
    (t : Term L) (hClosed : Term.isClosed t)
    (x : Nat) (A : FormulaN L) :
    isFreeForN t x A := by
  induction A generalizing x with
  | predN _ _ =>
      simp [isFreeForN]
  | eq_ _ _ _ =>
      simp [isFreeForN]
  | neg A ih =>
      exact ih x
  | conj A B ihA ihB =>
      exact ⟨ihA x, ihB x⟩
  | disj A B ihA ihB =>
      exact ⟨ihA x, ihB x⟩
  | impl A B ihA ihB =>
      exact ⟨ihA x, ihB x⟩
  | all y A ih =>
      simp only [isFreeForN]
      right
      refine ⟨?_, ih x⟩
      intro hy
      unfold Term.isClosed at hClosed
      rw [hClosed] at hy
      exact hy.elim
  | ex y A ih =>
      simp only [isFreeForN]
      right
      refine ⟨?_, ih x⟩
      intro hy
      unfold Term.isClosed at hClosed
      rw [hClosed] at hy
      exact hy.elim

/-- A mapped eigenvariable closes to its stored term, independently
of the fallback seed. -/
private theorem closeSkolemTermWithSeed_var_of_lookup
    {L : Language} (seed : ClosedTerm L)
    (eigenMap : ClosedEigenvarMap L) (x : Nat)
    (t : ClosedTerm L) (hLookup : eigenMap.lookup x = some t) :
    closeSkolemTermWithSeed seed eigenMap (.var x) = t.1 := by
  simp [closeSkolemTermWithSeed, closeBaseTermAt, hLookup]

/-- An unmapped eigenvariable closes to the explicit seed. -/
private theorem closeSkolemTermWithSeed_var_of_not_mapped
    {L : Language} (seed : ClosedTerm L)
    (eigenMap : ClosedEigenvarMap L) (x : Nat)
    (hLookup : eigenMap.lookup x = none) :
    closeSkolemTermWithSeed seed eigenMap (.var x) = seed.1 := by
  simp [closeSkolemTermWithSeed, closeBaseTermAt, hLookup]

/-- Transport an exact maximal quantifier occurrence through formula
normalization.  Its connective address is unchanged. -/
private def closeMaxQuantifierOccurrence {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L) :
    {A : FormulaN L} → MaxQuantifierOccurrence A →
      MaxQuantifierOccurrence (closeFormula seed eigenMap A)
  | _, .all x B =>
      .all x (closeFormulaAt seed eigenMap [x] B)
  | _, .ex x B =>
      .ex x (closeFormulaAt seed eigenMap [x] B)
  | _, .conjLeft occurrence B =>
      .conjLeft
        (closeMaxQuantifierOccurrence seed eigenMap occurrence)
        (closeFormula seed eigenMap B)
  | _, .conjRight A occurrence =>
      .conjRight (closeFormula seed eigenMap A)
        (closeMaxQuantifierOccurrence seed eigenMap occurrence)
  | _, .disjLeft occurrence B =>
      .disjLeft
        (closeMaxQuantifierOccurrence seed eigenMap occurrence)
        (closeFormula seed eigenMap B)
  | _, .disjRight A occurrence =>
      .disjRight (closeFormula seed eigenMap A)
        (closeMaxQuantifierOccurrence seed eigenMap occurrence)

/-- Transport preserves the exact selected formula. -/
private theorem closeMaxQuantifierOccurrence_selected
    {L : Language} (seed : ClosedTerm L)
    (eigenMap : ClosedEigenvarMap L)
    {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    (closeMaxQuantifierOccurrence
        seed eigenMap occurrence).selected =
      closeFormula seed eigenMap occurrence.selected := by
  induction occurrence with
  | all _ _ =>
      rfl
  | ex _ _ =>
      rfl
  | conjLeft _ _ ih =>
      exact ih
  | conjRight _ _ ih =>
      exact ih
  | disjLeft _ _ ih =>
      exact ih
  | disjRight _ _ ih =>
      exact ih

/-- Closing a formula commutes with replacement at one exact maximal
quantifier occurrence. -/
private theorem closeFormula_replace {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L) :
    closeFormula seed eigenMap
        (occurrence.replace replacement) =
      (closeMaxQuantifierOccurrence
          seed eigenMap occurrence).replace
        (closeFormula seed eigenMap replacement) := by
  induction occurrence with
  | all _ _ =>
      rfl
  | ex _ _ =>
      rfl
  | conjLeft occurrence B ih =>
      exact congrArg₂_local FormulaN.conj ih rfl
  | conjRight A occurrence ih =>
      exact congrArg₂_local FormulaN.conj rfl ih
  | disjLeft occurrence B ih =>
      exact congrArg₂_local FormulaN.disj ih rfl
  | disjRight A occurrence ih =>
      exact congrArg₂_local FormulaN.disj rfl ih

/-- Pointwise closed normalization uses the supplied decidable formula equality
to deduplicate the normalized finite component. -/
private def closeFinset {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (S : LCS.Finset (FormulaN L)) :
    LCS.Finset (FormulaN L) :=
  LCS.Finset.image (closeFormula seed eigenMap) S

private theorem closeFinset_mem {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (S : LCS.Finset (FormulaN L)) (A : FormulaN L) :
    A ∈ closeFinset seed eigenMap S ↔
      ∃ B ∈ S, closeFormula seed eigenMap B = A := by
  exact LCS.Finset.mem_image

private theorem closeFinset_insert {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (S : LCS.Finset (FormulaN L)) :
    closeFinset seed eigenMap (LCS.Finset.insert A S) =
      LCS.Finset.insert (closeFormula seed eigenMap A)
        (closeFinset seed eigenMap S) := by
  exact LCS.Finset.image_insert _ A S

private theorem closeFinset_empty {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L) :
    closeFinset seed eigenMap
      (LCS.Finset.empty : LCS.Finset (FormulaN L)) =
        LCS.Finset.empty := by
  apply LCS.Finset.ext
  intro A
  constructor
  · intro hA
    obtain ⟨B, hB, _⟩ :=
      (closeFinset_mem seed eigenMap
        (LCS.Finset.empty : LCS.Finset (FormulaN L)) A).mp hA
    exact (LCS.Finset.not_mem_empty hB).elim
  · intro hA
    exact (LCS.Finset.not_mem_empty hA).elim

/-- Image collisions can shrink a finite component but cannot erase
all of a nonempty component. -/
private theorem closeFinset_ne_empty {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (S : LCS.Finset (FormulaN L))
    (hS : S ≠ LCS.Finset.empty) :
    closeFinset seed eigenMap S ≠ LCS.Finset.empty := by
  intro hClose
  apply hS
  apply LCS.Finset.ext
  intro A
  constructor
  · intro hA
    have hImage :
        closeFormula seed eigenMap A ∈
          closeFinset seed eigenMap S :=
      (closeFinset_mem seed eigenMap S
        (closeFormula seed eigenMap A)).mpr
        ⟨A, hA, rfl⟩
    rw [hClose] at hImage
    exact (LCS.Finset.not_mem_empty hImage).elim
  · intro hA
    exact (LCS.Finset.not_mem_empty hA).elim

private theorem closeFinset_singleton_closed {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) (hClosed : FormulaN.isClosed A) :
    closeFinset seed eigenMap
        ({A} : LCS.Finset (FormulaN L)) =
      ({A} : LCS.Finset (FormulaN L)) := by
  rw [show ({A} : LCS.Finset (FormulaN L)) =
      LCS.Finset.insert A LCS.Finset.empty from rfl,
    closeFinset_insert,
    closeFormula_eq_self_of_isClosed
      seed eigenMap A hClosed,
    closeFinset_empty]

/-- Every member of a normalized finite component is closed. -/
private theorem closeFinset_allClosed {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (S : LCS.Finset (FormulaN L)) :
    ∀ A, A ∈ closeFinset seed eigenMap S →
      FormulaN.isClosed A := by
  intro A hA
  obtain ⟨B, _, rfl⟩ :=
    (closeFinset_mem seed eigenMap S A).mp hA
  exact closeFormula_isClosed seed eigenMap B

/-- Pointwise normalization preserves rectification of a finite
component. -/
private theorem closeFinset_allRectified {L : Language}
    [DecidableEq (FormulaN L)]
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (S : LCS.Finset (FormulaN L))
    (hRect : ∀ A, A ∈ S → isRectified A) :
    ∀ A, A ∈ closeFinset seed eigenMap S →
      isRectified A := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ :=
    (closeFinset_mem seed eigenMap S A).mp hA
  exact closeFormula_isRectified
    seed eigenMap B (hRect B hB)

-- ===================================================================
-- Lemma 7.6.2: chronological closed lower-path state
-- ===================================================================

/-- The all-variable carrier agrees with ordinary term free variables.
This small bridge lets occurrence-sensitive purity, which is deliberately
stated with `formulaAllVariables`, rule out a free-variable witness. -/
private theorem termVariables_eq_termFV {L : Language}
    (t : Term L) :
    termVariables t = termFV t := by
  induction t with
  | var _ =>
      rfl
  | const _ =>
      rfl
  | func f ts ih =>
      simp only [termVariables, termFV]
      congr 1
      funext i
      exact ih i

/-- Every free formula variable is, in particular, an all-variable
occurrence. -/
private theorem formulaFVN_mem_formulaAllVariables
    {L : Language} (A : FormulaN L) (y : Nat)
    (hy : y ∈ formulaFVN A) :
    y ∈ formulaAllVariables A := by
  induction A with
  | predN P ts =>
      simp only [formulaFVN, formulaAllVariables] at hy ⊢
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, by
        change y ∈ termVariables (ts i)
        rw [termVariables_eq_termFV]
        exact hi⟩
  | eq_ hEq lhs rhs =>
      simp only [formulaFVN, formulaAllVariables] at hy ⊢
      rcases hy with hy | hy
      · exact Or.inl (by
          rw [termVariables_eq_termFV]
          exact hy)
      · exact Or.inr (by
          rw [termVariables_eq_termFV]
          exact hy)
  | neg B ih =>
      exact ih hy
  | conj B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | disj B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | impl B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | all x B ih =>
      exact Or.inr (ih hy.1)
  | ex x B ih =>
      exact Or.inr (ih hy.1)

/-- Term substitution cannot erase a different source variable. -/
private theorem termFV_termSubst_of_mem_of_ne
    {L : Language} (u t : Term L) (x y : Nat)
    (hy : y ∈ termFV u) (hyx : y ≠ x) :
    y ∈ termFV (termSubst u t x) := by
  induction u with
  | var z =>
      have hyz : y = z := hy
      subst z
      simp [termSubst, termFV, hyx]
  | const _ =>
      exact hy.elim
  | func f us ih =>
      simp only [termFV] at hy ⊢
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, ih i hi⟩

/-- If `x` occurs in a term, substituting the variable `y` for `x`
introduces `y`. -/
private theorem termFV_termSubst_var_of_mem
    {L : Language} (u : Term L) (x y : Nat)
    (hx : x ∈ termFV u) :
    y ∈ termFV (termSubst u (.var y) x) := by
  induction u with
  | var z =>
      have hxz : x = z := hx
      subst z
      simp [termSubst, termFV]
  | const _ =>
      exact hx.elim
  | func f us ih =>
      simp only [termFV] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, ih i hi⟩

/-- Substitution cannot erase a different free variable.  This is the
forward counterpart of the imported FV-substitution containment lemma. -/
private theorem formulaFVN_formulaSubstN_of_mem_of_ne
    {L : Language} (A : FormulaN L) (t : Term L)
    (x y : Nat) (hy : y ∈ formulaFVN A) (hyx : y ≠ x) :
    y ∈ formulaFVN (formulaSubstN A t x) := by
  induction A with
  | predN P ts =>
      simp only [formulaFVN] at hy ⊢
      obtain ⟨i, hi⟩ := hy
      exact ⟨i,
        termFV_termSubst_of_mem_of_ne (ts i) t x y hi hyx⟩
  | eq_ hEq lhs rhs =>
      simp only [formulaFVN] at hy ⊢
      rcases hy with hy | hy
      · exact Or.inl
          (termFV_termSubst_of_mem_of_ne lhs t x y hy hyx)
      · exact Or.inr
          (termFV_termSubst_of_mem_of_ne rhs t x y hy hyx)
  | neg B ih =>
      exact ih hy
  | conj B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | disj B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | impl B C ihB ihC =>
      rcases hy with hy | hy
      · exact Or.inl (ihB hy)
      · exact Or.inr (ihC hy)
  | all z B ih =>
      simp only [formulaFVN] at hy ⊢
      obtain ⟨hyB, hyz⟩ := hy
      simp only [formulaSubstN]
      by_cases hxz : x = z
      · subst z
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false,
          formulaFVN]
        change formulaFVN B y ∧ ¬Set.singleton x y
        exact ⟨hyB, hyz⟩
      · simp only [bne_iff_ne.mpr hxz, if_true, formulaFVN]
        exact ⟨ih hyB, hyz⟩
  | ex z B ih =>
      simp only [formulaFVN] at hy ⊢
      obtain ⟨hyB, hyz⟩ := hy
      simp only [formulaSubstN]
      by_cases hxz : x = z
      · subst z
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false,
          formulaFVN]
        change formulaFVN B y ∧ ¬Set.singleton x y
        exact ⟨hyB, hyz⟩
      · simp only [bne_iff_ne.mpr hxz, if_true, formulaFVN]
        exact ⟨ih hyB, hyz⟩

/-- Replacing one selected maximal quantifier preserves every free
variable already present in the ambient formula, provided the replacement
is obtained by substituting in the selected body. -/
private theorem maxQuantifierOccurrence_replace_subst_fv
    {L : Language} {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B ∨
        occurrence.selected = FormulaN.ex x B) :
    ∀ y, y ∈ formulaFVN A →
      y ∈ formulaFVN
        (occurrence.replace (formulaSubstN B t x)) := by
  induction occurrence with
  | all z C =>
      intro y hy
      rcases hSelected with hSelected | hSelected
      · have hzx : z = x := by
          cases hSelected
          rfl
        have hCB : C = B := by
          cases hSelected
          rfl
        subst z
        subst C
        exact
          formulaFVN_formulaSubstN_of_mem_of_ne
            B t x y hy.1 hy.2
      · cases hSelected
  | ex z C =>
      intro y hy
      rcases hSelected with hSelected | hSelected
      · cases hSelected
      · have hzx : z = x := by
          cases hSelected
          rfl
        have hCB : C = B := by
          cases hSelected
          rfl
        subst z
        subst C
        exact
          formulaFVN_formulaSubstN_of_mem_of_ne
            B t x y hy.1 hy.2
  | conjLeft inner C ih =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (ih hSelected y hy)
      · exact Or.inr hy
  | conjRight C inner ih =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (ih hSelected y hy)
  | disjLeft inner C ih =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (ih hSelected y hy)
      · exact Or.inr hy
  | disjRight C inner ih =>
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (ih hSelected y hy)

/-- A free variable of the supplied replacement is free in the ambient
formula after exact occurrence replacement. -/
private theorem maxQuantifierOccurrence_replace_fv_of_replacement
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L) (y : Nat)
    (hy : y ∈ formulaFVN replacement) :
    y ∈ formulaFVN (occurrence.replace replacement) := by
  induction occurrence with
  | all _ _ =>
      exact hy
  | ex _ _ =>
      exact hy
  | conjLeft inner C ih =>
      exact Or.inl ih
  | conjRight C inner ih =>
      exact Or.inr ih
  | disjLeft inner C ih =>
      exact Or.inl ih
  | disjRight C inner ih =>
      exact Or.inr ih

/-- If `x` genuinely occurs free in `B`, a free-for substitution of the
fresh variable `y` makes `y` occur free in `B[y/x]`.  The free-for premise
is exactly what excludes capture at a quantifier binding `y`. -/
private theorem formulaFVN_formulaSubstN_var_of_relevant
    {L : Language} (B : FormulaN L) (x y : Nat)
    (hRelevant : x ∈ formulaFVN B)
    (hFreeFor : isFreeForN (.var y) x B) :
    y ∈ formulaFVN (formulaSubstN B (.var y) x) := by
  induction B with
  | predN P ts =>
      simp only [formulaFVN] at hRelevant ⊢
      obtain ⟨i, hi⟩ := hRelevant
      exact ⟨i, termFV_termSubst_var_of_mem (ts i) x y hi⟩
  | eq_ hEq lhs rhs =>
      simp only [formulaFVN] at hRelevant ⊢
      rcases hRelevant with hRelevant | hRelevant
      · exact Or.inl
          (termFV_termSubst_var_of_mem lhs x y hRelevant)
      · exact Or.inr
          (termFV_termSubst_var_of_mem rhs x y hRelevant)
  | neg C ih =>
      exact ih hRelevant hFreeFor
  | conj C D ihC ihD =>
      rcases hRelevant with hRelevant | hRelevant
      · exact Or.inl (ihC hRelevant hFreeFor.1)
      · exact Or.inr (ihD hRelevant hFreeFor.2)
  | disj C D ihC ihD =>
      rcases hRelevant with hRelevant | hRelevant
      · exact Or.inl (ihC hRelevant hFreeFor.1)
      · exact Or.inr (ihD hRelevant hFreeFor.2)
  | impl C D ihC ihD =>
      rcases hRelevant with hRelevant | hRelevant
      · exact Or.inl (ihC hRelevant hFreeFor.1)
      · exact Or.inr (ihD hRelevant hFreeFor.2)
  | all z C ih =>
      simp only [formulaFVN] at hRelevant ⊢
      obtain ⟨hxC, hxz⟩ := hRelevant
      rcases hFreeFor with hEq | ⟨hyz, hFreeFor⟩
      · exact (hxz hEq).elim
      · simp only [formulaSubstN,
          bne_iff_ne.mpr hxz, if_true, formulaFVN]
        refine ⟨ih hxC hFreeFor, ?_⟩
        intro hyEq
        apply hyz
        exact hyEq.symm
  | ex z C ih =>
      simp only [formulaFVN] at hRelevant ⊢
      obtain ⟨hxC, hxz⟩ := hRelevant
      rcases hFreeFor with hEq | ⟨hyz, hFreeFor⟩
      · exact (hxz hEq).elim
      · simp only [formulaSubstN,
          bne_iff_ne.mpr hxz, if_true, formulaFVN]
        refine ⟨ih hxC hFreeFor, ?_⟩
        intro hyEq
        apply hyz
        exact hyEq.symm

/-- Every variable in the supplied chronological list still has a
free occurrence in the current antecedent.  This is the live invariant
used to turn occurrence-sensitive purity into pairwise freshness. -/
def AntecedentVariablesLive
    {L : Language} (variables : List Nat)
    (Gamma : LCS.Finset (FormulaN L)) : Prop :=
  ∀ y, y ∈ variables →
    ∃ A, A ∈ Gamma ∧ y ∈ formulaFVN A

/-- A principal left quantifier step preserves every already-live
antecedent variable.  The exact maximal occurrence is replaced, while
raw-context witnesses remain unchanged. -/
private theorem antecedentVariablesLive_replaceSubst
    {L : Language} [DecidableEq (FormulaN L)]
    {variables : List Nat} {Gamma : LCS.Finset (FormulaN L)}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B ∨
        occurrence.selected = FormulaN.ex x B)
    (hLive :
      AntecedentVariablesLive variables
        (LCS.Finset.insert A Gamma)) :
    AntecedentVariablesLive variables
      (LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x))
        Gamma) := by
  intro y hy
  obtain ⟨F, hF, hyF⟩ := hLive y hy
  rcases LCS.Finset.mem_insert.mp hF with hFA | hFContext
  · subst F
    exact
      ⟨occurrence.replace (formulaSubstN B t x),
        LCS.Finset.mem_insert.mpr (Or.inl rfl),
        maxQuantifierOccurrence_replace_subst_fv
          occurrence x t hSelected y hyF⟩
  · exact
      ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hFContext), hyF⟩

/-- Append one freshly witnessed variable to a live chronological list. -/
theorem antecedentVariablesLive_append_singleton
    {L : Language} {variables : List Nat} {y : Nat}
    {Gamma : LCS.Finset (FormulaN L)}
    (hLive : AntecedentVariablesLive variables Gamma)
    (hNew : ∃ A, A ∈ Gamma ∧ y ∈ formulaFVN A) :
    AntecedentVariablesLive (variables ++ [y]) Gamma := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hLive z hz
  · have hzy : z = y := List.mem_singleton.mp hz
    subst z
    exact hNew

/-- Occurrence-sensitive freedom of the current sequent excludes its
variable from any live antecedent chronology. -/
theorem not_mem_of_g2nnfSequentVariableFree_of_live
    {L : Language} [DecidableEq (FormulaN L)]
    {variables : List Nat} {y : Nat}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (hFree : g2nnfSequentVariableFree y Gamma Delta)
    (hLive : AntecedentVariablesLive variables Gamma) :
    y ∉ variables := by
  intro hy
  obtain ⟨A, hA, hyA⟩ := hLive y hy
  exact hFree A (Or.inl hA)
    (formulaFVN_mem_formulaAllVariables A y hyA)

/-- Equality-system occurrence-sensitive freedom has the same live-list
consequence. -/
theorem not_mem_of_g2nnfEqSequentVariableFree_of_live
    {L : Language} [DecidableEq (FormulaN L)]
    {variables : List Nat} {y : Nat}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (hFree : g2nnfEqSequentVariableFree y Gamma Delta)
    (hLive : AntecedentVariablesLive variables Gamma) :
    y ∉ variables := by
  intro hy
  obtain ⟨A, hA, hyA⟩ := hLive y hy
  exact hFree A (Or.inl hA)
    (formulaFVN_mem_formulaAllVariables A y hyA)

/-- Restrict occurrence-sensitive purity from a composed G2nnf path to
its exact suffix. -/
private theorem g2nnfVariableOccursOnlyAlongPath_suffix
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaMid DeltaMid GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq GammaRoot DeltaRoot}
    {mid : G2nnfProofTree hNoEq GammaMid DeltaMid}
    {node : G2nnfProofTree hNoEq GammaNode DeltaNode}
    (y : Nat)
    (pathPrefix : G2nnfProofTree.RootToNodePath root mid)
    (suffix : G2nnfProofTree.RootToNodePath mid node)
    (hOnly :
      g2nnfVariableOccursOnlyAlongPath y
        (pathPrefix.trans suffix)) :
    g2nnfVariableOccursOnlyAlongPath y suffix := by
  induction pathPrefix with
  | root _ =>
      exact hOnly
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      exact ih suffix hOnly.2
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ih suffix hOnly.2.2
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ih suffix hOnly.2.2

/-- Equality-system suffix restriction for occurrence-sensitive purity. -/
theorem g2nnfEqVariableOccursOnlyAlongPath_suffix
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaMid DeltaMid GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL GammaRoot DeltaRoot}
    {mid : G2nnfEqProofTree hL GammaMid DeltaMid}
    {node : G2nnfEqProofTree hL GammaNode DeltaNode}
    (y : Nat)
    (pathPrefix : G2nnfEqProofTree.RootToNodePath root mid)
    (suffix : G2nnfEqProofTree.RootToNodePath mid node)
    (hOnly :
      g2nnfEqVariableOccursOnlyAlongPath y
        (pathPrefix.trans suffix)) :
    g2nnfEqVariableOccursOnlyAlongPath y suffix := by
  induction pathPrefix with
  | root _ =>
      exact hOnly
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      exact ih suffix hOnly.2
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ih suffix hOnly.2.2
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ih suffix hOnly.2.2

/-- Every one-premise Core quantifier rule transports the already-live
antecedent chronology to its exact stored-context premise. -/
theorem g2nnfQuantifierPremise_preserves_live
    {L : Language} [DecidableEq (FormulaN L)]
    {variables : List Nat} (rule : G2nnfRuleCore L)
    (hPrem : rule.premises.length = 1)
    (hQuantifier : rule.isQuantifierRule)
    (hLive : AntecedentVariablesLive variables rule.conclusion.1) :
    AntecedentVariablesLive variables
      (rule.premises[0]'(by omega)).1 := by
  cases rule <;>
    simp only [G2nnfRuleCore.isQuantifierRule] at hQuantifier
  next A occurrence x B t hSelected Gamma Delta =>
    exact antecedentVariablesLive_replaceSubst
      occurrence x t (Or.inl hSelected) hLive
  next A occurrence x B y hSelected Gamma Delta =>
    exact hLive
  next A occurrence x B y hSelected Gamma Delta =>
    exact antecedentVariablesLive_replaceSubst
      occurrence x (.var y) (Or.inr hSelected) hLive
  next A occurrence x B t hSelected Gamma Delta =>
    exact hLive

/-- Equality quantifier inferences use the same stored-context Core rule
and preserve the same exact live antecedent chronology. -/
theorem g2nnfEqQuantifierPremise_preserves_live
    {L : Language} [DecidableEq (FormulaN L)]
    {variables : List Nat} (rule : G2nnfRuleCore L)
    (hPrem : rule.premises.length = 1)
    (hQuantifier : rule.isQuantifierRule)
    (hLive : AntecedentVariablesLive variables rule.conclusion.1) :
    AntecedentVariablesLive variables
      (rule.premises[0]'(by omega)).1 :=
  g2nnfQuantifierPremise_preserves_live rule hPrem hQuantifier hLive

/-- Relevance plus the rule's free-for side condition supplies the new
eigenvariable's concrete free occurrence in the exact G2nnf premise. -/
theorem g2nnfExSubLeft_eigenvariable_witness
    {L : Language} [DecidableEq (FormulaN L)]
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hSC :
      G2nnfRuleCore.SideConditions
        (.exSubLeft A occurrence x B y hSelected Gamma Delta))
    (hRelevant : x ∈ formulaFVN B) :
    ∃ F,
      F ∈ LCS.Finset.insert
        (occurrence.replace
          (formulaSubstN B (.var y) x)) Gamma ∧
      y ∈ formulaFVN F := by
  let replacement :=
    occurrence.replace (formulaSubstN B (.var y) x)
  refine
    ⟨replacement, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
  apply maxQuantifierOccurrence_replace_fv_of_replacement
    occurrence (formulaSubstN B (.var y) x) y
  exact formulaFVN_formulaSubstN_var_of_relevant
    B x y hRelevant hSC.logical.1

/-- The shared Core relevance/free-for witness also applies to equality
inferences, with the same exact occurrence and context. -/
theorem g2nnfEqExSubLeft_eigenvariable_witness
    {L : Language}
    [DecidableEq (FormulaN L)]
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hSC :
      G2nnfRuleCore.SideConditions
        (.exSubLeft A occurrence x B y hSelected Gamma Delta))
    (hRelevant : x ∈ formulaFVN B) :
    ∃ F,
      F ∈ LCS.Finset.insert
        (occurrence.replace
          (formulaSubstN B (.var y) x)) Gamma ∧
      y ∈ formulaFVN F :=
  g2nnfExSubLeft_eigenvariable_witness
    A B occurrence x y hSelected Gamma Delta hSC hRelevant

/-- At an exact G2nnf existential-left occurrence, whole-proof purity
provides both freedom of the current conclusion and purity of the exact
premise occurrence. -/
theorem g2nnfExSubLeft_purity_step
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot : LCS.Finset (FormulaN L)}
    {outer : G2nnfProofTree hNoEq GammaRoot DeltaRoot}
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hPrem :
      (G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises.length = 1)
    (hSC :
      G2nnfRuleCore.SideConditions
        (.exSubLeft A occurrence x B y hSelected Gamma Delta))
    (sub : G2nnfProofTree hNoEq
      (((G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1
      (((G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).2)
    (pathPrefix : G2nnfProofTree.RootToNodePath outer
      (.onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial hPrem hSC sub))
    (hPure :
      isPureVariableProofG2nnfAux outer
        (.onePremise
          (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub)
        pathPrefix) :
    let step : G2nnfProofTree.RootToNodePath
        (.onePremise
          (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub)
        sub :=
      .onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub (.root sub)
    g2nnfSequentVariableFree y
        (LCS.Finset.insert A Gamma) Delta ∧
      isPureVariableProofG2nnfAux outer sub
        (pathPrefix.trans step) := by
  dsimp only
  let step : G2nnfProofTree.RootToNodePath
      (.onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub)
      sub :=
    .onePremise
      (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
      hPrem hSC sub (.root sub)
  change
    (g2nnfNoFreeBoundOverlap (hL := hNoEq) y outer ∧
      g2nnfVariableOccursOnlyAlongPath y
        (pathPrefix.trans step)) ∧
      isPureVariableProofG2nnfAux outer sub
        (pathPrefix.trans step) at hPure
  have hSuffix :=
    g2nnfVariableOccursOnlyAlongPath_suffix
      y pathPrefix step hPure.1.2
  exact ⟨hSuffix.1, hPure.2⟩

end LCS.Herbrand.SHGTheorem.Herbrand
end

