import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

private theorem termSubst_commutes_with_active_alpha {L : Language}
    (r t : Term L) (x v z : Nat)
    (hxv : x ≠ v) (hxz : x ≠ z) (hvt : v ∉ termFV t) :
    termSubst (termSubst r t x) (.var z) v =
      termSubst (termSubst r (.var z) v) t x := by
  have hComp :=
    termSubst_composition r (.var z) t x v (Ne.symm hxv)
      (by
        intro h
        change x = z at h
        exact hxz h)
  have ht : termSubst t (.var z) v = t :=
    termSubst_not_free t (.var z) v hvt
  simpa only [ht] using hComp

/-- Away from the renamed target, substitution commutes with the
scope-aware alpha traversal.  When the traversal is active, the original
free-for condition at the surrounding `v`-binder supplies `v ∉ FV(t)`. -/
private theorem alphaRenameBoundAux_formulaSubstN_of_ne {L : Language}
    (A : FormulaN L) (t : Term L) (x v z : Nat) (active : Bool)
    (hxv : x ≠ v) (hxz : x ≠ z)
    (hActive : active = true → v ∉ termFV t)
    (hFree : isFreeForN t x A) :
    alphaRenameBoundAux v z active (formulaSubstN A t x) =
      formulaSubstN (alphaRenameBoundAux v z active A) t x := by
  induction A generalizing active with
  | predN P ts =>
      cases active with
      | false =>
          rfl
      | true =>
          simp only [formulaSubstN, alphaRenameBoundAux,
            Bool.true_eq, ↓reduceIte, FormulaN.predN.injEq,
            heq_eq_eq, true_and]
          funext i
          exact termSubst_commutes_with_active_alpha
            (ts i) t x v z hxv hxz (hActive rfl)
  | eq_ hL t₁ t₂ =>
      cases active with
      | false =>
          rfl
      | true =>
          simp only [formulaSubstN, alphaRenameBoundAux,
            Bool.true_eq, ↓reduceIte, FormulaN.eq_.injEq]
          exact
            ⟨termSubst_commutes_with_active_alpha
                t₁ t x v z hxv hxz (hActive rfl),
             termSubst_commutes_with_active_alpha
                t₂ t x v z hxv hxz (hActive rfl)⟩
  | neg A ih =>
      simp only [formulaSubstN, alphaRenameBoundAux, FormulaN.neg.injEq]
      exact ih active hActive hFree
  | conj A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBoundAux,
        FormulaN.conj.injEq]
      exact
        ⟨ihA active hActive hFree.1,
         ihB active hActive hFree.2⟩
  | disj A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBoundAux,
        FormulaN.disj.injEq]
      exact
        ⟨ihA active hActive hFree.1,
         ihB active hActive hFree.2⟩
  | impl A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBoundAux,
        FormulaN.impl.injEq]
      exact
        ⟨ihA active hActive hFree.1,
         ihB active hActive hFree.2⟩
  | all q A ih =>
      by_cases hxq : x = q
      · subst q
        simp [formulaSubstN, alphaRenameBoundAux, hxv]
      · have hFreeBody : isFreeForN t x A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxq
          · exact h.2
        have hqFresh : q ∉ termFV t := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxq
          · exact h.1
        by_cases hqv : q = v
        · subst q
          have hRec :=
            ih true (fun _ => hqFresh) hFreeBody
          simp [formulaSubstN, alphaRenameBoundAux, hxv, hxz, hRec]
        · have hRec := ih active hActive hFreeBody
          simp [formulaSubstN, alphaRenameBoundAux, hxq, hqv, hRec]
  | ex q A ih =>
      by_cases hxq : x = q
      · subst q
        simp [formulaSubstN, alphaRenameBoundAux, hxv]
      · have hFreeBody : isFreeForN t x A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxq
          · exact h.2
        have hqFresh : q ∉ termFV t := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxq
          · exact h.1
        by_cases hqv : q = v
        · subst q
          have hRec :=
            ih true (fun _ => hqFresh) hFreeBody
          simp [formulaSubstN, alphaRenameBoundAux, hxv, hxz, hRec]
        · have hRec := ih active hActive hFreeBody
          simp [formulaSubstN, alphaRenameBoundAux, hxq, hqv, hRec]

/-- Factoring substitution for `v` through a fresh intermediate `z`
matches selective alpha-renaming of the resulting formula. -/
private theorem alphaRenameBound_formulaSubstN_self {L : Language}
    (A : FormulaN L) (t : Term L) (v z : Nat)
    (hzv : z ≠ v)
    (hzFV : z ∉ formulaFVN A)
    (hzBV : z ∉ formulaBVN A)
    (hFree : isFreeForN t v A) :
    alphaRenameBound (formulaSubstN A t v) v z =
      formulaSubstN (alphaRenameBoundAux v z true A) t z := by
  induction A with
  | predN P ts =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, Bool.false_eq_true, if_false,
        Bool.true_eq, if_true, FormulaN.predN.injEq,
        heq_eq_eq, true_and]
      funext i
      exact
        (termSubst_via_fresh (ts i) t v z hzv
          (fun h => hzFV ⟨i, h⟩)).symm
  | eq_ hL t₁ t₂ =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, Bool.false_eq_true, if_false,
        Bool.true_eq, if_true, FormulaN.eq_.injEq]
      exact
        ⟨(termSubst_via_fresh t₁ t v z hzv
            (fun h => hzFV (Or.inl h))).symm,
         (termSubst_via_fresh t₂ t v z hzv
            (fun h => hzFV (Or.inr h))).symm⟩
  | neg A ih =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, FormulaN.neg.injEq]
      exact ih hzFV hzBV hFree
  | conj A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, FormulaN.conj.injEq]
      exact
        ⟨ihA (fun h => hzFV (Or.inl h))
            (fun h => hzBV (Or.inl h)) hFree.1,
         ihB (fun h => hzFV (Or.inr h))
            (fun h => hzBV (Or.inr h)) hFree.2⟩
  | disj A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, FormulaN.disj.injEq]
      exact
        ⟨ihA (fun h => hzFV (Or.inl h))
            (fun h => hzBV (Or.inl h)) hFree.1,
         ihB (fun h => hzFV (Or.inr h))
            (fun h => hzBV (Or.inr h)) hFree.2⟩
  | impl A B ihA ihB =>
      simp only [formulaSubstN, alphaRenameBound,
        alphaRenameBoundAux, FormulaN.impl.injEq]
      exact
        ⟨ihA (fun h => hzFV (Or.inl h))
            (fun h => hzBV (Or.inl h)) hFree.1,
         ihB (fun h => hzFV (Or.inr h))
            (fun h => hzBV (Or.inr h)) hFree.2⟩
  | all q A ih =>
      have hzq : z ≠ q := fun h => hzBV (Or.inr h)
      by_cases hqv : q = v
      · subst q
        simp [formulaSubstN, alphaRenameBound,
          alphaRenameBoundAux, hzv]
      · have hFreeBody : isFreeForN t v A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h (Ne.symm hqv)
          · exact h.2
        have hzFVBody : z ∉ formulaFVN A := by
          intro h
          exact hzFV ⟨h, hzq⟩
        have hRec :=
          ih hzFVBody (fun h => hzBV (Or.inl h)) hFreeBody
        have hvqB : (v != q) = true :=
          bne_iff_ne.mpr (Ne.symm hqv)
        have hzqB : (z != q) = true :=
          bne_iff_ne.mpr hzq
        simp only [formulaSubstN, hvqB, hzqB, ↓reduceIte,
          alphaRenameBound, alphaRenameBoundAux, if_neg hqv]
        exact congrArg (FormulaN.all q) hRec
  | ex q A ih =>
      have hzq : z ≠ q := fun h => hzBV (Or.inr h)
      by_cases hqv : q = v
      · subst q
        simp [formulaSubstN, alphaRenameBound,
          alphaRenameBoundAux, hzv]
      · have hFreeBody : isFreeForN t v A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h (Ne.symm hqv)
          · exact h.2
        have hzFVBody : z ∉ formulaFVN A := by
          intro h
          exact hzFV ⟨h, hzq⟩
        have hRec :=
          ih hzFVBody (fun h => hzBV (Or.inl h)) hFreeBody
        have hvqB : (v != q) = true :=
          bne_iff_ne.mpr (Ne.symm hqv)
        have hzqB : (z != q) = true :=
          bne_iff_ne.mpr hzq
        simp only [formulaSubstN, hvqB, hzqB, ↓reduceIte,
          alphaRenameBound, alphaRenameBoundAux, if_neg hqv]
        exact congrArg (FormulaN.ex q) hRec

private theorem alphaRenameBinderBody_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x v z : Nat)
    (hFree : isFreeForN t x A)
    (hzA : z ∉ formulaVariableSupport A)
    (_hzt : z ∉ termFV t) (hzx : z ≠ x) :
    formulaSubstN (alphaRenameBinderBody A x v z) t
        (alphaRenameBinderIndex x v z) =
      alphaRenameBound (formulaSubstN A t x) v z := by
  have hzFV : z ∉ formulaFVN A :=
    fun h => hzA (formulaFVN_mem_formulaVariableSupport A z h)
  have hzBV : z ∉ formulaBVN A :=
    fun h => hzA (formulaBVN_mem_formulaVariableSupport A z h)
  by_cases hxv : x = v
  · subst v
    simp only [alphaRenameBinderBody, if_pos rfl,
      alphaRenameBinderIndex, if_pos rfl]
    exact
      (alphaRenameBound_formulaSubstN_self
        A t x z hzx hzFV hzBV hFree).symm
  · simp only [alphaRenameBinderBody, if_neg hxv,
      alphaRenameBinderIndex, if_neg hxv]
    exact
      (alphaRenameBoundAux_formulaSubstN_of_ne
        A t x v z false hxv (Ne.symm hzx)
          (by simp) hFree).symm

private theorem alphaRenameBoundAux_true_isFreeForN {L : Language}
    (A : FormulaN L) (t : Term L) (x v z : Nat)
    (hFree : isFreeForN t x A)
    (hzt : z ∉ termFV t)
    (hzBV : z ∉ formulaBVN A) :
    isFreeForN t (if x = v then z else x)
      (alphaRenameBoundAux v z true A) := by
  induction A generalizing x with
  | predN P ts =>
      trivial
  | eq_ hL t₁ t₂ =>
      trivial
  | neg A ih =>
      exact ih x hFree hzBV
  | conj A B ihA ihB =>
      exact
        ⟨ihA x hFree.1 (fun h => hzBV (Or.inl h)),
         ihB x hFree.2 (fun h => hzBV (Or.inr h))⟩
  | disj A B ihA ihB =>
      exact
        ⟨ihA x hFree.1 (fun h => hzBV (Or.inl h)),
         ihB x hFree.2 (fun h => hzBV (Or.inr h))⟩
  | impl A B ihA ihB =>
      exact
        ⟨ihA x hFree.1 (fun h => hzBV (Or.inl h)),
         ihB x hFree.2 (fun h => hzBV (Or.inr h))⟩
  | all q A ih =>
      have hzBody : z ∉ formulaBVN A :=
        fun h => hzBV (Or.inl h)
      by_cases hqv : q = v
      · subst q
        by_cases hxv : x = v
        · subst x
          simp [alphaRenameBoundAux, isFreeForN]
        · have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxv
            · exact h.2
          simp only [alphaRenameBoundAux, if_pos rfl, isFreeForN,
            if_neg hxv]
          exact Or.inr
            ⟨hzt,
             by
               simpa only [if_neg hxv] using
                 ih x hFreeBody hzBody⟩
      · by_cases hxq : x = q
        · subst x
          simp [alphaRenameBoundAux, hqv, isFreeForN]
        · have hFreshQ : q ∉ termFV t := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.1
          have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.2
          simp only [alphaRenameBoundAux, if_neg hqv, isFreeForN]
          exact Or.inr
            ⟨hFreshQ, ih x hFreeBody hzBody⟩
  | ex q A ih =>
      have hzBody : z ∉ formulaBVN A :=
        fun h => hzBV (Or.inl h)
      by_cases hqv : q = v
      · subst q
        by_cases hxv : x = v
        · subst x
          simp [alphaRenameBoundAux, isFreeForN]
        · have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxv
            · exact h.2
          simp only [alphaRenameBoundAux, if_pos rfl, isFreeForN,
            if_neg hxv]
          exact Or.inr
            ⟨hzt,
             by
               simpa only [if_neg hxv] using
                 ih x hFreeBody hzBody⟩
      · by_cases hxq : x = q
        · subst x
          simp [alphaRenameBoundAux, hqv, isFreeForN]
        · have hFreshQ : q ∉ termFV t := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.1
          have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.2
          simp only [alphaRenameBoundAux, if_neg hqv, isFreeForN]
          exact Or.inr
            ⟨hFreshQ, ih x hFreeBody hzBody⟩

private theorem alphaRenameBoundAux_false_isFreeForN_of_ne
    {L : Language} (A : FormulaN L) (t : Term L) (x v z : Nat)
    (hxv : x ≠ v)
    (hFree : isFreeForN t x A)
    (hzt : z ∉ termFV t)
    (hzBV : z ∉ formulaBVN A) :
    isFreeForN t x (alphaRenameBoundAux v z false A) := by
  induction A with
  | predN P ts =>
      trivial
  | eq_ hL t₁ t₂ =>
      trivial
  | neg A ih =>
      exact ih hFree hzBV
  | conj A B ihA ihB =>
      exact
        ⟨ihA hFree.1 (fun h => hzBV (Or.inl h)),
         ihB hFree.2 (fun h => hzBV (Or.inr h))⟩
  | disj A B ihA ihB =>
      exact
        ⟨ihA hFree.1 (fun h => hzBV (Or.inl h)),
         ihB hFree.2 (fun h => hzBV (Or.inr h))⟩
  | impl A B ihA ihB =>
      exact
        ⟨ihA hFree.1 (fun h => hzBV (Or.inl h)),
         ihB hFree.2 (fun h => hzBV (Or.inr h))⟩
  | all q A ih =>
      have hzBody : z ∉ formulaBVN A :=
        fun h => hzBV (Or.inl h)
      by_cases hqv : q = v
      · subst q
        have hFreeBody : isFreeForN t x A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxv
          · exact h.2
        simp only [alphaRenameBoundAux, if_pos rfl, isFreeForN]
        exact Or.inr
          ⟨hzt,
           by
             simpa only [if_neg hxv] using
               alphaRenameBoundAux_true_isFreeForN
                 A t x v z hFreeBody hzt hzBody⟩
      · by_cases hxq : x = q
        · subst x
          simp [alphaRenameBoundAux, hqv, isFreeForN]
        · have hFreshQ : q ∉ termFV t := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.1
          have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.2
          simp only [alphaRenameBoundAux, if_neg hqv, isFreeForN]
          exact Or.inr
            ⟨hFreshQ, ih hFreeBody hzBody⟩
  | ex q A ih =>
      have hzBody : z ∉ formulaBVN A :=
        fun h => hzBV (Or.inl h)
      by_cases hqv : q = v
      · subst q
        have hFreeBody : isFreeForN t x A := by
          simp only [isFreeForN] at hFree
          rcases hFree with h | h
          · exact absurd h hxv
          · exact h.2
        simp only [alphaRenameBoundAux, if_pos rfl, isFreeForN]
        exact Or.inr
          ⟨hzt,
           by
             simpa only [if_neg hxv] using
               alphaRenameBoundAux_true_isFreeForN
                 A t x v z hFreeBody hzt hzBody⟩
      · by_cases hxq : x = q
        · subst x
          simp [alphaRenameBoundAux, hqv, isFreeForN]
        · have hFreshQ : q ∉ termFV t := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.1
          have hFreeBody : isFreeForN t x A := by
            simp only [isFreeForN] at hFree
            rcases hFree with h | h
            · exact absurd h hxq
            · exact h.2
          simp only [alphaRenameBoundAux, if_neg hqv, isFreeForN]
          exact Or.inr
            ⟨hFreshQ, ih hFreeBody hzBody⟩

private theorem alphaRenameBinderBody_isFreeForN {L : Language}
    (A : FormulaN L) (t : Term L) (x v z : Nat)
    (hFree : isFreeForN t x A)
    (hzA : z ∉ formulaVariableSupport A)
    (hzt : z ∉ termFV t) (_hzx : z ≠ x) :
    isFreeForN t (alphaRenameBinderIndex x v z)
      (alphaRenameBinderBody A x v z) := by
  have hzBV : z ∉ formulaBVN A :=
    fun h => hzA (formulaBVN_mem_formulaVariableSupport A z h)
  by_cases hxv : x = v
  · subst v
    simpa [alphaRenameBinderBody, alphaRenameBinderIndex] using
      alphaRenameBoundAux_true_isFreeForN
        A t x x z hFree hzt hzBV
  · simp only [alphaRenameBinderBody, if_neg hxv,
      alphaRenameBinderIndex, if_neg hxv]
    exact alphaRenameBoundAux_false_isFreeForN_of_ne
      A t x v z hxv hFree hzt hzBV

-- ===================================================================
-- Private substitution preparation: rule-level bound renaming
-- ===================================================================

private noncomputable def alphaRenameBoundRule {L : Language}
    (v z : Nat) : G1nnfRule L → G1nnfRule L
  | .axiomPosAtomic A hAtom Γ Δ =>
      .axiomPosAtomic (alphaRenameBound A v z)
        (alphaRenameBound_isAtomic A v z hAtom)
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z)
  | .axiomNegAtomic A hAtom Γ Δ =>
      .axiomNegAtomic (alphaRenameBound A v z)
        (alphaRenameBound_isAtomic A v z hAtom)
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z)
  | .axiomCompLeft A hAtom Γ Δ =>
      .axiomCompLeft (alphaRenameBound A v z)
        (alphaRenameBound_isAtomic A v z hAtom)
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z)
  | .axiomCompRight A hAtom Γ Δ =>
      .axiomCompRight (alphaRenameBound A v z)
        (alphaRenameBound_isAtomic A v z hAtom)
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z)
  | .cut A Lam Theta =>
      .cut (alphaRenameBound A v z)
        (alphaRenameFormulaFinset Lam v z)
        (alphaRenameFormulaFinset Theta v z)
  | .conjLeft1 A B =>
      .conjLeft1 (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .conjLeft2 A B =>
      .conjLeft2 (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .conjRight A B =>
      .conjRight (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .disjLeft A B =>
      .disjLeft (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .disjRight1 A B =>
      .disjRight1 (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .disjRight2 A B =>
      .disjRight2 (alphaRenameBound A v z) (alphaRenameBound B v z)
  | .allLeft x A t =>
      .allLeft (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) t
  | .allRight x A ev =>
      .allRight (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) ev
  | .exLeft x A ev =>
      .exLeft (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) ev
  | .exRight x A t =>
      .exRight (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) t

theorem alphaRenameBoundRule_conclusion_eq {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z : Nat) :
    (alphaRenameBoundRule v z rule).conclusion
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z) =
      (alphaRenameFormulaFinset (rule.conclusion Γ Δ).1 v z,
       alphaRenameFormulaFinset (rule.conclusion Γ Δ).2 v z) := by
  cases rule <;>
    simp [alphaRenameBoundRule, G1nnfRule.conclusion,
      alphaRenameFormulaFinset_insert, alphaRenameFormulaFinset_union,
      alphaRenameBound_all, alphaRenameBound_ex,
      alphaRenameBound, alphaRenameBoundAux,
      alphaRenameBinderIndex, alphaRenameBinderBody] <;>
    split <;> rfl

private theorem alphaRenameBoundRule_premises_length {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z : Nat) :
    ((alphaRenameBoundRule v z rule).premises
      (alphaRenameFormulaFinset Γ v z)
      (alphaRenameFormulaFinset Δ v z)).length =
        (rule.premises Γ Δ).length := by
  cases rule <;> rfl

theorem alphaRenameBoundRule_cutFormula {L : Language}
    (rule : G1nnfRule L) (v z : Nat) :
    (alphaRenameBoundRule v z rule).cutFormula =
      rule.cutFormula.map (fun A => alphaRenameBound A v z) := by
  cases rule <;>
    simp [alphaRenameBoundRule, G1nnfRule.cutFormula, Option.map]

private theorem alphaRenameBoundRule_sideConditions {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z : Nat)
    (hSC : rule.SideConditions Γ Δ)
    (hz : z ∉ rule.variableSupport) :
    (alphaRenameBoundRule v z rule).SideConditions
      (alphaRenameFormulaFinset Γ v z)
      (alphaRenameFormulaFinset Δ v z) := by
  cases rule with
  | axiomPosAtomic _ _ _ _ => trivial
  | axiomNegAtomic _ _ _ _ => trivial
  | axiomCompLeft _ _ _ _ => trivial
  | axiomCompRight _ _ _ _ => trivial
  | cut _ _ _ => trivial
  | conjLeft1 _ _ => trivial
  | conjLeft2 _ _ => trivial
  | conjRight _ _ => trivial
  | disjLeft _ _ => trivial
  | disjRight1 _ _ => trivial
  | disjRight2 _ _ => trivial
  | allLeft x A t =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_allLeft_formula x A t z h)
      have hzt : z ∉ termFV t :=
        fun h => hz
          (G1nnfRule.variableSupport_allLeft_term x A t z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_allLeft_binder x A t)
      exact alphaRenameBinderBody_isFreeForN
        A t x v z hSC hzA hzt hzx
  | allRight x A ev =>
      rcases hSC with ⟨hFree, hPrincipal, hGamma, hDelta⟩
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_allRight_formula x ev A z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_allRight_binder x ev A)
      have hzev : z ≠ ev := by
        intro h
        subst z
        exact hz
          (G1nnfRule.variableSupport_allRight_eigenvariable x ev A)
      have hzTerm : z ∉ termFV (.var ev : Term L) := by
        intro h
        change z = ev at h
        exact hzev h
      refine
        ⟨alphaRenameBinderBody_isFreeForN
            A (.var ev) x v z hFree hzA hzTerm hzx,
         ?_, ?_, ?_⟩
      · have h :=
          alphaRenameBound_preserves_freeVariable_absence
            (.all x A) v z ev hPrincipal
        simpa only [alphaRenameBound_all] using h
      · exact alphaRenameFormulaFinset_preserves_freshness
          Γ v z ev hGamma
      · exact alphaRenameFormulaFinset_preserves_freshness
          Δ v z ev hDelta
  | exLeft x A ev =>
      rcases hSC with ⟨hFree, hPrincipal, hGamma, hDelta⟩
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_exLeft_formula x ev A z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_exLeft_binder x ev A)
      have hzev : z ≠ ev := by
        intro h
        subst z
        exact hz
          (G1nnfRule.variableSupport_exLeft_eigenvariable x ev A)
      have hzTerm : z ∉ termFV (.var ev : Term L) := by
        intro h
        change z = ev at h
        exact hzev h
      refine
        ⟨alphaRenameBinderBody_isFreeForN
            A (.var ev) x v z hFree hzA hzTerm hzx,
         ?_, ?_, ?_⟩
      · have h :=
          alphaRenameBound_preserves_freeVariable_absence
            (.ex x A) v z ev hPrincipal
        simpa only [alphaRenameBound_ex] using h
      · exact alphaRenameFormulaFinset_preserves_freshness
          Γ v z ev hGamma
      · exact alphaRenameFormulaFinset_preserves_freshness
          Δ v z ev hDelta
  | exRight x A t =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_exRight_formula x A t z h)
      have hzt : z ∉ termFV t :=
        fun h => hz
          (G1nnfRule.variableSupport_exRight_term x A t z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_exRight_binder x A t)
      exact alphaRenameBinderBody_isFreeForN
        A t x v z hSC hzA hzt hzx

private theorem alphaRenameBoundRule_applicationConditions {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z : Nat)
    (hAC : rule.ApplicationConditions Γ Δ)
    (hz : z ∉ rule.variableSupport) :
    (alphaRenameBoundRule v z rule).ApplicationConditions
      (alphaRenameFormulaFinset Γ v z)
      (alphaRenameFormulaFinset Δ v z) := by
  refine
    ⟨alphaRenameBoundRule_sideConditions
        rule Γ Δ v z hAC.1 hz, ?_⟩
  rw [alphaRenameBoundRule_conclusion_eq]
  exact
    ⟨alphaRenameFormulaFinset_isNNF
        (rule.conclusion Γ Δ).1 v z hAC.2.1,
     alphaRenameFormulaFinset_isNNF
        (rule.conclusion Γ Δ).2 v z hAC.2.2⟩

private theorem alphaRenameBoundRule_premises_eq {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z : Nat)
    (hSC : rule.SideConditions Γ Δ)
    (hz : z ∉ rule.variableSupport) :
    (alphaRenameBoundRule v z rule).premises
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z) =
      (rule.premises Γ Δ).map (fun p =>
        (alphaRenameFormulaFinset p.1 v z,
         alphaRenameFormulaFinset p.2 v z)) := by
  cases rule with
  | axiomPosAtomic _ _ _ _ => rfl
  | axiomNegAtomic _ _ _ _ => rfl
  | axiomCompLeft _ _ _ _ => rfl
  | axiomCompRight _ _ _ _ => rfl
  | cut A Lam Theta =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert]
  | conjLeft1 A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | conjLeft2 A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | conjRight A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | disjLeft A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | disjRight1 A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | disjRight2 A B =>
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, alphaRenameBound,
        alphaRenameBoundAux]
  | allLeft x A t =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_allLeft_formula x A t z h)
      have hzt : z ∉ termFV t :=
        fun h => hz
          (G1nnfRule.variableSupport_allLeft_term x A t z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_allLeft_binder x A t)
      have hComm :=
        alphaRenameBinderBody_formulaSubstN
          A t x v z hSC hzA hzt hzx
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, hComm]
  | allRight x A ev =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_allRight_formula x ev A z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_allRight_binder x ev A)
      have hzev : z ≠ ev := by
        intro h
        subst z
        exact hz
          (G1nnfRule.variableSupport_allRight_eigenvariable x ev A)
      have hzTerm : z ∉ termFV (.var ev : Term L) := by
        intro h
        change z = ev at h
        exact hzev h
      have hComm :=
        alphaRenameBinderBody_formulaSubstN
          A (.var ev) x v z hSC.1 hzA hzTerm hzx
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, hComm]
  | exLeft x A ev =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_exLeft_formula x ev A z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_exLeft_binder x ev A)
      have hzev : z ≠ ev := by
        intro h
        subst z
        exact hz
          (G1nnfRule.variableSupport_exLeft_eigenvariable x ev A)
      have hzTerm : z ∉ termFV (.var ev : Term L) := by
        intro h
        change z = ev at h
        exact hzev h
      have hComm :=
        alphaRenameBinderBody_formulaSubstN
          A (.var ev) x v z hSC.1 hzA hzTerm hzx
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, hComm]
  | exRight x A t =>
      have hzA : z ∉ formulaVariableSupport A :=
        fun h => hz
          (G1nnfRule.variableSupport_exRight_formula x A t z h)
      have hzt : z ∉ termFV t :=
        fun h => hz
          (G1nnfRule.variableSupport_exRight_term x A t z h)
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hz (G1nnfRule.variableSupport_exRight_binder x A t)
      have hComm :=
        alphaRenameBinderBody_formulaSubstN
          A t x v z hSC hzA hzt hzx
      simp [alphaRenameBoundRule, G1nnfRule.premises,
        alphaRenameFormulaFinset_insert, hComm]

private theorem alphaRenameBoundRule_premises_nth_eq {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (v z n : Nat)
    (hn : n < (rule.premises Γ Δ).length)
    (hSC : rule.SideConditions Γ Δ)
    (hz : z ∉ rule.variableSupport) :
    ((alphaRenameBoundRule v z rule).premises
        (alphaRenameFormulaFinset Γ v z)
        (alphaRenameFormulaFinset Δ v z))[n]'
          (by rw [alphaRenameBoundRule_premises_length]; exact hn) =
      (alphaRenameFormulaFinset
          ((rule.premises Γ Δ)[n]'hn).1 v z,
       alphaRenameFormulaFinset
          ((rule.premises Γ Δ)[n]'hn).2 v z) := by
  have hEq :=
    alphaRenameBoundRule_premises_eq
      rule Γ Δ v z hSC hz
  have hGet :
      ((alphaRenameBoundRule v z rule).premises
          (alphaRenameFormulaFinset Γ v z)
          (alphaRenameFormulaFinset Δ v z))[n]'
            (by rw [alphaRenameBoundRule_premises_length]; exact hn) =
        ((rule.premises Γ Δ).map (fun p =>
          (alphaRenameFormulaFinset p.1 v z,
           alphaRenameFormulaFinset p.2 v z)))[n]'
            (by simpa using hn) := by
    simp [hEq]
  rw [hGet, List.getElem_map]

theorem alphaRenameBoundRule_eigenvariable_eq {L : Language}
    (rule : G1nnfRule L) (v z w : Nat) :
    (match alphaRenameBoundRule v z rule with
     | .allRight _ _ ev => w = ev
     | .exLeft _ _ ev => w = ev
     | _ => False) =
    (match rule with
     | .allRight _ _ ev => w = ev
     | .exLeft _ _ ev => w = ev
     | _ => False) := by
  cases rule <;> rfl

end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

/-- Rename one unsafe binder label throughout a proof tree.  The selected
fresh label is outside the complete tree support, so every rule transport
and every recursive premise transport is capture-free.  Eigenlabels are
deliberately unchanged in this first hygiene phase. -/
noncomputable def alphaRenameBoundTree {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) → (v z : Nat) → v ≠ z →
    z ∉ T.variableSupport →
    G1nnfProofTree hL
      (alphaRenameFormulaFinset Γ v z)
      (alphaRenameFormulaFinset Δ v z)
  | _, _, .axiom_ rule Γ Δ hAxiom hAC, v, z, hvz, hz =>
      have hzRule : z ∉ rule.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_axiom_of_rule (hL := hL)
            rule Γ Δ hAxiom hAC z h)
      have hEq1 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).1 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).1 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hEq2 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).2 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).2 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hPremLen :
          ((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).length = 0 := by
        rw [alphaRenameBoundRule_premises_length]
        exact hAxiom
      have hAC' :
          (alphaRenameBoundRule v z rule).ApplicationConditions
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z) :=
        alphaRenameBoundRule_applicationConditions
          rule Γ Δ v z hAC hzRule
      have core :=
        G1nnfProofTree.axiom_ (hL := hL)
          (alphaRenameBoundRule v z rule)
          (alphaRenameFormulaFinset Γ v z)
          (alphaRenameFormulaFinset Δ v z)
          hPremLen hAC'
      hEq1 ▸ hEq2 ▸ core
  | _, _, .onePremise rule Γ Δ hPrem hAC sub,
      v, z, hvz, hz =>
      have hzRule : z ∉ rule.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_onePremise_of_rule
            rule Γ Δ hPrem hAC sub z h)
      have hzSub : z ∉ sub.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_onePremise_of_subtree
            rule Γ Δ hPrem hAC sub z h)
      let subNew :=
        alphaRenameBoundTree sub v z hvz hzSub
      have hEq1 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).1 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).1 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hEq2 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).2 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).2 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hPremLen :
          ((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).length = 1 := by
        rw [alphaRenameBoundRule_premises_length]
        exact hPrem
      have hAC' :
          (alphaRenameBoundRule v z rule).ApplicationConditions
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z) :=
        alphaRenameBoundRule_applicationConditions
          rule Γ Δ v z hAC hzRule
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by
        rw [hPrem]
        omega
      have hPremEq :=
        alphaRenameBoundRule_premises_nth_eq
          rule Γ Δ v z 0 hPrem0 hAC.1 hzRule
      have h1 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).1 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[0]'hPrem0).1 v z := by
        rw [hPremEq]
      have h2 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).2 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[0]'hPrem0).2 v z := by
        rw [hPremEq]
      have subCast :
          G1nnfProofTree hL
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).1
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).2 :=
        h1 ▸ h2 ▸ subNew
      have core :=
        G1nnfProofTree.onePremise
          (alphaRenameBoundRule v z rule)
          (alphaRenameFormulaFinset Γ v z)
          (alphaRenameFormulaFinset Δ v z)
          hPremLen hAC' subCast
      hEq1 ▸ hEq2 ▸ core
  | _, _, .twoPremise rule Γ Δ hPrem hAC sub1 sub2,
      v, z, hvz, hz =>
      have hzRule : z ∉ rule.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_twoPremise_of_rule
            rule Γ Δ hPrem hAC sub1 sub2 z h)
      have hzSub1 : z ∉ sub1.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_twoPremise_of_left_subtree
            rule Γ Δ hPrem hAC sub1 sub2 z h)
      have hzSub2 : z ∉ sub2.variableSupport := by
        intro h
        exact hz
          (G1nnfProofTree.variableSupport_twoPremise_of_right_subtree
            rule Γ Δ hPrem hAC sub1 sub2 z h)
      let subNew1 :=
        alphaRenameBoundTree sub1 v z hvz hzSub1
      let subNew2 :=
        alphaRenameBoundTree sub2 v z hvz hzSub2
      have hEq1 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).1 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).1 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hEq2 :
          ((alphaRenameBoundRule v z rule).conclusion
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).2 =
          alphaRenameFormulaFinset
            (rule.conclusion Γ Δ).2 v z := by
        rw [alphaRenameBoundRule_conclusion_eq]
      have hPremLen :
          ((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z)).length = 2 := by
        rw [alphaRenameBoundRule_premises_length]
        exact hPrem
      have hAC' :
          (alphaRenameBoundRule v z rule).ApplicationConditions
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z) :=
        alphaRenameBoundRule_applicationConditions
          rule Γ Δ v z hAC hzRule
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by
        rw [hPrem]
        omega
      have hPrem1 : 1 < (rule.premises Γ Δ).length := by
        rw [hPrem]
        omega
      have hPremEq0 :=
        alphaRenameBoundRule_premises_nth_eq
          rule Γ Δ v z 0 hPrem0 hAC.1 hzRule
      have hPremEq1 :=
        alphaRenameBoundRule_premises_nth_eq
          rule Γ Δ v z 1 hPrem1 hAC.1 hzRule
      have h1_0 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).1 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[0]'hPrem0).1 v z := by
        rw [hPremEq0]
      have h2_0 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).2 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[0]'hPrem0).2 v z := by
        rw [hPremEq0]
      have h1_1 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[1]'(by omega)).1 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[1]'hPrem1).1 v z := by
        rw [hPremEq1]
      have h2_1 :
          (((alphaRenameBoundRule v z rule).premises
            (alphaRenameFormulaFinset Γ v z)
            (alphaRenameFormulaFinset Δ v z))[1]'(by omega)).2 =
          alphaRenameFormulaFinset
            ((rule.premises Γ Δ)[1]'hPrem1).2 v z := by
        rw [hPremEq1]
      have sub1Cast :
          G1nnfProofTree hL
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).1
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[0]'(by omega)).2 :=
        h1_0 ▸ h2_0 ▸ subNew1
      have sub2Cast :
          G1nnfProofTree hL
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[1]'(by omega)).1
            (((alphaRenameBoundRule v z rule).premises
              (alphaRenameFormulaFinset Γ v z)
              (alphaRenameFormulaFinset Δ v z))[1]'(by omega)).2 :=
        h1_1 ▸ h2_1 ▸ subNew2
      have core :=
        G1nnfProofTree.twoPremise
          (alphaRenameBoundRule v z rule)
          (alphaRenameFormulaFinset Γ v z)
          (alphaRenameFormulaFinset Δ v z)
          hPremLen hAC' sub1Cast sub2Cast
      hEq1 ▸ hEq2 ▸ core

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

