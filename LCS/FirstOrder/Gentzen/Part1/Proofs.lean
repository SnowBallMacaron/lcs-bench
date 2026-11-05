import LCS.FirstOrder.Gentzen.Part1

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Definition 5.4.1 (connective convention): Translate to the six-connective
syntax by expanding equivalence into two implications and replacing ⊥ with
B₀ ∧ ¬B₀; the supplied formula B₀ provides a contradiction in the target syntax. -/
def toFormulaN {L : Language} (B₀ : FormulaN L) : Syntax.Formula L → FormulaN L
  | .falsum => .conj B₀ (.neg B₀)
  | .pred0 P hP => .predN P (fun i => (hP ▸ i).elim0)
  | .predN P _ ts => .predN P ts
  | .eq_ h t u => .eq_ h t u
  | .conj A B => .conj (toFormulaN B₀ A) (toFormulaN B₀ B)
  | .disj A B => .disj (toFormulaN B₀ A) (toFormulaN B₀ B)
  | .impl A B => .impl (toFormulaN B₀ A) (toFormulaN B₀ B)
  | .equiv_ A B => .conj (.impl (toFormulaN B₀ A) (toFormulaN B₀ B))
      (.impl (toFormulaN B₀ B) (toFormulaN B₀ A))
  | .neg A => .neg (toFormulaN B₀ A)
  | .all x A => .all x (toFormulaN B₀ A)
  | .ex x A => .ex x (toFormulaN B₀ A)

helper /-- Definition 5.4.1 (no loss of generality): Over a language without equality,
the six-connective translation preserves truth in every structure and assignment. -/
theorem toFormulaN_equiv {L : Language} (hL : L.withoutEquality)
    (B₀ : FormulaN L) (M : Structure L) (A : Syntax.Formula L) (s : Assignment M) :
    Semantics.formulaEval M A s ↔ formulaEvalN M (toFormulaN B₀ A) s := by
  induction A generalizing s with
  | falsum => simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.andM, Basic.negM]
  | pred0 P hP =>
    apply Iff.of_eq
    apply congrArg (M.interpPred P)
    funext i
    exact (hP ▸ i).elim0
  | predN P hP ts => rfl
  | eq_ h t u => rfl
  | conj A B ihA ihB =>
    simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.andM, ihA, ihB]
  | disj A B ihA ihB =>
    simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.orM, ihA, ihB]
  | impl A B ihA ihB =>
    simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.implM, ihA, ihB]
  | equiv_ A B ihA ihB =>
    simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.equivM, Basic.andM, Basic.implM,
      ihA, ihB, iff_iff_implies_and_implies]
  | neg A ih => simp [Semantics.formulaEval, toFormulaN, formulaEvalN, Basic.negM, ih]
  | all x A ih => simp [Semantics.formulaEval, toFormulaN, formulaEvalN, ih]
  | ex x A ih => simp [Semantics.formulaEval, toFormulaN, formulaEvalN, ih]

proof_of exists_equiv_formulaN := by
  let B₀ : FormulaN L := .predN P (fun _ => .var 0)
  exact ⟨toFormulaN B₀ A, fun M s => toFormulaN_equiv hL B₀ M A s⟩


end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

namespace GProofTree



end GProofTree

end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

namespace GDeductionTree



end GDeductionTree

end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

proof_of termSubstNamingConst := by
  -- BEGIN PROOF
    induction r with
    | var y =>
      simp [termSubst]
      split
      · simp [termEval, namingConst, extendedInterp]
      · rfl
    | const c =>
      simp [termSubst]
    | func f ts ih =>
      simp [termSubst, termEval]
      congr 1; funext j; exact ih j


helper /-- Lemma 5.4.1: If t is free for x in A, then (A[t/x])_M[s] =
(A[a/x])_M[s] where a is the naming constant for t_M[s]. This bridges formula-level substitution with semantic evaluation via naming constants. Proved by induction on FormulaN (8 cases). -/
theorem formulaSubstNamingConst {L : Language}
    (M : Structure L) (s : Assignment (extendedInterp M))
    (A : FormulaN (extendedLanguage L M.carrier))
    (t : Term (extendedLanguage L M.carrier)) (x : Nat)
    (hfree : isFreeForN t x A) :
    formulaEvalN (extendedInterp M) (formulaSubstN A t x) s ↔
    formulaEvalN (extendedInterp M)
      (formulaSubstN A (namingConst (termEval (extendedInterp M) s t)) x) s :=
-- BEGIN PROOF
by
  induction A generalizing s with
  | predN P ts =>
    simp only [formulaSubstN, formulaEvalN]
    constructor <;> intro h
    · have : ∀ j, termEval (extendedInterp M) s (termSubst (ts j) t x) =
             termEval (extendedInterp M) s
               (termSubst (ts j) (namingConst (termEval (extendedInterp M) s t)) x) :=
        fun j => termSubstNamingConst M s t (ts j) x
      simp only [this] at h; exact h
    · have : ∀ j, termEval (extendedInterp M) s (termSubst (ts j) t x) =
             termEval (extendedInterp M) s
               (termSubst (ts j) (namingConst (termEval (extendedInterp M) s t)) x) :=
        fun j => termSubstNamingConst M s t (ts j) x
      simp only [this]; exact h
  | eq_ _ t1 t2 =>
    simp [formulaSubstN, formulaEvalN]
    rw [termSubstNamingConst M s t t1 x, termSubstNamingConst M s t t2 x]
  | neg A ih =>
    simp only [formulaSubstN, formulaEvalN, Basic.negM]
    exact not_congr (ih s hfree)
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.andM]
    have ⟨hfA, hfB⟩ : isFreeForN t x A ∧ isFreeForN t x B := hfree
    exact and_congr (ihA s hfA) (ihB s hfB)
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.orM]
    have ⟨hfA, hfB⟩ : isFreeForN t x A ∧ isFreeForN t x B := hfree
    exact or_congr (ihA s hfA) (ihB s hfB)
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.implM]
    have ⟨hfA, hfB⟩ : isFreeForN t x A ∧ isFreeForN t x B := hfree
    exact imp_congr (ihA s hfA) (ihB s hfB)
  | all j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj; simp [formulaEvalN]
    · simp [hxj]
      have ⟨hjt, hfree'⟩ : ¬ termFV t j ∧ isFreeForN t x A := by
        have h : x = j ∨ (¬ termFV t j ∧ isFreeForN t x A) := hfree
        cases h with
        | inl heq => exact absurd heq hxj
        | inr hfr => exact hfr
      have hteval : ∀ a, termEval (extendedInterp M) (assignUpdate s j a) t =
                         termEval (extendedInterp M) s t := by
        intro a
        exact termCoincidence (extendedInterp M) t (assignUpdate s j a) s
          (fun y hy => by simp [assignUpdate]; intro heq; exact absurd (heq ▸ hy) hjt)
      have ihA : ∀ a, formulaEvalN (extendedInterp M) (formulaSubstN A t x) (assignUpdate s j a) ↔
                       formulaEvalN (extendedInterp M)
                         (formulaSubstN A (namingConst (termEval (extendedInterp M) s t)) x)
                         (assignUpdate s j a) := by
        intro a
        have h := ih (assignUpdate s j a) hfree'
        rw [hteval a] at h
        exact h
      constructor <;> intro h a
      · exact (ihA a).mp (h a)
      · exact (ihA a).mpr (h a)
  | ex j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj; simp [formulaEvalN]
    · simp [hxj, formulaEvalN]
      have ⟨hjt, hfree'⟩ : ¬ termFV t j ∧ isFreeForN t x A := by
        have h : x = j ∨ (¬ termFV t j ∧ isFreeForN t x A) := hfree
        cases h with
        | inl heq => exact absurd heq hxj
        | inr hfr => exact hfr
      have hteval : ∀ a, termEval (extendedInterp M) (assignUpdate s j a) t =
                         termEval (extendedInterp M) s t := by
        intro a
        exact termCoincidence (extendedInterp M) t (assignUpdate s j a) s
          (fun y hy => by simp [assignUpdate]; intro heq; exact absurd (heq ▸ hy) hjt)
      have ihA : ∀ a, formulaEvalN (extendedInterp M) (formulaSubstN A t x) (assignUpdate s j a) ↔
                       formulaEvalN (extendedInterp M)
                         (formulaSubstN A (namingConst (termEval (extendedInterp M) s t)) x)
                         (assignUpdate s j a) := by
        intro a
        have h := ih (assignUpdate s j a) hfree'
        rw [hteval a] at h
        exact h
      constructor <;> intro ⟨a, ha⟩
      · exact ⟨a, (ihA a).mp ha⟩
      · exact ⟨a, (ihA a).mpr ha⟩

proof_of formulaSubstNamingConstNoEq := formulaSubstNamingConst M s A t x hfree
































helper theorem memsnoc_left {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X] := List.mem_append_left _ h

helper theorem memsnoc_right {α : Type} {Γ : List α} {X : α} :
    X ∈ Γ ++ [X] := List.mem_append_right _ (List.Mem.head _)

proof_of ruleFalsificationIff1 := by
  -- BEGIN PROOF
    cases rule with
    | conjLeft Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, fun F hF => by
          rcases mem2_cases hF with h1 | h2 | h3 | h4
          · exact hant F (mem1_left h1)
          · rw [h2]; exact (hant _ mem1_center).1
          · rw [h3]; exact (hant _ mem1_center).2
          · exact hant F (mem1_right h4), hsucc⟩
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem2_left h1)
          · exact ⟨hant A mem2_first, hant B mem2_second⟩
          · exact hant F (mem2_right h3), hsucc⟩
    | disjRight Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAB := hsucc _ mem1_center
        have hA : ¬ formulaEvalN M A s := fun h => hAB (Or.inl h)
        have hB : ¬ formulaEvalN M B s := fun h => hAB (Or.inr h)
        exact ⟨s, hant, fun F hF => by
          rcases mem2_cases hF with h1 | h2 | h3 | h4
          · exact hsucc F (mem1_left h1)
          · rw [h2]; exact hA
          · rw [h3]; exact hB
          · exact hsucc F (mem1_right h4)⟩
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem2_left h1)
          · intro hAB; rcases hAB with hA | hB
            · exact hsucc A mem2_first hA
            · exact hsucc B mem2_second hB
          · exact hsucc F (mem2_right h3)⟩
    | implRight Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAB := hsucc _ mem1_center
        have hA : formulaEvalN M A s :=
          Classical.byContradiction (fun hNA => hAB (fun h => absurd h hNA))
        have hB : ¬ formulaEvalN M B s := fun hB => hAB (fun _ => hB)
        exact ⟨s, fun F hF => by
          rcases memcons_cases hF with rfl | hF'
          · exact hA
          · exact hant F hF',
          fun F hF => by
          rcases memcons_cases hF with rfl | hCtx
          · exact hB
          · rcases memcat_cases hCtx with hΔ | hΛ
            · exact hsucc F (mem1_left hΔ)
            · exact hsucc F (mem1_right hΛ)⟩
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, fun F hF => hant F (memcons_tail hF), fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (memcons_tail (memcat_left h1))
          · simp only [formulaEvalN]
            intro hAB
            exact absurd (hAB (hant A memcons_head)) (hsucc B memcons_head)
          · exact hsucc F (memcons_tail (memcat_right h3))⟩
    | negLeft Γ Δ Λ A =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hNA := hant _ mem1_center
        exact ⟨s, fun F hF => by
          rcases memcat_cases hF with hΓ | hΔ
          · exact hant F (mem1_left hΓ)
          · exact hant F (mem1_right hΔ),
          fun F hF => by
          rcases memcons_cases hF with rfl | hΛ
          · exact hNA
          · exact hsucc F hΛ⟩
      · intro ⟨s, hant, hsucc⟩
        have hA := hsucc A memcons_head
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (memcat_left h1)
          · exact hA
          · exact hant F (memcat_right h3), fun F hF => hsucc F (memcons_tail hF)⟩
    | negRight Γ Δ Λ A =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hNA := hsucc _ mem1_center
        have hA : formulaEvalN M A s :=
          Classical.byContradiction (fun h => hNA h)
        exact ⟨s, fun F hF => by
          rcases memcons_cases hF with rfl | hF'
          · exact hA
          · exact hant F hF',
          fun F hF => by
          rcases memcat_cases hF with hΔ | hΛ
          · exact hsucc F (mem1_left hΔ)
          · exact hsucc F (mem1_right hΛ)⟩
      · intro ⟨s, hant, hsucc⟩
        have hA := hant A memcons_head
        exact ⟨s, fun F hF => hant F (memcons_tail hF),
          fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (memcat_left h1)
          · intro hNA; exact absurd hA hNA
          · exact hsucc F (memcat_right h3)⟩
    | allLeft t Γ Δ Λ x A hfree =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAll := hant _ mem1_center
        exact ⟨s, fun F hF => by
          rcases mem2_cases hF with h1 | h2 | h3 | h4
          · exact hant F (mem1_left h1)
          · rw [h2]
            exact (formulaSubstEvalDirectN s A _ x hfree).mpr (hAll (termEval M s _))
          · rw [h3]; exact hAll
          · exact hant F (mem1_right h4), hsucc⟩
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem2_left h1)
          · exact hant _ mem2_second
          · exact hant F (mem2_right h3), hsucc⟩
    | allRight y Γ Δ Λ x A hfresh hfreeFor =>
      have hfreeY : isFreeForN (Term.var y) x A := hfreeFor
      have yA : ∀ z ∈ formulaFVN A, z ≠ x → z ≠ y := by
        intro z hz hzx hzy; subst hzy
        exact hfresh (FormulaN.all x A) (List.mem_append_right _ mem1_center) ⟨hz, hzx⟩
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAll := hsucc _ mem1_center
        have ⟨a, ha⟩ : ∃ a, ¬ formulaEvalN M A (assignUpdate s x a) :=
          Classical.byContradiction (fun h =>
            hAll (fun a => Classical.byContradiction (fun hna => h ⟨a, hna⟩)))
        let s' : Assignment M := assignUpdate s y a
        have coin_fresh : ∀ (F : FormulaN L), y ∉ formulaFVN F →
            ∀ z, z ∈ formulaFVN F → s z = (assignUpdate s y a) z := by
          intro F hyF z hz
          show s z = if z = y then a else s z
          split
          · rename_i hzy; exact absurd (hzy ▸ hz) hyF
          · rfl
        have coin_fresh_ant : ∀ F ∈ Γ, formulaEvalN M F s' := fun F hF =>
          (coincidenceLemmaN M F s s' (coin_fresh F
            (hfresh F (List.mem_append_left _ hF)))).mp (hant F hF)
        have coin_fresh_succ : ∀ F ∈ Δ ++ Λ, ¬ formulaEvalN M F s' := by
          intro F hF heval
          have hyF : y ∉ formulaFVN F := by
            rcases List.mem_append.mp hF with hD | hL
            · exact hfresh F (List.mem_append_right _ (mem1_left hD))
            · exact hfresh F (List.mem_append_right _ (mem1_right hL))
          have : formulaEvalN M F s := (coincidenceLemmaN M F s' s (fun z hz => by
            show assignUpdate s y a z = s z
            rw [coin_fresh F hyF z hz])).mp heval
          rcases List.mem_append.mp hF with hD | hL
          · exact hsucc F (mem1_left hD) this
          · exact hsucc F (mem1_right hL) this
        have coinA' : formulaEvalN M A (assignUpdate (assignUpdate s y a) x a) ↔
            formulaEvalN M A (assignUpdate s x a) :=
          coincidenceLemmaN M A _ _ (fun z hz => by
            simp only [assignUpdate]
            split
            · rfl
            · rename_i hzx; split
              · rename_i hzy; exact absurd hzy (yA z hz hzx)
              · rfl)
        have hAsub : ¬ formulaEvalN M (formulaSubstN A (Term.var y) x) s' := by
          intro heval
          rw [formulaSubstEvalDirectN s' A (Term.var y) x hfreeY] at heval
          have : termEval M s' (Term.var y) = a := by
            show assignUpdate s y a y = a
            simp only [assignUpdate, ite_true]
          rw [this] at heval
          exact ha (coinA'.mp heval)
        exact ⟨s', coin_fresh_ant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact coin_fresh_succ F (List.mem_append_left _ h1)
          · exact hAsub
          · exact coin_fresh_succ F (List.mem_append_right _ h3)⟩
      · intro ⟨s, hant, hsucc⟩
        have hAsub := hsucc _ mem1_center
        have hNotA : ¬ formulaEvalN M A (assignUpdate s x (s y)) := by
          intro heval
          apply hAsub
          rw [formulaSubstEvalDirectN s A (Term.var y) x hfreeY]
          simp [termEval]; exact heval
        exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem1_left h1)
          · intro hall; exact hNotA (hall (s y))
          · exact hsucc F (mem1_right h3)⟩
    | exLeft y Γ Δ Λ x A hfresh hfreeFor =>
      have hfreeY : isFreeForN (Term.var y) x A := hfreeFor
      have yA : ∀ z ∈ formulaFVN A, z ≠ x → z ≠ y := by
        intro z hz hzx hzy; subst hzy
        exact hfresh (FormulaN.ex x A) (List.mem_append_left _ mem1_center) ⟨hz, hzx⟩
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hExA := hant _ mem1_center
        obtain ⟨a, ha⟩ := hExA
        let s' : Assignment M := assignUpdate s y a
        have coin_fresh : ∀ (F : FormulaN L), y ∉ formulaFVN F →
            ∀ z, z ∈ formulaFVN F → s z = (assignUpdate s y a) z := by
          intro F hyF z hz
          show s z = if z = y then a else s z
          split
          · rename_i hzy; exact absurd (hzy ▸ hz) hyF
          · rfl
        have coin_fresh_ant : ∀ F ∈ Γ ++ Δ, formulaEvalN M F s' := by
          intro F hF
          have hyF : y ∉ formulaFVN F := by
            rcases List.mem_append.mp hF with hΓ | hΔ
            · exact hfresh F (List.mem_append_left _ (mem1_left hΓ))
            · exact hfresh F (List.mem_append_left _ (mem1_right hΔ))
          exact (coincidenceLemmaN M F s s' (coin_fresh F hyF)).mp (by
            rcases List.mem_append.mp hF with hΓ | hΔ
            · exact hant F (mem1_left hΓ)
            · exact hant F (mem1_right hΔ))
        have coin_fresh_succ : ∀ F ∈ Λ, ¬ formulaEvalN M F s' := by
          intro F hF heval
          have hyF : y ∉ formulaFVN F := hfresh F (List.mem_append_right _ hF)
          have : formulaEvalN M F s := (coincidenceLemmaN M F s' s (fun z hz => by
            rw [coin_fresh F hyF z hz])).mp heval
          exact hsucc F hF this
        have coinA : formulaEvalN M A (assignUpdate (assignUpdate s y a) x a) ↔
            formulaEvalN M A (assignUpdate s x a) :=
          coincidenceLemmaN M A _ _ (fun z hz => by
            simp only [assignUpdate]
            split
            · rfl
            · rename_i hzx; split
              · rename_i hzy; exact absurd hzy (yA z hz hzx)
              · rfl)
        have hAsub : formulaEvalN M (formulaSubstN A (Term.var y) x) s' := by
          rw [formulaSubstEvalDirectN s' A (Term.var y) x hfreeY]
          have : termEval M s' (Term.var y) = a := by
            show assignUpdate s y a y = a
            simp only [assignUpdate, ite_true]
          rw [this]
          exact coinA.mpr ha
        exact ⟨s', fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact coin_fresh_ant F (List.mem_append_left _ h1)
          · exact hAsub
          · exact coin_fresh_ant F (List.mem_append_right _ h3), coin_fresh_succ⟩
      · intro ⟨s, hant, hsucc⟩
        have hAyx := hant _ mem1_center
        have hExA : formulaEvalN M (FormulaN.ex x A) s :=
          ⟨s y, (formulaSubstEvalDirectN s A (Term.var y) x hfreeY).mp hAyx⟩
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem1_left h1)
          · exact hExA
          · exact hant F (mem1_right h3), hsucc⟩
    | exRight t Γ Δ Λ x A hfree =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hExA := hsucc _ mem1_center
        have hNotSub : ¬ formulaEvalN M (formulaSubstN A t x) s := fun h =>
          hExA ⟨termEval M s t,
            (formulaSubstEvalDirectN s A t x hfree).mp h⟩
        exact ⟨s, hant, fun F hF => by
          rcases mem2_cases hF with h1 | h2 | h3 | h4
          · exact hsucc F (mem1_left h1)
          · rw [h2]; exact hNotSub
          · rw [h3]; exact hExA
          · exact hsucc F (mem1_right h4)⟩
      · intro ⟨s, hant, hsucc⟩
        exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem2_left h1)
          · exact hsucc _ mem2_second
          · exact hsucc F (mem2_right h3)⟩


proof_of ruleFalsificationIff2 := by
  -- BEGIN PROOF
    cases rule with
    | conjRight Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAB := hsucc _ mem1_center
        rcases Classical.em (formulaEvalN M A s) with hA | hA
        · right; exact ⟨s, hant, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hsucc F (mem1_left h1)
            · exact fun hB => hAB ⟨hA, hB⟩
            · exact hsucc F (mem1_right h3)⟩
        · left; exact ⟨s, hant, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hsucc F (mem1_left h1)
            · exact hA
            · exact hsucc F (mem1_right h3)⟩
      · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
        · have hA := hsucc _ mem1_center
          exact ⟨s, hant, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hsucc F (mem1_left h1)
            · intro ⟨ha, _⟩; exact hA ha
            · exact hsucc F (mem1_right h3)⟩
        · have hB := hsucc _ mem1_center
          exact ⟨s, hant, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hsucc F (mem1_left h1)
            · intro ⟨_, hb⟩; exact hB hb
            · exact hsucc F (mem1_right h3)⟩
    | disjLeft Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAB := hant _ mem1_center
        rcases hAB with hA | hB
        · left; exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (mem1_left h1)
            · exact hA
            · exact hant F (mem1_right h3), hsucc⟩
        · right; exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (mem1_left h1)
            · exact hB
            · exact hant F (mem1_right h3), hsucc⟩
      · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
        · exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (mem1_left h1)
            · exact Or.inl (hant A mem1_center)
            · exact hant F (mem1_right h3), hsucc⟩
        · exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (mem1_left h1)
            · exact Or.inr (hant B mem1_center)
            · exact hant F (mem1_right h3), hsucc⟩
    | implLeft Γ Δ Λ A B =>
      constructor
      · intro ⟨s, hant, hsucc⟩
        have hAB := hant _ mem1_center
        rcases Classical.em (formulaEvalN M A s) with hA | hA
        · have hB := hAB hA
          right; exact ⟨s, fun F hF => by
            rcases memcons_cases hF with rfl | hF'
            · exact hB
            · rcases memcat_cases hF' with hΓ | hΔ
              · exact hant F (mem1_left hΓ)
              · exact hant F (mem1_right hΔ), hsucc⟩
        · left; exact ⟨s, fun F hF => by
            rcases memcat_cases hF with hΓ | hΔ
            · exact hant F (mem1_left hΓ)
            · exact hant F (mem1_right hΔ),
            fun F hF => by
            rcases memcons_cases hF with rfl | hΛ
            · exact hA
            · exact hsucc F hΛ⟩
      · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
        · have hA := hsucc A memcons_head
          exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (memcat_left h1)
            · intro hA'; exact absurd hA' hA
            · exact hant F (memcat_right h3),
            fun F hF => hsucc F (memcons_tail hF)⟩
        · have hB := hant B memcons_head
          exact ⟨s, fun F hF => by
            rcases mem1_cases hF with h1 | rfl | h3
            · exact hant F (memcons_tail (memcat_left h1))
            · intro _; exact hB
            · exact hant F (memcons_tail (memcat_right h3)), hsucc⟩


end LCS.FirstOrder.Gentzen

end
