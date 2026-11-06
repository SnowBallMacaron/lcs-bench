import LCS.FirstOrder.Equality.HintikkaSets

section

namespace LCS.FirstOrder.Equality

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness

helper theorem chooseRep_spec {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    (q : QType hL H S hHS) :
    q = qmk (chooseRep q) := by
-- BEGIN PROOF
  exact Classical.choose_spec (@Quotient.inductionOn
    { t : Term L // t ∈ H } (eqSetoid hL H S hHS)
    (fun q' => ∃ (a : { t : Term L // t ∈ H }),
      q' = @Quotient.mk _ (eqSetoid hL H S hHS) a)
    q (fun a => ⟨a, rfl⟩))

helper theorem finQuotLift_mk {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    {β : Sort _} {n : Nat}
    (g : (Fin n → { t : Term L // t ∈ H }) → β)
    (hg : ∀ xs ys : Fin n → { t : Term L // t ∈ H },
      (∀ i, @Setoid.r _ (eqSetoid hL H S hHS) (xs i) (ys i)) → g xs = g ys)
    (ts : Fin n → { t : Term L // t ∈ H }) :
    finQuotLift g hg (fun i => qmk (ts i)) = g ts := by
-- BEGIN PROOF
  unfold finQuotLift
  apply hg
  intro i
  -- chooseRep (qmk (ts i)) is congruent to ts i
  have hspec := @chooseRep_spec L hL H S hHS (qmk (ts i))
  have heq := @Quotient.exact _ (eqSetoid hL H S hHS) _ _ hspec
  show eqCongruence hL S (@chooseRep L hL H S hHS (qmk (ts i))).val (ts i).val
  exact (eqCongruence_equiv hHS).symm heq

helper /-- A term in H evaluates to its class when its free variables are represented in H. -/
theorem quotTermEvalIdentity {L : Language} {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)} {hHS : IsHintikkaSetEq L hL H S}
    (t : Term L) (ht : t ∈ H) (hvars : ∀ x, x ∈ termFV t → Term.var x ∈ H) :
    termEval (quotientStructureEq hL H S hHS) (quotAssignment hL H S hHS) t =
      qmk ⟨t, ht⟩ := by
  induction t with
  | var x =>
    simp only [termEval, quotAssignment]
    exact dif_pos ht
  | const c =>
    have hc := (hHS.base.hTA.symbols (.const c) ht).2 c List.mem_cons_self
    simp only [termEval, quotientStructureEq]
    exact dif_pos hc
  | func f ts ih =>
    have hsyms := hHS.base.hTA.symbols (.func f ts) ht
    have hf : f ∈ signedSetFunSyms S := hsyms.1 f (Or.inl rfl)
    have hvars_i : ∀ i x, x ∈ termFV (ts i) → Term.var x ∈ H :=
      fun i x hx => hvars x ⟨i, hx⟩
    have hti : ∀ i, ts i ∈ H := fun i => termInHOver hHS.base.hTA (ts i)
      ⟨fun g hg => hsyms.1 g (Or.inr ⟨i, hg⟩),
       fun c hc => hsyms.2 c ((termConstSyms_func_iff f ts c).mpr ⟨i, hc⟩)⟩ (hvars_i i)
    have hevals : (fun i => termEval (quotientStructureEq hL H S hHS)
        (quotAssignment hL H S hHS) (ts i)) = (fun i => qmk ⟨ts i, hti i⟩) :=
      funext (fun i => ih i (hti i) (hvars_i i))
    simp only [termEval]
    rw [hevals]
    simp only [quotientStructureEq]
    rw [dif_pos hf, finQuotLift_mk]

helper /-- Terms occurring in a signed member of S use only symbols of L_S. -/
theorem signedOccurrence_symbols {L : Language} {S : Set (SignedFormula L)}
    (sf : SignedFormula L) (hsf : sf ∈ S) (t : Term L) (hocc : occursIn t sf) :
    termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S := by
  cases sf with
  | trueF A =>
    have h := termOccursInFormulaN_symbols A hocc
    exact ⟨fun f hf => ⟨.trueF A, hsf, h.1 f hf⟩,
      fun c hc => ⟨.trueF A, hsf, h.2 c hc⟩⟩
  | falseF A =>
    have h := termOccursInFormulaN_symbols A hocc
    exact ⟨fun f hf => ⟨.falseF A, hsf, h.1 f hf⟩,
      fun c hc => ⟨.falseF A, hsf, h.2 c hc⟩⟩

helper /-- Substitution of a free-for term evaluates using its quotient class.
H5 supplies its variables when the substitution is nonvacuous. -/
theorem quotSubstEval {L : Language} {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)} (hHS : IsHintikkaSetEq L hL H S)
    (A : FormulaN L) (t : Term L) (x : Nat) (ht : t ∈ H)
    (hfree : isFreeForN t x A)
    (hmem : SignedFormula.trueF (formulaSubstN A t x) ∈ S ∨
      SignedFormula.falseF (formulaSubstN A t x) ∈ S) :
    formulaEvalN (quotientStructureEq hL H S hHS) (formulaSubstN A t x)
        (quotAssignment hL H S hHS) ↔
      formulaEvalN (quotientStructureEq hL H S hHS) A
        (assignUpdate (quotAssignment hL H S hHS) x (qmk ⟨t, ht⟩)) := by
  classical
  refine (formulaSubstEvalDirectN (quotAssignment hL H S hHS) A t x hfree).trans ?_
  by_cases hx : x ∈ formulaFVN A
  · have hvars : ∀ v, v ∈ termFV t → Term.var v ∈ H := by
      intro v hv
      have hsub := formulaFVN_subst_contains A t x v hfree hx hv
      rcases hmem with h | h
      · exact hHS.base.h5 (.trueF (formulaSubstN A t x)) h v hsub
      · exact hHS.base.h5 (.falseF (formulaSubstN A t x)) h v hsub
    rw [quotTermEvalIdentity t ht hvars]
  · apply coincidenceLemmaN
    intro y hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    simp [assignUpdate, hyx]

proof_of hintikka_set_eq_satisfiable := by
  let M := quotientStructureEq hL H S hHS
  let s := quotAssignment hL H S hHS
  have predN_eval_iff (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L)
      (hmem : SignedFormula.trueF (.predN P ts) ∈ S ∨ SignedFormula.falseF (.predN P ts) ∈ S) :
      formulaEvalN M (.predN P ts) s ↔ SignedFormula.falseF (.predN P ts) ∉ S := by
    have hvars : ∀ i x, x ∈ termFV (ts i) → Term.var x ∈ H := by
      intro i x hx
      rcases hmem with h | h
      · exact hHS.base.h5 (.trueF (.predN P ts)) h x ⟨i, hx⟩
      · exact hHS.base.h5 (.falseF (.predN P ts)) h x ⟨i, hx⟩
    have htsH : ∀ i, ts i ∈ H := fun i => termInHOver hHS.base.hTA (ts i)
      (predicateArgument_symbols P ts hmem i) (hvars i)
    have hevals : (fun i => termEval M s (ts i)) = (fun i => qmk ⟨ts i, htsH i⟩) :=
      funext (fun i => quotTermEvalIdentity (ts i) (htsH i) (hvars i))
    simp only [formulaEvalN]
    rw [hevals]
    change (quotientStructureEq hL H S hHS).interpPred P _ ↔ _
    simp only [quotientStructureEq]
    rw [finQuotLift_mk]
  have predN_case : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      (SignedFormula.trueF (.predN P ts) ∈ S → formulaEvalN M (.predN P ts) s) ∧
      (SignedFormula.falseF (.predN P ts) ∈ S → ¬ formulaEvalN M (.predN P ts) s) := by
    intro P ts
    exact ⟨fun hT => (predN_eval_iff P ts (Or.inl hT)).mpr
        (fun hF => hHS.base.h0 (.predN P ts) rfl ⟨hT, hF⟩),
      fun hF heval => (predN_eval_iff P ts (Or.inr hF)).mp heval hF⟩
  have eq_eval_iff (t1 t2 : Term L)
      (hmem : SignedFormula.trueF (.eq_ hL t1 t2) ∈ S ∨ SignedFormula.falseF (.eq_ hL t1 t2) ∈ S) :
      formulaEvalN M (.eq_ hL t1 t2) s ↔ eqCongruence hL S t1 t2 := by
    have hvars : ∀ t, (t = t1 ∨ t = t2) → ∀ x, x ∈ termFV t → Term.var x ∈ H := by
      intro t ht x hx
      have hx' : x ∈ formulaFVN (.eq_ hL t1 t2) := by
        rcases ht with rfl | rfl
        · exact Or.inl hx
        · exact Or.inr hx
      rcases hmem with h | h
      · exact hHS.base.h5 (.trueF (.eq_ hL t1 t2)) h x hx'
      · exact hHS.base.h5 (.falseF (.eq_ hL t1 t2)) h x hx'
    have hterms : ∀ t, (t = t1 ∨ t = t2) → t ∈ H := by
      intro t ht
      apply termInHOver hHS.base.hTA t
      · have ho : termOccursInFormulaN t (.eq_ hL t1 t2) := by
          rcases ht with rfl | rfl
          · exact Or.inl (.self t)
          · exact Or.inr (.self t)
        rcases hmem with h | h
        · exact signedOccurrence_symbols (.trueF (.eq_ hL t1 t2)) h t ho
        · exact signedOccurrence_symbols (.falseF (.eq_ hL t1 t2)) h t ho
      · exact hvars t ht
    simp only [formulaEvalN]
    rw [quotTermEvalIdentity t1 (hterms t1 (Or.inl rfl)) (hvars t1 (Or.inl rfl)),
      quotTermEvalIdentity t2 (hterms t2 (Or.inr rfl)) (hvars t2 (Or.inr rfl))]
    exact ⟨Quotient.exact, fun h =>
      @Quotient.sound _ (eqSetoid hL H S hHS)
        ⟨t1, hterms t1 (Or.inl rfl)⟩ ⟨t2, hterms t2 (Or.inr rfl)⟩ h⟩
  have eq_case : ∀ (t1 t2 : Term L),
      (SignedFormula.trueF (.eq_ hL t1 t2) ∈ S → formulaEvalN M (.eq_ hL t1 t2) s) ∧
      (SignedFormula.falseF (.eq_ hL t1 t2) ∈ S → ¬ formulaEvalN M (.eq_ hL t1 t2) s) := by
    intro t1 t2
    exact ⟨fun hT => (eq_eval_iff t1 t2 (Or.inl hT)).mpr hT,
      fun hF heval => hHS.base.h0 (.eq_ hL t1 t2) rfl
        ⟨(eq_eval_iff t1 t2 (Or.inr hF)).mp heval, hF⟩⟩
  -- Main induction on formulaDepth (FormulaN version from Hintikka.lean).
  have key : ∀ A : FormulaN L,
      (SignedFormula.trueF A ∈ S → formulaEvalN M A s) ∧
      (SignedFormula.falseF A ∈ S → ¬ formulaEvalN M A s) := by
    suffices aux : ∀ (n : Nat) (A : FormulaN L), formulaDepth A ≤ n →
        (SignedFormula.trueF A ∈ S → formulaEvalN M A s) ∧
        (SignedFormula.falseF A ∈ S → ¬ formulaEvalN M A s) from
      fun A => aux (formulaDepth A) A (Nat.le_refl _)
    intro n; induction n with
    | zero =>
      intro A hle
      match A with
      | .predN P ts => exact predN_case P ts
      | .eq_ _ t1 t2 => exact eq_case t1 t2
      | .conj _ _ => simp [formulaDepth] at hle
      | .disj _ _ => simp [formulaDepth] at hle
      | .impl _ _ => simp [formulaDepth] at hle
      | .neg _ => simp [formulaDepth] at hle
      | .all _ _ => simp [formulaDepth] at hle
      | .ex _ _ => simp [formulaDepth] at hle
    | succ n ih_n =>
      intro A hle
      match A with
      | .predN P ts => exact predN_case P ts
      | .eq_ _ t1 t2 => exact eq_case t1 t2
      | .conj A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => ⟨ihA.1 ((hHS.base.h1 (TypeA.tConj A' B') hT).1),
                            ihB.1 ((hHS.base.h1 (TypeA.tConj A' B') hT).2)⟩,
               fun hF ⟨ha, hb⟩ => (hHS.base.h2 (TypeB.fConj A' B') hF).elim
                 (fun hA => ihA.2 hA ha) (fun hB => ihB.2 hB hb)⟩
      | .disj A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => (hHS.base.h2 (TypeB.tDisj A' B') hT).elim
                 (fun hA => Or.inl (ihA.1 hA)) (fun hB => Or.inr (ihB.1 hB)),
               fun hF h => by
                 obtain ⟨hA, hB⟩ := hHS.base.h1 (TypeA.fDisj A' B') hF
                 cases h with
                 | inl ha => exact ihA.2 hA ha
                 | inr hb => exact ihB.2 hB hb⟩
      | .impl A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT ha => (hHS.base.h2 (TypeB.tImpl A' B') hT).elim
                 (fun hFA => absurd ha (ihA.2 hFA)) (fun hTB => ihB.1 hTB),
               fun hF h => ihB.2 ((hHS.base.h1 (TypeA.fImpl A' B') hF).2)
                 (h (ihA.1 ((hHS.base.h1 (TypeA.fImpl A' B') hF).1)))⟩
      | .neg A' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => ihA.2 (hHS.base.h1 (TypeA.tNeg A') hT).1,
               fun hF heval => heval (ihA.1 (hHS.base.h1 (TypeA.fNeg A') hF).1)⟩
      | .all x A' =>
        constructor
        · intro hT a
          revert a
          apply @Quotient.ind _ (eqSetoid hL H S hHS)
          intro ⟨t, ht⟩
          have hfree : isFreeForN t x A' := hHS.base.h6 x A' t ht (Or.inl hT)
          have hsubst_in_S := hHS.base.h3 (TypeC.tAll x A') hT t ht hfree
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have heval_subst := (ih_n (formulaSubstN A' t x) hdepth_sub).1 hsubst_in_S
          exact (quotSubstEval hHS A' t x ht hfree (Or.inl hsubst_in_S)).mp heval_subst
        · intro hF hall
          obtain ⟨t, ht, hfree, hsubst_in_S⟩ := hHS.base.h4 (TypeD.fAll x A') hF
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have hneval := (ih_n (formulaSubstN A' t x) hdepth_sub).2 hsubst_in_S
          apply hneval
          exact (quotSubstEval hHS A' t x ht hfree (Or.inr hsubst_in_S)).mpr (hall (qmk ⟨t, ht⟩))
      | .ex x A' =>
        constructor
        · intro hT
          obtain ⟨t, ht, hfree, hsubst_in_S⟩ := hHS.base.h4 (TypeD.tEx x A') hT
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have heval_subst := (ih_n (formulaSubstN A' t x) hdepth_sub).1 hsubst_in_S
          exact ⟨qmk ⟨t, ht⟩, (quotSubstEval hHS A' t x ht hfree (Or.inl hsubst_in_S)).mp heval_subst⟩
        · intro hF ⟨a, heval⟩
          revert heval
          refine @Quotient.inductionOn _ (eqSetoid hL H S hHS)
            (fun a' => formulaEvalN M A' (assignUpdate s x a') → False)
            a ?_
          intro ⟨t, ht⟩ heval
          have hfree : isFreeForN t x A' := hHS.base.h6 x A' t ht (Or.inr (Or.inr (Or.inr hF)))
          have hsubst_in_S := hHS.base.h3 (TypeC.fEx x A') hF t ht hfree
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have hneval := (ih_n (formulaSubstN A' t x) hdepth_sub).2 hsubst_in_S
          apply hneval
          exact (quotSubstEval hHS A' t x ht hfree (Or.inr hsubst_in_S)).mpr heval
  intro sf hsf; cases sf with
  | trueF A => exact (key A).1 hsf
  | falseF A => exact (key A).2 hsf

end LCS.FirstOrder.Equality

end
