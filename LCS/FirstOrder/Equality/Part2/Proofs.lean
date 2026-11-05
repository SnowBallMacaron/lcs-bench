import LCS.FirstOrder.Equality.Part2

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

helper /-- Lemma 5.6.1 (companion): If s_i ~ t_i for all i, then
TP(s1,...,sn) in S iff TP(t1,...,tn) in S, using H6(iii) and H2.
Ensures well-definedness of the predicate interpretation on
equivalence classes. -/
theorem eqCongruence_pred {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H)
    (hcong : ∀ i, eqCongruence hL S (ss i) (ts i)) :
    (SignedFormula.trueF (FormulaN.predN P ss) ∈ S ↔
     SignedFormula.trueF (FormulaN.predN P ts) ∈ S) :=
-- BEGIN PROOF
by
  have forward : ∀ (uu vv : Fin (L.predArity P) → Term L),
      (∀ i, eqCongruence hL S (uu i) (vv i)) →
      (∀ i, uu i ∈ H) → (∀ i, vv i ∈ H) →
      SignedFormula.trueF (FormulaN.predN P uu) ∈ S →
      SignedFormula.trueF (FormulaN.predN P vv) ∈ S := by
    intro uu vv hc huu hvv hPuu
    have hPS : P ∈ signedSetPredSyms S :=
      ⟨SignedFormula.trueF (FormulaN.predN P uu), hPuu, rfl⟩
    have h6iii := hHS.h6iii P hPS uu vv huu hvv
    have hb := hHS.base.h2 (TypeB.tImpl
      (conjoinFormulae (FormulaN.predN P uu)
        (eqPairsList hL uu vv ++ [FormulaN.predN P uu]))
      (FormulaN.predN P vv))
    simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
    cases hb h6iii with
    | inr h => exact h
    | inl hF =>
      exfalso
      have hne : (eqPairsList hL uu vv ++ [FormulaN.predN P uu]) ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
      exact falseConjoinContra hHS.base.h0 hHS.base.h2
        (FormulaN.predN P uu) (eqPairsList hL uu vv ++ [FormulaN.predN P uu])
        hne hF
        (fun F hF' => by
          simp [List.mem_append] at hF'
          rcases hF' with hpair | rfl
          · simp [eqPairsList, List.mem_map] at hpair
            obtain ⟨i, _, rfl⟩ := hpair
            exact hc i
          · exact hPuu)
        (fun F hF' => by
          simp [List.mem_append] at hF'
          rcases hF' with hpair | rfl
          · simp [eqPairsList, List.mem_map] at hpair
            obtain ⟨i, _, rfl⟩ := hpair
            exact rfl
          · exact rfl)
  constructor
  · exact forward ss ts hcong hss hts
  · have hcong_sym : ∀ i, eqCongruence hL S (ts i) (ss i) :=
      fun i => eqCongruence_symm hHS (ss i) (ts i)
        (hss i) (hts i) (hcong i)
    exact forward ts ss hcong_sym hts hss

helper /-- Lemma 5.6.1 (companion): For every term t in H, evaluating t
in the subtype structure under the identity assignment yields the
subtype element (t, ht). Proved by structural induction on terms:
variables map to themselves by the identity assignment, constants
map to themselves, and function applications compose by induction
hypothesis. -/
theorem quotientTermEvalIdentity {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S} {hTA : IsGeneratedTermAlgebra L H}
    (t : Term L) (ht : t ∈ H) :
    termEval (quotientHintikkaStructure hL H S hHS hTA)
      (quotientIdentityAssignment hL H S hHS hTA) t =
    ⟨t, ht⟩ :=
-- BEGIN PROOF
by
  induction t with
  | var x =>
    simp only [termEval, quotientIdentityAssignment]
    exact dif_pos ht
  | const c =>
    simp only [termEval, quotientHintikkaStructure]
  | func f ts ih =>
    -- By closedSubterm: since func f ts ∈ H, each ts i ∈ H
    simp only [termEval, quotientHintikkaStructure]
    apply Subtype.ext
    simp only
    congr 1
    funext i
    have hti : ts i ∈ H := hTA.closedSubterm f ts ht i
    have ihi := ih i hti
    exact congrArg Subtype.val ihi

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

helper theorem termInHEq {L : Language} {H : Set (Term L)}
    (hTA : IsGeneratedTermAlgebra L H) (t : Term L)
    (hvars : ∀ x, x ∈ termFV t → Term.var x ∈ H) : t ∈ H := by
-- BEGIN PROOF
  induction t with
  | var x => exact hvars x rfl
  | const c => exact hTA.closedConst c
  | func f ts ih =>
    exact hTA.closedFunc f ts (fun i => ih i (fun x hx => hvars x ⟨i, hx⟩))

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


helper /-- Helper: if a formula is valid (true in all structures under all
assignments), then adding it to the antecedent of a sequent does not
change validity. The forward direction holds because the extra formula
is true anyway; the backward direction holds because removing a true
antecedent only weakens the hypothesis. -/
theorem addValidToAntecedent_iff {L : Language}
    (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L)) (A : FormulaN L)
    (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
    sequentValid (Sequent.mk (Γ ++ Δ) Λ) ↔
    sequentValid (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  constructor
  · -- Forward: valid without A → valid with A (weakening)
    intro h M s hant
    exact h M s (fun F hF => by
      rcases memcat_cases hF with hΓ | hΔ
      · exact hant F (mem1_left hΓ)
      · exact hant F (mem1_right hΔ))
  · -- Backward: valid with A → valid without A
    intro h M s hant
    exact h M s (fun F hF => by
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hant F (memcat_left h1)
      · exact hvalid M s
      · exact hant F (memcat_right h3))

helper /-- Helper: adding multiple valid formulas (appended) to the
antecedent does not change validity. -/
theorem addValidListToAntecedent_iff {L : Language}
    (axioms : List (FormulaN L)) (ant succ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms, ∀ (M : Structure L) (s : Assignment M),
      formulaEvalN M A s) :
    sequentValid (Sequent.mk ant succ) ↔
    sequentValid (Sequent.mk (ant ++ axioms) succ) := by
-- BEGIN PROOF
  constructor
  · intro h M s hant
    exact h M s (fun F hF => hant F (List.mem_append_left _ hF))
  · intro h M s hant
    exact h M s (fun F hF => by
      rcases List.mem_append.mp hF with horiginal | hax
      · exact hant F horiginal
      · exact hvalid F hax M s)









helper /-- Helper: adding a valid formula to the antecedent does not change
falsifiability in a specific model. -/
theorem addValidToAntecedent_falsifiableIn_iff {L : Language}
    (M : Structure L)
    (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L)) (A : FormulaN L)
    (hvalid : ∀ (s : Assignment M), formulaEvalN M A s) :
    sequentFalsifiableIn M (Sequent.mk (Γ ++ Δ) Λ) ↔
    sequentFalsifiableIn M (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  constructor
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hant F (memcat_left h1)
      · exact hvalid s
      · exact hant F (memcat_right h3),
    hsucc⟩
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases memcat_cases hF with hΓ | hΔ
      · exact hant F (mem1_left hΓ)
      · exact hant F (mem1_right hΔ),
    hsucc⟩

helper /-- Helper: adding multiple valid formulas (appended) to the
antecedent does not change falsifiability in a specific model. -/
theorem addValidListToAntecedent_falsifiableIn_iff {L : Language}
    (M : Structure L)
    (axioms : List (FormulaN L)) (ant succ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms, ∀ (s : Assignment M),
      formulaEvalN M A s) :
    sequentFalsifiableIn M (Sequent.mk ant succ) ↔
    sequentFalsifiableIn M (Sequent.mk (ant ++ axioms) succ) := by
-- BEGIN PROOF
  constructor
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases List.mem_append.mp hF with horiginal | hax
      · exact hant F horiginal
      · exact hvalid F hax s,
    hsucc⟩
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => hant F (List.mem_append_left _ hF), hsucc⟩





proof_of eqRuleFalsificationIff := by
  have hsingle (A : FormulaN L)
      (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
      sequentFalsifiable (Sequent.mk (Γ ++ [A]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ) := by
    change (∃ M, sequentFalsifiableIn M (Sequent.mk (Γ ++ [A]) Δ)) ↔
      (∃ M, sequentFalsifiableIn M (Sequent.mk Γ Δ))
    apply exists_congr
    intro M
    simpa only [List.append_nil] using
      (addValidToAntecedent_falsifiableIn_iff M Γ [] Δ A (hvalid M)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hsingle _ (eqReflValid hL t)
  · intro f ss ts
    exact hsingle _ (eqFuncCongValid hL f ss ts)
  · intro P ss ts
    exact hsingle _ (eqPredCongValid hL P ss ts)
  · intro s1 s2 t1 t2
    exact hsingle _ (eqEqCongValid hL s1 s2 t1 t2)
  · intro axioms _hne haxioms
    change (∃ M, sequentFalsifiableIn M (Sequent.mk (Γ ++ axioms) Δ)) ↔
      (∃ M, sequentFalsifiableIn M (Sequent.mk Γ Δ))
    apply exists_congr
    intro M
    exact (addValidListToAntecedent_falsifiableIn_iff M axioms Γ Δ
      (fun A hA s => eqAxiomInstanceValid hL A (haxioms A hA) M s)).symm


helper /-- Lemma 5.6.2 (companion): For arbitrary contexts, reflexivity,
function congruence, predicate congruence, equality congruence,
and the nonempty generalized equality rule preserve and reflect validity,
with the equality axioms appended to the antecedent. -/
theorem eqRuleValidityIff {L : Language} (hL : L.hasEquality = true)
    (Γ Δ : List (FormulaN L)) :
    (∀ t : Term L,
      sequentValid (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t]) Δ) ↔
        sequentValid (Sequent.mk Γ Δ)) ∧
    (∀ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
      sequentValid (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ) ↔
        sequentValid (Sequent.mk Γ Δ)) ∧
    (∀ (P : L.predSymbols)
      (ss ts : Fin (L.predArity P) → Term L),
      sequentValid (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ) ↔
        sequentValid (Sequent.mk Γ Δ)) ∧
    (∀ s1 s2 t1 t2 : Term L,
      sequentValid (Sequent.mk (Γ ++ [eqCongruenceImplEq hL s1 s2 t1 t2]) Δ) ↔
        sequentValid (Sequent.mk Γ Δ)) ∧
    (∀ (axioms : List (FormulaN L)) (_hne : axioms ≠ [])
      (_haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A),
      sequentValid (Sequent.mk (Γ ++ axioms) Δ) ↔
        sequentValid (Sequent.mk Γ Δ)) := by
  have hsingle (A : FormulaN L)
      (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
      sequentValid (Sequent.mk (Γ ++ [A]) Δ) ↔
        sequentValid (Sequent.mk Γ Δ) := by
    simpa only [List.append_nil] using
      (addValidToAntecedent_iff Γ [] Δ A hvalid).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hsingle _ (eqReflValid hL t)
  · intro f ss ts
    exact hsingle _ (eqFuncCongValid hL f ss ts)
  · intro P ss ts
    exact hsingle _ (eqPredCongValid hL P ss ts)
  · intro s1 s2 t1 t2
    exact hsingle _ (eqEqCongValid hL s1 s2 t1 t2)
  · intro axioms _hne haxioms
    exact (addValidListToAntecedent_iff axioms Γ Δ
      (fun A hA M s => eqAxiomInstanceValid hL A (haxioms A hA) M s)).symm

proof_of soundnessGEq := 
  -- BEGIN PROOF
  let rec
    /-- Helper: every GEq proof tree has a valid conclusion. -/
    eqTreeValid : ∀ (s : Sequent L), GEqProofTree hL s →
        sequentValid s
      | _, .base g => soundnessG_Ext _ ⟨g⟩
      | _, .axiom_ s hAx => by
          intro M as hant
          obtain ⟨A, hA_ant, hA_suc⟩ := hAx
          exact ⟨A, hA_suc, hant A hA_ant⟩
      | _, .onePremise rule sub =>
          (ruleValidityIff1Ext rule).mpr (eqTreeValid _ sub)
      | _, .twoPremise rule sub1 sub2 =>
          (ruleValidityIff2Ext rule).mpr
            ⟨eqTreeValid _ sub1, eqTreeValid _ sub2⟩
      | _, .eqRefl t Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqReflValid hL t)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqFuncCong f ss ts Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqFuncCongValid hL f ss ts)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqPredCong P ss ts Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqPredCongValid hL P ss ts)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqGeneral axioms hne haxioms Γ Δ sub =>
          (addValidListToAntecedent_iff _ _ _
            (fun A hA M s => eqAxiomInstanceValid hL A (haxioms A hA) M s)).mpr
            (eqTreeValid _ sub)
  by
    obtain ⟨tree⟩ := h
    exact eqTreeValid seq tree


end LCS.FirstOrder.Equality

end
