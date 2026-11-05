import LCS.Herbrand.NNFHauptsatz.Soundness

namespace LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SyntaxN.Variables

open LCS.Herbrand.NNFHauptsatz

open LCS.CutElim.Hauptsatz

open LCS.Herbrand.PrenexForm

open LCS.FirstOrder.SemanticsN.Substitution

helper /-- If B is in the maximal quantified subformulae of A, then B is a
universal or existential quantifier formula. -/
theorem maxQuantSub_is_quant {L : Language}
    (A B : FormulaN L)
    (h : Membership.mem (maxQuantSubformulaeCore A) B) :
    (∃ x D, B = FormulaN.all x D) ∨ (∃ x D, B = FormulaN.ex x D) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd h id
  | disj _ _ ih1 ih2 => rcases h with h1 | h2; exact ih1 h1; exact ih2 h2
  | conj _ _ ih1 ih2 => rcases h with h1 | h2; exact ih1 h1; exact ih2 h2
  | all x D => exact Or.inl ⟨x, D, h⟩
  | ex x D => exact Or.inr ⟨x, D, h⟩

helper /-- When B is a quantifier formula not in QF(A), replacing B with C
in A is the identity operation. -/
theorem replaceMaxQuantSub_not_in_qf {L : Language} [DecidableEq (FormulaN L)]
    (A B C : FormulaN L)
    (hBquant : (∃ x D, B = FormulaN.all x D) ∨ (∃ x D, B = FormulaN.ex x D))
    (h : ¬ Membership.mem (maxQuantSubformulaeCore A) B) :
    replaceMaxQuantSubCore A B C = A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl | eq_ _ _ => rfl
  | neg _ => rfl | impl _ _ => rfl
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = B) := by
      rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;> subst heq <;> intro h <;> cases h
    simp [hne]; exact ⟨ih1 (fun hm => h (Or.inl hm)), ih2 (fun hm => h (Or.inr hm))⟩
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = B) := by
      rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;> subst heq <;> intro h <;> cases h
    simp [hne]; exact ⟨ih1 (fun hm => h (Or.inl hm)), ih2 (fun hm => h (Or.inr hm))⟩
  | all x D =>
    simp only [replaceMaxQuantSubCore]
    simp [show ¬ (FormulaN.all x D = B) from fun heq => h (by subst heq; rfl)]
  | ex x D =>
    simp only [replaceMaxQuantSubCore]
    simp [show ¬ (FormulaN.ex x D = B) from fun heq => h (by subst heq; rfl)]

helper /-- Lemma 7.4.1 (helper): If formula A in NNF is satisfied in structure
M by assignment s, then the formula A[C/B] (obtained by replacing the
maximal quantified subformula B with C via replaceMaxQuantSubCore) is also
satisfied in M by s. This is sub-case (ii) of the forall-left soundness
argument where A is not equal to C. Proved by structural induction on A
considering the disjunction (A1 or A2) and conjunction (A1 and A2)
cases. Requires DecidableEq on FormulaN L for the replacement
operation. -/
theorem satisfaction_preserved_subformula_subst
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A B C : FormulaN L)
    (hBinQF : Membership.mem (maxQuantSubformulaeCore A) B)
    (hSatA : formulaEvalN M A s)
    (hSatC : formulaEvalN M C s) :
    formulaEvalN M (replaceMaxQuantSubCore A B C) s :=
-- BEGIN PROOF
by
  have hBquant := maxQuantSub_is_quant A B hBinQF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd hBinQF id
  | all x D =>
    simp only [replaceMaxQuantSubCore]
    simp [hBinQF.symm]; exact hSatC
  | ex x D =>
    simp only [replaceMaxQuantSubCore]
    simp [hBinQF.symm]; exact hSatC
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = B) := by
      rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;> subst heq <;> intro h <;> cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    rcases hSatA with hSat1 | hSat2
    · left
      by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) B
      · exact ih1 h1 hSat1
      · rw [replaceMaxQuantSub_not_in_qf A1 B C hBquant h1]; exact hSat1
    · right
      by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) B
      · exact ih2 h2 hSat2
      · rw [replaceMaxQuantSub_not_in_qf A2 B C hBquant h2]; exact hSat2
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = B) := by
      rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;> subst heq <;> intro h <;> cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    obtain ⟨hSat1, hSat2⟩ := hSatA
    constructor
    · by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) B
      · exact ih1 h1 hSat1
      · rw [replaceMaxQuantSub_not_in_qf A1 B C hBquant h1]; exact hSat1
    · by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) B
      · exact ih2 h2 hSat2
      · rw [replaceMaxQuantSub_not_in_qf A2 B C hBquant h2]; exact hSat2

helper /-- Lemma 7.4.1 (companion theorem): Case 1 of the soundness proof. For the
forall-left rule of G2nnf, replacing one selected maximal occurrence of
`forall x B` by `B[t/x]` preserves satisfaction when `t` is free for `x` in
`B`.  The occurrence witness selects exactly one branch even when another
maximal occurrence has the same formula syntax. -/
theorem forall_left_soundness
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (B : FormulaN L) (t : Term L)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (hFreeFor : isFreeForN t x B)
    (hSatA : formulaEvalN M A s) :
    formulaEvalN M
      (occurrence.replace (formulaSubstN B t x)) s :=
-- BEGIN PROOF
by
  revert hSelected hSatA
  induction occurrence with
  | all y D =>
    intro hSelected hSatA
    have heq : FormulaN.all y D = FormulaN.all x B := hSelected
    have hyx : x = y := (FormulaN.all.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.all.inj heq |>.2).symm
    subst hyx; subst hDB
    simp only [MaxQuantifierOccurrence.replace]
    simp only [formulaEvalN] at hSatA
    exact (formulaSubstEvalDirectN s B t x hFreeFor).mpr (hSatA (termEval M s t))
  | ex _ _ =>
    intro hSelected _
    cases hSelected
  | conjLeft _ _ ih =>
    intro hSelected hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    exact ⟨ih hSelected hSatA.1, hSatA.2⟩
  | conjRight _ _ ih =>
    intro hSelected hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    exact ⟨hSatA.1, ih hSelected hSatA.2⟩
  | disjLeft _ _ ih =>
    intro hSelected hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    rcases hSatA with hSat1 | hSat2
    · exact Or.inl (ih hSelected hSat1)
    · exact Or.inr hSat2
  | disjRight _ _ ih =>
    intro hSelected hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    rcases hSatA with hSat1 | hSat2
    · exact Or.inl hSat1
    · exact Or.inr (ih hSelected hSat2)

helper /-- For any value a making B false under s[x:=a], replacing C = all x B
with B[y/x] in A preserves falsification under s[y:=a], when A is
false under s and y is fresh for A. -/
theorem replace_falsified_universal
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (x : Nat) (B : FormulaN L) (y : Nat)
    (hCinQF : Membership.mem (maxQuantSubformulaeCore A) (FormulaN.all x B))
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hFalsA : ¬ formulaEvalN M A s)
    (a : M.carrier)
    (hFalsB : ¬ formulaEvalN M B (assignUpdate s x a)) :
    ¬ formulaEvalN M (replaceMaxQuantSubCore A (FormulaN.all x B)
          (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd hCinQF id
  | all z D =>
    have heq : FormulaN.all z D = FormulaN.all x B := hCinQF.symm
    have hzx : x = z := (FormulaN.all.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.all.inj heq |>.2).symm
    subst hzx; subst hDB
    simp only [replaceMaxQuantSubCore, ite_true]
    intro hsat
    rw [formulaSubstEvalDirectN (assignUpdate s y a) B (Term.var y) x hFreeFor] at hsat
    simp only [termEval] at hsat
    apply hFalsB
    exact (coincidenceLemmaN M B _ _
      (fun v hv => by
        simp only [assignUpdate]
        by_cases hvx : v = x
        · simp [hvx]
        · by_cases hvy : v = y
          · subst hvy; exfalso; apply hYfreshA; exact ⟨hv, hvx⟩
          · simp [hvx, hvy])).mp hsat
  | ex z D => exfalso; cases hCinQF
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = FormulaN.all x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hFalsA ⊢
    have hF1 : ¬ formulaEvalN M A1 s := fun h => hFalsA (Or.inl h)
    have hF2 : ¬ formulaEvalN M A2 s := fun h => hFalsA (Or.inr h)
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    intro hR; rcases hR with hR1 | hR2
    · by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.all x B)
      · exact ih1 h1 hfr1 hF1 hR1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inl ⟨x, B, rfl⟩) h1] at hR1
        exact hF1 ((formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mp hR1)
    · by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.all x B)
      · exact ih2 h2 hfr2 hF2 hR2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inl ⟨x, B, rfl⟩) h2] at hR2
        exact hF2 ((formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mp hR2)
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = FormulaN.all x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hFalsA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    intro ⟨hR1, hR2⟩; apply hFalsA; constructor
    · by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.all x B)
      · exact Classical.byContradiction (fun hF1 => ih1 h1 hfr1 hF1 hR1)
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inl ⟨x, B, rfl⟩) h1] at hR1
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mp hR1
    · by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.all x B)
      · exact Classical.byContradiction (fun hF2 => ih2 h2 hfr2 hF2 hR2)
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inl ⟨x, B, rfl⟩) h2] at hR2
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mp hR2

helper /-- When the universal formula all x B is true in M under s (i.e., for
every domain element a, B is satisfied under s[x:=a]), and formula A is
falsified, replacing all x B with B[y/x] in A preserves falsification
under s[y:=a] for any a. The base case A = all x B is contradictory
(true and false simultaneously). -/
theorem replace_true_universal_preserves_false
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (x : Nat) (B : FormulaN L) (y : Nat)
    (hCinQF : Membership.mem (maxQuantSubformulaeCore A) (FormulaN.all x B))
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hFalsA : ¬ formulaEvalN M A s)
    (hAllTrue : ∀ a : M.carrier, formulaEvalN M B (assignUpdate s x a))
    (a : M.carrier) :
    ¬ formulaEvalN M (replaceMaxQuantSubCore A (FormulaN.all x B)
          (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd hCinQF id
  | all z D =>
    have heq : FormulaN.all z D = FormulaN.all x B := hCinQF.symm
    have hzx : x = z := (FormulaN.all.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.all.inj heq |>.2).symm
    subst hzx; subst hDB
    exfalso; apply hFalsA; simp only [formulaEvalN]; exact hAllTrue
  | ex z D => exfalso; cases hCinQF
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = FormulaN.all x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hFalsA ⊢
    have hF1 : ¬ formulaEvalN M A1 s := fun h => hFalsA (Or.inl h)
    have hF2 : ¬ formulaEvalN M A2 s := fun h => hFalsA (Or.inr h)
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    intro hR; rcases hR with hR1 | hR2
    · by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.all x B)
      · exact ih1 h1 hfr1 hF1 hR1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inl ⟨x, B, rfl⟩) h1] at hR1
        exact hF1 ((formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mp hR1)
    · by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.all x B)
      · exact ih2 h2 hfr2 hF2 hR2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inl ⟨x, B, rfl⟩) h2] at hR2
        exact hF2 ((formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mp hR2)
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = FormulaN.all x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hFalsA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    intro ⟨hR1, hR2⟩; apply hFalsA; constructor
    · by_cases h1 : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.all x B)
      · exact Classical.byContradiction (fun hF1 => ih1 h1 hfr1 hF1 hR1)
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inl ⟨x, B, rfl⟩) h1] at hR1
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mp hR1
    · by_cases h2 : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.all x B)
      · exact Classical.byContradiction (fun hF2 => ih2 h2 hfr2 hF2 hR2)
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inl ⟨x, B, rfl⟩) h2] at hR2
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mp hR2

helper /-- Lemma 7.4.1 (companion theorem): Case 2 of the soundness proof.  If `A`
is falsified and `y` is fresh for `A`, replacing one selected maximal
occurrence of `forall x B` by `B[y/x]` is falsified under `s[y := a]` for
some domain element `a`. -/
theorem forall_right_soundness
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (B : FormulaN L) (y : Nat)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hFalsA : ¬ formulaEvalN M A s) :
    ∃ (a : M.carrier),
      ¬ formulaEvalN M
        (occurrence.replace (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) :=
-- BEGIN PROOF
by
  revert hSelected hYfreshA hFalsA
  induction occurrence with
  | all z D =>
    intro hSelected hYfreshA hFalsA
    have heq : FormulaN.all z D = FormulaN.all x B := hSelected
    have hzx : x = z := (FormulaN.all.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.all.inj heq |>.2).symm
    subst hzx; subst hDB
    simp only [MaxQuantifierOccurrence.replace]
    simp only [formulaEvalN] at hFalsA
    have ⟨a, ha⟩ := Classical.not_forall.mp hFalsA
    refine ⟨a, ?_⟩
    intro hsat
    rw [formulaSubstEvalDirectN (assignUpdate s y a) B (Term.var y) x hFreeFor] at hsat
    simp only [termEval, assignUpdate] at hsat
    apply ha
    exact (coincidenceLemmaN M B _ _
      (fun v hv => by
        simp only [assignUpdate]
        by_cases hvx : v = x
        · simp [hvx]
        · by_cases hvy : v = y
          · subst hvy; exfalso; apply hYfreshA; exact ⟨hv, hvx⟩
          · simp [hvx, hvy])).mp hsat
  | ex _ _ =>
    intro hSelected _ _
    cases hSelected
  | conjLeft _ C ih =>
    intro hSelected hYfreshA hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    by_cases hSatC : formulaEvalN M C s
    · obtain ⟨a, hFalsReplaced⟩ :=
        ih hSelected
          (fun h => hYfreshA (Or.inl h))
          (fun h => hFalsA ⟨h, hSatC⟩)
      exact ⟨a, fun h => hFalsReplaced h.1⟩
    · have a₀ := Classical.choice M.carrierNonempty
      refine ⟨a₀, ?_⟩
      intro hSat
      exact hSatC
        ((formulaEval_assignUpdate_irrelevant s y a₀ C
          (fun h => hYfreshA (Or.inr h))).mp hSat.2)
  | conjRight A _ ih =>
    intro hSelected hYfreshA hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    by_cases hSatA : formulaEvalN M A s
    · obtain ⟨a, hFalsReplaced⟩ :=
        ih hSelected
          (fun h => hYfreshA (Or.inr h))
          (fun h => hFalsA ⟨hSatA, h⟩)
      exact ⟨a, fun h => hFalsReplaced h.2⟩
    · have a₀ := Classical.choice M.carrierNonempty
      refine ⟨a₀, ?_⟩
      intro hSat
      exact hSatA
        ((formulaEval_assignUpdate_irrelevant s y a₀ A
          (fun h => hYfreshA (Or.inl h))).mp hSat.1)
  | disjLeft _ C ih =>
    intro hSelected hYfreshA hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    obtain ⟨a, hFalsReplaced⟩ :=
      ih hSelected
        (fun h => hYfreshA (Or.inl h))
        (fun h => hFalsA (Or.inl h))
    refine ⟨a, ?_⟩
    intro hSat
    rcases hSat with hSat | hSat
    · exact hFalsReplaced hSat
    · exact hFalsA (Or.inr
        ((formulaEval_assignUpdate_irrelevant s y a C
          (fun h => hYfreshA (Or.inr h))).mp hSat))
  | disjRight A _ ih =>
    intro hSelected hYfreshA hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    obtain ⟨a, hFalsReplaced⟩ :=
      ih hSelected
        (fun h => hYfreshA (Or.inr h))
        (fun h => hFalsA (Or.inr h))
    refine ⟨a, ?_⟩
    intro hSat
    rcases hSat with hSat | hSat
    · exact hFalsA (Or.inl
        ((formulaEval_assignUpdate_irrelevant s y a A
          (fun h => hYfreshA (Or.inl h))).mp hSat))
    · exact hFalsReplaced hSat

helper /-- Lemma 7.4.1 (helper): Existential analog of
`forall_left_soundness`.  Replacing one selected maximal occurrence of
`exists x B` by `B[t/x]` preserves falsification when `t` is free for `x` in
`B`. -/
theorem exists_right_soundness
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (B : FormulaN L) (t : Term L)
    (hSelected : occurrence.selected = FormulaN.ex x B)
    (hFreeFor : isFreeForN t x B)
    (hFalsA : ¬ formulaEvalN M A s) :
    ¬ formulaEvalN M
      (occurrence.replace (formulaSubstN B t x)) s := by
-- BEGIN PROOF
  revert hSelected hFalsA
  induction occurrence with
  | all _ _ =>
    intro hSelected _
    cases hSelected
  | ex y D' =>
    intro hSelected hFalsA
    have heq : FormulaN.ex y D' = FormulaN.ex x B := hSelected
    have hyx : x = y := (FormulaN.ex.inj heq |>.1).symm
    have hDB : B = D' := (FormulaN.ex.inj heq |>.2).symm
    subst hyx; subst hDB
    simp only [MaxQuantifierOccurrence.replace]
    simp only [formulaEvalN] at hFalsA
    have hAll : ∀ a, ¬ formulaEvalN M B (assignUpdate s x a) := by
      intro a ha; exact hFalsA ⟨a, ha⟩
    intro hsat
    rw [formulaSubstEvalDirectN s B t x hFreeFor] at hsat
    exact hAll (termEval M s t) hsat
  | conjLeft _ _ ih =>
    intro hSelected hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    intro hSat
    apply hFalsA
    exact ⟨Classical.byContradiction
      (fun hFals => ih hSelected hFals hSat.1), hSat.2⟩
  | conjRight _ _ ih =>
    intro hSelected hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    intro hSat
    apply hFalsA
    exact ⟨hSat.1, Classical.byContradiction
      (fun hFals => ih hSelected hFals hSat.2)⟩
  | disjLeft _ _ ih =>
    intro hSelected hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    intro hSat
    rcases hSat with hSat | hSat
    · exact ih hSelected (fun h => hFalsA (Or.inl h)) hSat
    · exact hFalsA (Or.inr hSat)
  | disjRight _ _ ih =>
    intro hSelected hFalsA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hFalsA ⊢
    intro hSat
    rcases hSat with hSat | hSat
    · exact hFalsA (Or.inl hSat)
    · exact ih hSelected (fun h => hFalsA (Or.inr h)) hSat

helper /-- For any value a making B true under s[x:=a], replacing D = ex x B
with B[y/x] in A preserves satisfaction under s[y:=a], when A is
true under s and y is fresh for A. -/
theorem replace_satisfied_existential
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (x : Nat) (B : FormulaN L) (y : Nat)
    (hDinQF : Membership.mem (maxQuantSubformulaeCore A) (FormulaN.ex x B))
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hSatA : formulaEvalN M A s)
    (a : M.carrier)
    (hSatB : formulaEvalN M B (assignUpdate s x a)) :
    formulaEvalN M (replaceMaxQuantSubCore A (FormulaN.ex x B)
          (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd hDinQF id
  | ex z D =>
    have heq : FormulaN.ex z D = FormulaN.ex x B := hDinQF.symm
    have hzx : x = z := (FormulaN.ex.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.ex.inj heq |>.2).symm
    subst hzx; subst hDB
    simp only [replaceMaxQuantSubCore, ite_true]
    rw [formulaSubstEvalDirectN (assignUpdate s y a) B (Term.var y) x hFreeFor]
    simp only [termEval, assignUpdate]
    exact (coincidenceLemmaN M B _ _
      (fun v hv => by
        simp only [assignUpdate]
        by_cases hvx : v = x
        · simp [hvx]
        · by_cases hvy : v = y
          · subst hvy; exfalso; apply hYfreshA; exact ⟨hv, hvx⟩
          · simp [hvx, hvy])).mpr hSatB
  | all z D => exfalso; cases hDinQF
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = FormulaN.ex x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    rcases hSatA with h1 | h2
    · left
      by_cases hm : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.ex x B)
      · exact ih1 hm hfr1 h1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mpr h1
    · right
      by_cases hm : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.ex x B)
      · exact ih2 hm hfr2 h2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mpr h2
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = FormulaN.ex x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    constructor
    · by_cases hm : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.ex x B)
      · exact ih1 hm hfr1 hSatA.1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mpr hSatA.1
    · by_cases hm : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.ex x B)
      · exact ih2 hm hfr2 hSatA.2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mpr hSatA.2

helper /-- When the existential formula ex x B is false in M under s (i.e.,
for every domain element a, B is falsified under s[x:=a]), and formula A
is satisfied, replacing ex x B with B[y/x] in A preserves satisfaction
under s[y:=a] for any a. The base case A = ex x B is contradictory
(satisfied yet the existential is false). -/
theorem replace_false_existential_preserves_sat
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (x : Nat) (B : FormulaN L) (y : Nat)
    (hDinQF : Membership.mem (maxQuantSubformulaeCore A) (FormulaN.ex x B))
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hSatA : formulaEvalN M A s)
    (hExFalse : ∀ a : M.carrier, ¬ formulaEvalN M B (assignUpdate s x a))
    (a : M.carrier) :
    formulaEvalN M (replaceMaxQuantSubCore A (FormulaN.ex x B)
          (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ | neg _ | impl _ _ =>
    exact absurd hDinQF id
  | ex z D =>
    have heq : FormulaN.ex z D = FormulaN.ex x B := hDinQF.symm
    have hzx : x = z := (FormulaN.ex.inj heq |>.1).symm
    have hDB : B = D := (FormulaN.ex.inj heq |>.2).symm
    subst hzx; subst hDB
    exfalso; simp only [formulaEvalN] at hSatA
    obtain ⟨a', ha'⟩ := hSatA
    exact hExFalse a' ha'
  | all z D => exfalso; cases hDinQF
  | disj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.disj A1 A2 = FormulaN.ex x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    rcases hSatA with h1 | h2
    · left
      by_cases hm : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.ex x B)
      · exact ih1 hm hfr1 h1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mpr h1
    · right
      by_cases hm : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.ex x B)
      · exact ih2 hm hfr2 h2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mpr h2
  | conj A1 A2 ih1 ih2 =>
    simp only [replaceMaxQuantSubCore]
    have hne : ¬ (FormulaN.conj A1 A2 = FormulaN.ex x B) := by intro h; cases h
    simp [hne]; simp only [formulaEvalN] at hSatA ⊢
    have hfr1 : ¬ Membership.mem (formulaFVN A1) y := fun h => hYfreshA (Or.inl h)
    have hfr2 : ¬ Membership.mem (formulaFVN A2) y := fun h => hYfreshA (Or.inr h)
    constructor
    · by_cases hm : Membership.mem (maxQuantSubformulaeCore A1) (FormulaN.ex x B)
      · exact ih1 hm hfr1 hSatA.1
      · rw [replaceMaxQuantSub_not_in_qf A1 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A1 hfr1).mpr hSatA.1
    · by_cases hm : Membership.mem (maxQuantSubformulaeCore A2) (FormulaN.ex x B)
      · exact ih2 hm hfr2 hSatA.2
      · rw [replaceMaxQuantSub_not_in_qf A2 _ _ (Or.inr ⟨x, B, rfl⟩) hm]
        exact (formulaEval_assignUpdate_irrelevant s y a A2 hfr2).mpr hSatA.2

helper /-- Lemma 7.4.1 (helper): Existential analog of
`forall_right_soundness`.  If `A` is satisfied and `y` is fresh for `A`,
replacing one selected maximal occurrence of `exists x B` by `B[y/x]` is
satisfied under `s[y := a]` for some domain element `a`. -/
theorem exists_left_soundness
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (B : FormulaN L) (y : Nat)
    (hSelected : occurrence.selected = FormulaN.ex x B)
    (hYfreshA : ¬ Membership.mem (formulaFVN A) y)
    (hFreeFor : isFreeForN (Term.var y) x B)
    (hSatA : formulaEvalN M A s) :
    ∃ (a : M.carrier),
      formulaEvalN M
        (occurrence.replace (formulaSubstN B (Term.var y) x))
        (assignUpdate s y a) :=
-- BEGIN PROOF
by
  revert hSelected hYfreshA hSatA
  induction occurrence with
  | all _ _ =>
    intro hSelected _ _
    cases hSelected
  | ex z D' =>
    intro hSelected hYfreshA hSatA
    have heq : FormulaN.ex z D' = FormulaN.ex x B := hSelected
    have hzx : x = z := (FormulaN.ex.inj heq |>.1).symm
    have hDB : B = D' := (FormulaN.ex.inj heq |>.2).symm
    subst hzx; subst hDB
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    obtain ⟨a, ha⟩ := hSatA
    refine ⟨a, ?_⟩
    rw [formulaSubstEvalDirectN (assignUpdate s y a) B (Term.var y) x hFreeFor]
    simp only [termEval, assignUpdate]
    exact (coincidenceLemmaN M B _ _
      (fun v hv => by
        simp only [assignUpdate]
        by_cases hvx : v = x
        · simp [hvx]
        · by_cases hvy : v = y
          · subst hvy; exfalso; apply hYfreshA; exact ⟨hv, hvx⟩
          · simp [hvx, hvy])).mpr ha
  | conjLeft _ C ih =>
    intro hSelected hYfreshA hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    obtain ⟨a, hSatReplaced⟩ :=
      ih hSelected (fun h => hYfreshA (Or.inl h)) hSatA.1
    exact ⟨a, hSatReplaced,
      (formulaEval_assignUpdate_irrelevant s y a C
        (fun h => hYfreshA (Or.inr h))).mpr hSatA.2⟩
  | conjRight A _ ih =>
    intro hSelected hYfreshA hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    obtain ⟨a, hSatReplaced⟩ :=
      ih hSelected (fun h => hYfreshA (Or.inr h)) hSatA.2
    exact ⟨a,
      (formulaEval_assignUpdate_irrelevant s y a A
        (fun h => hYfreshA (Or.inl h))).mpr hSatA.1,
      hSatReplaced⟩
  | disjLeft _ C ih =>
    intro hSelected hYfreshA hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    rcases hSatA with hSatA | hSatC
    · obtain ⟨a, hSatReplaced⟩ :=
        ih hSelected (fun h => hYfreshA (Or.inl h)) hSatA
      exact ⟨a, Or.inl hSatReplaced⟩
    · have a₀ := Classical.choice M.carrierNonempty
      exact ⟨a₀, Or.inr
        ((formulaEval_assignUpdate_irrelevant s y a₀ C
          (fun h => hYfreshA (Or.inr h))).mpr hSatC)⟩
  | disjRight A _ ih =>
    intro hSelected hYfreshA hSatA
    simp only [MaxQuantifierOccurrence.replace, formulaEvalN] at hSatA ⊢
    rcases hSatA with hSatA | hSatB
    · have a₀ := Classical.choice M.carrierNonempty
      exact ⟨a₀, Or.inl
        ((formulaEval_assignUpdate_irrelevant s y a₀ A
          (fun h => hYfreshA (Or.inl h))).mpr hSatA)⟩
    · obtain ⟨a, hSatReplaced⟩ :=
        ih hSelected (fun h => hYfreshA (Or.inr h)) hSatB
      exact ⟨a, Or.inr hSatReplaced⟩

helper /-- Lemma 7.4.1 (companion rule-level step): Single inference-rule validity
preservation. Given any G2nnf rule whose side conditions are met, if every
premise sequent is valid, then the conclusion sequent is valid. Proved by
contrapositive using `g2nnf_rule_falsification_preservation`. Exact maximal
occurrence selection and quantifier shape are constructor data; the remaining
quantifier side conditions are free-for and eigenvariable freshness. The full
tree-level statement is `g2nnf_tree_soundness` /
`g2nnf_provable_implies_valid`. -/
theorem g2nnf_soundness
    {L : Language} (hL : L.withoutEquality) [DecidableEq (FormulaN L)]
    (rule : G2nnfRule L hL)
    (hSC : G2nnfRule.SideConditions rule)
    (hPremsValid : ∀ prem ∈
      G2nnfRule.premises rule,
      setSequentValid prem.1 prem.2) :
    setSequentValid
      (G2nnfRule.conclusion rule).1
      (G2nnfRule.conclusion rule).2 :=
-- BEGIN PROOF
by
  intro M s hGamma
  exact Classical.byContradiction fun hNotDelta => by
    have hDelta : ∀ B, Membership.mem (G2nnfRule.conclusion rule).2 B →
        ¬ formulaEvalN M B s :=
      fun B hB hEval => hNotDelta ⟨B, hB, hEval⟩
    have hFals : setSequentFalsifiableIn M
        (G2nnfRule.conclusion rule).1
        (G2nnfRule.conclusion rule).2 :=
      ⟨s, hGamma, hDelta⟩
    obtain ⟨prem, hPremIn, s', hGamma', hDelta'⟩ :=
      g2nnf_core_rule_falsification_preservation M rule.val hSC hFals
    have hPremValid := hPremsValid prem hPremIn
    obtain ⟨B, hBin, hBeval⟩ := hPremValid M s' hGamma'
    exact hDelta' B hBin hBeval

proof_of g2nnf_provable_implies_valid := by
  -- BEGIN PROOF
    intro hProv M s hG
    obtain ⟨T⟩ := hProv
    exact Classical.byContradiction fun hNotDelta => by
      have hDelta : ∀ B, Membership.mem Delta B → ¬ formulaEvalN M B s :=
        fun B hB hEval => hNotDelta ⟨B, hB, hEval⟩
      exact g2nnf_tree_soundness hL M T ⟨s, hG, hDelta⟩


end LCS.Herbrand.NNFHauptsatz.Soundness
