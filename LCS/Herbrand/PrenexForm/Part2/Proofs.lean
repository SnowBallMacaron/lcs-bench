import LCS.Herbrand.PrenexForm.Part2

section

namespace LCS.Herbrand.PrenexForm

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Equivalence

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Disjunction of two prenex formulas has a prenex equivalent.
    By well-founded induction on the total number of leading quantifiers. -/
theorem disjPrenex {L : Language} (P1 P2 : FormulaN L)
    (hp1 : isPrenex P1) (hp2 : isPrenex P2) :
    ∃ C : FormulaN L, isPrenex C ∧
      foLogEquivN (FormulaN.disj P1 P2) C := by
-- BEGIN PROOF
  -- Reduce to conjPrenex via De Morgan
  -- disj P1 P2 ≡ neg (conj (neg P1) (neg P2))
  -- neg P1, neg P2 have prenex equivs by negPrenex_equiv.
  -- Their conjunction has a prenex equiv by conjPrenex.
  -- Negating that prenex gives another prenex by negPrenex_equiv.
  -- The overall chain is: disj P1 P2 ≡ ... ≡ prenex.
  obtain ⟨NP1, hpNP1, heNP1⟩ := negPrenex_equiv P1 hp1
  obtain ⟨NP2, hpNP2, heNP2⟩ := negPrenex_equiv P2 hp2
  obtain ⟨CJ, hpCJ, heCJ⟩ := conjPrenex NP1 NP2 hpNP1 hpNP2
  obtain ⟨R, hpR, heR⟩ := negPrenex_equiv CJ hpCJ
  refine ⟨R, hpR, ?_⟩
  intro M s
  simp only [formulaEvalN]
  have h1 := heNP1 M s
  have h2 := heNP2 M s
  have h3 := heCJ M s
  have h4 := heR M s
  simp only [formulaEvalN] at h1 h2 h3 h4
  constructor
  · intro h
    apply h4.1; intro hcj
    have ⟨hnp1, hnp2⟩ := h3.2 hcj
    exact h.elim (fun ha => h1.2 hnp1 ha) (fun hb => h2.2 hnp2 hb)
  · intro h
    by_cases ha : formulaEvalN M P1 s
    · exact Or.inl ha
    · by_cases hb : formulaEvalN M P2 s
      · exact Or.inr hb
      · exfalso; exact h4.2 h (h3.1 ⟨h1.1 ha, h2.1 hb⟩)

proof_of prenex_normal_form_exists := by
  -- BEGIN PROOF
    induction A with
    | predN P ts => exact ⟨.predN P ts, trivial, foLogEquivN_refl _⟩
    | eq_ hL t1 t2 => exact ⟨.eq_ hL t1 t2, trivial, foLogEquivN_refl _⟩
    | neg A ih =>
      obtain ⟨B, hpB, heB⟩ := ih
      obtain ⟨C, hpC, heC⟩ := negPrenex_equiv B hpB
      exact ⟨C, hpC, foLogEquivN_trans (foLogEquivN_neg heB) heC⟩
    | conj A1 A2 ih1 ih2 =>
      obtain ⟨B1, hp1, he1⟩ := ih1
      obtain ⟨B2, hp2, he2⟩ := ih2
      obtain ⟨C, hpC, heC⟩ := conjPrenex B1 B2 hp1 hp2
      exact ⟨C, hpC, foLogEquivN_trans (foLogEquivN_conj he1 he2) heC⟩
    | disj A1 A2 ih1 ih2 =>
      obtain ⟨B1, hp1, he1⟩ := ih1
      obtain ⟨B2, hp2, he2⟩ := ih2
      obtain ⟨C, hpC, heC⟩ := disjPrenex B1 B2 hp1 hp2
      exact ⟨C, hpC, foLogEquivN_trans (foLogEquivN_disj he1 he2) heC⟩
    | impl A1 A2 ih1 ih2 =>
      -- A1 → A2 ≡ ¬A1 ∨ A2
      obtain ⟨B1, hp1, he1⟩ := ih1
      obtain ⟨B2, hp2, he2⟩ := ih2
      obtain ⟨NB1, hpNB1, heNB1⟩ := negPrenex_equiv B1 hp1
      obtain ⟨C, hpC, heC⟩ := disjPrenex NB1 B2 hpNB1 hp2
      refine ⟨C, hpC, ?_⟩
      intro M s; simp only [formulaEvalN]
      have e1 := Iff.intro (he1 M s).1 (he1 M s).2
      have e2 := Iff.intro (he2 M s).1 (he2 M s).2
      -- C equiv ¬B1 ∨ B2 equiv (B1 → B2)
      have eC : formulaEvalN M C s ↔
          (formulaEvalN M B1 s → formulaEvalN M B2 s) := by
        have hc' := heC M s; have hn1' := heNB1 M s
        simp only [formulaEvalN] at hc' hn1'
        exact ⟨fun heval hb1 => (hc'.2 heval).elim
                (fun hn => absurd hb1 (hn1'.2 hn)) id,
               fun h => hc'.1 (by
                by_cases hb1 : formulaEvalN M B1 s
                · exact Or.inr (h hb1)
                · exact Or.inl (hn1'.1 hb1))⟩
      constructor
      · intro himp; exact eC.mpr (fun hb1 => e2.mp (himp (e1.mpr hb1)))
      · intro h ha; exact e2.mpr (eC.mp h (e1.mp ha))
    | all x A ih =>
      obtain ⟨B, hpB, heB⟩ := ih
      exact ⟨.all x B, hpB, foLogEquivN_all x heB⟩
    | ex x A ih =>
      obtain ⟨B, hpB, heB⟩ := ih
      exact ⟨.ex x B, hpB, foLogEquivN_ex x heB⟩


helper /-- toPrenexRaw always produces a prenex formula. -/
theorem toPrenexRaw_isPrenex {L : Language}
    (A : FormulaN L) :
    isPrenex (toPrenexRaw A) := by
-- BEGIN PROOF
  induction A with
  | predN P ts => simp [toPrenexRaw, isPrenex, FirstOrder.SemanticsN.isQuantifierFree]
  | eq_ hL t1 t2 => simp [toPrenexRaw, isPrenex, FirstOrder.SemanticsN.isQuantifierFree]
  | neg A ih =>
    simp only [toPrenexRaw]
    apply toPrenexHelper_isPrenex
    simp [FirstOrder.SemanticsN.isQuantifierFree]
    exact prenexMatrix_isQF _ ih
  | conj A B ihA ihB =>
    simp only [toPrenexRaw]
    apply toPrenexHelper_isPrenex
    exact ⟨prenexMatrix_isQF _ ihA, prenexMatrix_isQF _ ihB⟩
  | disj A B ihA ihB =>
    simp only [toPrenexRaw]
    apply toPrenexHelper_isPrenex
    exact ⟨prenexMatrix_isQF _ ihA, prenexMatrix_isQF _ ihB⟩
  | impl A B ihA ihB =>
    simp only [toPrenexRaw]
    apply toPrenexHelper_isPrenex
    exact ⟨prenexMatrix_isQF _ ihA, prenexMatrix_isQF _ ihB⟩
  | all x A ih =>
    simp [toPrenexRaw, isPrenex]
    exact ih
  | ex x A ih =>
    simp [toPrenexRaw, isPrenex]
    exact ih

helper /-- Theorem 7.2.1 (companion theorem): toPrenex always produces a prenex formula. This is the first conjunct of the prenex normal form theorem: the output of the conversion function is in prenex form. -/
theorem toPrenex_isPrenex {L : Language}
    (A : FormulaN L) :
    isPrenex (toPrenex A) :=
-- BEGIN PROOF
  toPrenexRaw_isPrenex (rectifyN A)

proof_of prenex_equiv_conj_distrib_left := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEvalN]
    exact ⟨and_or_left.mp, and_or_left.mpr⟩


proof_of prenex_equiv_conj_distrib_right := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEvalN]
    constructor
    · intro ⟨hor, ha⟩
      exact hor.elim (fun hb => Or.inl ⟨hb, ha⟩) (fun hc => Or.inr ⟨hc, ha⟩)
    · intro h
      exact h.elim (fun ⟨hb, ha⟩ => ⟨Or.inl hb, ha⟩) (fun ⟨hc, ha⟩ => ⟨Or.inr hc, ha⟩)


helper /-- Lemma 7.2.2 (companion theorem): Every literal is a conjunction-of-literals
    (with a single element). -/
theorem literal_isConjOfLiterals {L : Language} (A : FormulaN L)
    (h : isLiteral A) : isConjOfLiterals A :=
-- BEGIN PROOF
by
  cases A with
  | predN _ _ => exact h
  | eq_ _ _ _ => exact h
  | neg B => cases B <;> first | exact h | (simp [isLiteral] at h)
  | _ => simp [isLiteral] at h

helper theorem conjOfLiterals_isDNF {L : Language} (A : FormulaN L)
    (h : isConjOfLiterals A) : isDNF A := by
-- BEGIN PROOF
  cases A with
  | disj _ _ => simp [isConjOfLiterals, isLiteral] at h
  | conj A B => simp [isDNF]; exact h
  | _ => exact h

helper theorem disj_isDNF {L : Language} (A B : FormulaN L)
    (hA : isDNF A) (hB : isDNF B) :
    isDNF (.disj A B) := by
-- BEGIN PROOF
  simp [isDNF]; exact ⟨hA, hB⟩

helper theorem conj_isConjOfLiterals {L : Language} (A B : FormulaN L)
    (hA : isConjOfLiterals A) (hB : isConjOfLiterals B) :
    isConjOfLiterals (.conj A B) := by
-- BEGIN PROOF
  simp [isConjOfLiterals]; exact ⟨hA, hB⟩

helper theorem distribConj_dnf {L : Language} (A : FormulaN L)
    (hA : isConjOfLiterals A) :
    ∀ B : FormulaN L, isDNF B →
    ∃ C : FormulaN L, isDNF C ∧
      foLogEquivN (.conj A B) C := by
-- BEGIN PROOF
  intro B hB
  induction B with
  | disj B1 B2 ih1 ih2 =>
    simp [isDNF] at hB
    obtain ⟨C1, hd1, he1⟩ := ih1 hB.1
    obtain ⟨C2, hd2, he2⟩ := ih2 hB.2
    exact ⟨.disj C1 C2, ⟨hd1, hd2⟩,
      foLogEquivN_trans (prenex_equiv_conj_distrib_left A B1 B2)
        (foLogEquivN_disj he1 he2)⟩
  | _ =>
    exact ⟨.conj A _, conjOfLiterals_isDNF _ (conj_isConjOfLiterals A _ hA hB),
           foLogEquivN_refl _⟩

helper theorem distribDNF {L : Language} :
    ∀ (A B : FormulaN L),
    isDNF A → isDNF B →
    ∃ C : FormulaN L, isDNF C ∧
      foLogEquivN (.conj A B) C := by
-- BEGIN PROOF
  intro A B hA hB
  induction A with
  | disj A1 A2 ih1 ih2 =>
    simp [isDNF] at hA
    obtain ⟨C1, hd1, he1⟩ := ih1 hA.1
    obtain ⟨C2, hd2, he2⟩ := ih2 hA.2
    exact ⟨.disj C1 C2, ⟨hd1, hd2⟩,
      foLogEquivN_trans (prenex_equiv_conj_distrib_right B A1 A2)
        (foLogEquivN_disj he1 he2)⟩
  | _ =>
    exact distribConj_dnf _ hA _ hB

helper theorem neg_conjOfLiterals_dnf {L : Language} (A : FormulaN L)
    (h : isConjOfLiterals A) :
    ∃ B : FormulaN L, isDNF B ∧ foLogEquivN (.neg A) B := by
-- BEGIN PROOF
  induction A with
  | conj A1 A2 ih1 ih2 =>
    simp [isConjOfLiterals] at h
    obtain ⟨B1, hd1, he1⟩ := ih1 h.1
    obtain ⟨B2, hd2, he2⟩ := ih2 h.2
    exact ⟨.disj B1 B2, ⟨hd1, hd2⟩,
      foLogEquivN_trans (foLogEquivN_deMorgan_conj A1 A2)
        (foLogEquivN_disj he1 he2)⟩
  | predN P ts => exact ⟨.neg (.predN P ts), trivial, foLogEquivN_refl _⟩
  | eq_ hL t1 t2 => exact ⟨.neg (.eq_ hL t1 t2), trivial, foLogEquivN_refl _⟩
  | neg B _ =>
    -- neg (neg B) equiv B. B must be an atom (since neg B is a literal).
    cases B with
    | predN P ts => exact ⟨.predN P ts, trivial, foLogEquivN_double_neg _⟩
    | eq_ hL t1 t2 => exact ⟨.eq_ hL t1 t2, trivial, foLogEquivN_double_neg _⟩
    | _ => simp [isConjOfLiterals, isLiteral] at h
  | disj _ _ _ _ => simp [isConjOfLiterals, isLiteral] at h
  | impl _ _ _ _ => simp [isConjOfLiterals, isLiteral] at h
  | all _ _ _ => simp [isConjOfLiterals, isLiteral] at h
  | ex _ _ _ => simp [isConjOfLiterals, isLiteral] at h

helper theorem neg_dnf_dnf {L : Language} :
    ∀ (A : FormulaN L), isDNF A →
    ∃ B : FormulaN L, isDNF B ∧ foLogEquivN (.neg A) B := by
-- BEGIN PROOF
  intro A h
  induction A with
  | disj A1 A2 ih1 ih2 =>
    simp [isDNF] at h
    obtain ⟨B1, hd1, he1⟩ := ih1 h.1
    obtain ⟨B2, hd2, he2⟩ := ih2 h.2
    obtain ⟨C, hdC, heC⟩ := distribDNF B1 B2 hd1 hd2
    exact ⟨C, hdC,
      foLogEquivN_trans (foLogEquivN_deMorgan_disj A1 A2)
        (foLogEquivN_trans (foLogEquivN_conj he1 he2) heC)⟩
  | _ =>
    exact neg_conjOfLiterals_dnf _ h

proof_of qfree_dnf_exists := by
  -- REPAIR(T7-RE): proof pending; DNF reachable from A by the eight identities (the previous proof established isDNF B ∧ foLogEquivN A B only)
  sorry


helper /-- Lemma 7.2.2 (companion theorem): Every disjunction of literals is
quantifier-free. -/
theorem isDisjOfLiterals_quantifierFree {L : Language} (A : FormulaN L)
    (h : isDisjOfLiterals A) : isQuantifierFree A := by
-- BEGIN PROOF
  induction A with
  | disj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | neg A _ => cases A <;> simp_all [isDisjOfLiterals, isLiteral, isQuantifierFree]
  | _ => simp_all [isDisjOfLiterals, isLiteral, isQuantifierFree]

helper /-- Lemma 7.2.2 (companion theorem): The binary CNF grammar implies
quantifier-freeness. -/
theorem isCNF_quantifierFree {L : Language} (A : FormulaN L)
    (h : isCNF A) : isQuantifierFree A := by
-- BEGIN PROOF
  induction A with
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | _ => exact isDisjOfLiterals_quantifierFree _ h

proof_of qfree_cnf_exists := by
  -- BEGIN PROOF
    -- REPAIR(T7-87): proof pending
    sorry


end LCS.Herbrand.PrenexForm

end
