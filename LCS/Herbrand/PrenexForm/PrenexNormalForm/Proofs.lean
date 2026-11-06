import LCS.Herbrand.PrenexForm.PrenexNormalForm

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

end LCS.Herbrand.PrenexForm
