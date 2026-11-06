import LCS.FirstOrder.Semantics.Equivalence

namespace LCS.FirstOrder.Semantics.Equivalence

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.SemanticsN

open Classical

proof_of foLogEquivT_refl := by
  -- BEGIN PROOF
    intro M s
    simp [formulaEvalT]


proof_of foLogEquivT_symm := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hab, hba⟩ := h M s
    exact ⟨hba, hab⟩


proof_of foLogEquivT_trans := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hab, hba⟩ := h1 M s
    obtain ⟨hbc, hcb⟩ := h2 M s
    exact ⟨fun ha => hbc (hab ha), fun hc => hba (hcb hc)⟩


proof_of foLogEquivT_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨ha, hb⟩ => ⟨hAf ha, hBf hb⟩, fun ⟨ha', hb'⟩ => ⟨hAb ha', hBb hb'⟩⟩


proof_of foLogEquivT_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h => h.elim (Or.inl ∘ hAf) (Or.inr ∘ hBf),
           fun h => h.elim (Or.inl ∘ hAb) (Or.inr ∘ hBb)⟩

proof_of foLogEquivT_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hf, hb⟩ := h M s
    exact ⟨fun hna ha' => hna (hb ha'), fun hna' ha => hna' (hf ha)⟩

proof_of validF_equiv_elimination := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩


proof_of validF_impl_as_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h => (em _).elim (fun ha => Or.inr (h ha)) Or.inl,
           fun h ha => h.elim (fun hna => absurd ha hna) id⟩


proof_of validF_disj_as_impl := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h hna => h.elim (fun ha => absurd ha hna) id,
           fun h => (em _).elim Or.inl (fun hna => Or.inr (h hna))⟩


proof_of validF_disj_as_neg_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h ⟨hna, hnb⟩ => h.elim (fun ha => hna ha) (fun hb => hnb hb),
           fun h => (em _).elim Or.inl (fun hna =>
             Or.inr ((em _).elim id (fun hnb => absurd ⟨hna, hnb⟩ h)))⟩


proof_of validF_conj_as_neg_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun ⟨ha, hb⟩ h => h.elim (fun hna => hna ha) (fun hnb => hnb hb),
           fun h => ⟨byContradiction (fun hna => h (Or.inl hna)),
                      byContradiction (fun hnb => h (Or.inr hnb))⟩⟩


proof_of validF_neg_as_impl_falsum := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact Iff.rfl


proof_of validF_falsum_as_contradiction := by
  intro M s
  exact ⟨False.elim, fun h => h.2 h.1⟩


proof_of validF_neg_all_as_ex_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨Classical.not_forall.mp, fun ⟨a, hna⟩ h => hna (h a)⟩

proof_of validF_neg_ex_as_all_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h ⟨a, ha⟩ => h a ha⟩


proof_of validF_all_as_neg_ex_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h ⟨a, hna⟩ => hna (h a), fun h a => byContradiction (fun hna => h ⟨a, hna⟩)⟩


proof_of validF_ex_as_neg_all_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun ⟨a, ha⟩ h => h a ha, fun h => byContradiction (fun hne => h (fun a ha => hne ⟨a, ha⟩))⟩

proof_of foLogEquivN_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨ha, hb⟩ => ⟨hAf ha, hBf hb⟩, fun ⟨ha', hb'⟩ => ⟨hAb ha', hBb hb'⟩⟩


proof_of foLogEquivN_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h => h.elim (Or.inl ∘ hAf) (Or.inr ∘ hBf),
           fun h => h.elim (Or.inl ∘ hAb) (Or.inr ∘ hBb)⟩


proof_of foLogEquivN_impl := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h ha' => hBf (h (hAb ha')), fun h ha => hBb (h (hAf ha))⟩


proof_of foLogEquivN_equiv := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨hab, hba⟩ => ⟨fun ha' => hBf (hab (hAb ha')), fun hb' => hAf (hba (hBb hb'))⟩,
           fun ⟨hab', hba'⟩ => ⟨fun ha => hBb (hab' (hAf ha)), fun hb => hAb (hba' (hBf hb))⟩⟩


proof_of foLogEquivN_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hf, hb⟩ := h M s
    exact ⟨fun hna ha' => hna (hb ha'), fun hna' ha => hna' (hf ha)⟩


proof_of foLogEquivN_all := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    exact ⟨fun hall a => (h M (assignUpdate s x a)).1 (hall a),
           fun hall a => (h M (assignUpdate s x a)).2 (hall a)⟩


proof_of foLogEquivN_ex := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    exact ⟨fun ⟨a, ha⟩ => ⟨a, (h M (assignUpdate s x a)).1 ha⟩,
           fun ⟨a, ha'⟩ => ⟨a, (h M (assignUpdate s x a)).2 ha'⟩⟩

proof_of foLogEquivT_disj_assoc := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_assoc.mp, or_assoc.mpr⟩


proof_of foLogEquivT_conj_assoc := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_assoc.mp, and_assoc.mpr⟩


proof_of foLogEquivT_disj_comm := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨Or.comm.mp, Or.comm.mpr⟩


proof_of foLogEquivT_conj_comm := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨And.comm.mp, And.comm.mpr⟩


proof_of foLogEquivT_disj_distrib := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_and_left.mp, or_and_left.mpr⟩


proof_of foLogEquivT_conj_distrib := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_or_left.mp, and_or_left.mpr⟩


proof_of foLogEquivT_deMorgan_disj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨not_or.mp, not_or.mpr⟩


proof_of foLogEquivT_deMorgan_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEvalT]
    exact ⟨fun h => (em _).elim (fun ha => Or.inr (fun hb => h ⟨ha, hb⟩)) Or.inl,
           fun h ⟨ha, hb⟩ => h.elim (· ha) (· hb)⟩


proof_of foLogEquivT_disj_idem := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_self_iff.mp, or_self_iff.mpr⟩


proof_of foLogEquivT_conj_idem := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_self_iff.mp, and_self_iff.mpr⟩


proof_of foLogEquivT_double_neg := by
  -- BEGIN PROOF
    intro M s; simp [formulaEvalT]


proof_of foLogEquivT_absorb_disj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]
    exact ⟨fun h => h.elim id (fun ⟨ha, _⟩ => ha), Or.inl⟩


proof_of foLogEquivT_absorb_conj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]
    exact ⟨fun ⟨ha, _⟩ => ha, fun ha => ⟨ha, Or.inl ha⟩⟩


proof_of foLogEquivT_excluded_middle := by
  intro M s
  exact ⟨fun _ => trivial, fun _ => em _⟩


proof_of foLogEquivT_disj_identity := by
  intro M s
  exact ⟨fun h => h.elim id (fun hbot => False.elim (hbot.2 hbot.1)), Or.inl⟩


proof_of foLogEquivT_conj_annihilation := by
  intro M s
  exact ⟨And.right, fun hbot => False.elim (hbot.2 hbot.1)⟩


proof_of foLogEquivT_disj_top := by
  intro M s
  exact ⟨fun _ => trivial, fun _ => Or.inr trivial⟩


proof_of foLogEquivT_conj_identity_top := by
  intro M s
  exact ⟨And.left, fun h => ⟨h, trivial⟩⟩


proof_of foLogEquivT_contradiction := by
  intro M s
  exact ⟨fun h => False.elim (h.2 h.1), fun hbot => False.elim (hbot.2 hbot.1)⟩

end LCS.FirstOrder.Semantics.Equivalence
