import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import LCS.CutElim.LK.Syntax
import Attach
import LCS.CutElim.LK.Soundness.ProofsStamp

section
namespace LCS.CutElim.LK
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.CompletenessBridge

-- ===================================================================
-- Lemma 6.2.1: soundness_FOLK
-- ===================================================================
-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (axioms valid): Every axiom of LK is valid. An axiom
has the form [A] => [A], which is trivially valid. -/
theorem lemma_6_2_1_axioms_valid {L : Language} (s : Sequent L)
    (h : isFOLKAxiom s) : sequentValid s := by
-- BEGIN PROOF
  obtain ⟨A, hAnt, hSucc⟩ := h
  intro M val hAll
  refine ⟨A, ?_, ?_⟩
  · rw [hSucc]; exact List.Mem.head _
  · exact hAll A (by rw [hAnt]; exact List.Mem.head _)

-- retained: used by LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (one-premise rules preserve validity): For every
one-premise rule of LK, if the premise is valid, then the conclusion
is valid. -/
theorem lemma_6_2_1_rules1_preserve_validity {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (hprem : sequentValid prem) : sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | weakenLeft A Γ Δ =>
    intro M val hAll
    exact hprem M val (fun F hF => hAll F (List.Mem.tail _ hF))
  | weakenRight A Γ Δ =>
    intro M val hAll
    obtain ⟨B, hBmem, hBtrue⟩ := hprem M val hAll
    exact ⟨B, List.mem_append_left _ hBmem, hBtrue⟩
  | contractLeft A Γ Δ =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (A :: A :: Γ) := hF
    match hF' with
    | .head _ => exact hAll F (List.Mem.head _)
    | .tail _ (.head _) => exact hAll F (List.Mem.head _)
    | .tail _ (.tail _ h) => exact hAll F (List.Mem.tail _ h)
  | contractRight A Γ Δ =>
    intro M val hAll
    obtain ⟨B, hBmem, hBtrue⟩ := hprem M val hAll
    have hBmem' : B ∈ Δ ++ [A, A] := hBmem
    have hB : B ∈ Δ ++ [A] := by
      rcases List.mem_append.mp hBmem' with h | h
      · exact List.mem_append_left _ h
      · match h with
        | .head _ => exact List.mem_append_right _ (List.Mem.head _)
        | .tail _ (.head _) => exact List.mem_append_right _ (List.Mem.head _)
        | .tail _ (.tail _ h) => exact (nomatch h)
    exact ⟨B, hB, hBtrue⟩
  | exchangeLeft Γ A B Δ' Λ =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ Γ ++ [A, B] ++ Δ' := hF
    have : F ∈ Γ ++ [B, A] ++ Δ' := by
      rcases List.mem_append.mp hF' with h | h
      · rcases List.mem_append.mp h with h1 | h1
        · exact List.mem_append_left _ (List.mem_append_left _ h1)
        · match h1 with
          | .head _ =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.tail _ (.head _)))
          | .tail _ (.head _) =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.head _))
          | .tail _ (.tail _ h1) => exact (nomatch h1)
      · exact List.mem_append_right _ h
    exact hAll F this
  | exchangeRight Γ Δ' A B Λ =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [A, B] ++ Λ := hFmem
    have hF : F ∈ Δ' ++ [B, A] ++ Λ := by
      rcases List.mem_append.mp hFmem' with h | h
      · rcases List.mem_append.mp h with h1 | h1
        · exact List.mem_append_left _ (List.mem_append_left _ h1)
        · match h1 with
          | .head _ =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.tail _ (.head _)))
          | .tail _ (.head _) =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.head _))
          | .tail _ (.tail _ h1) => exact (nomatch h1)
      · exact List.mem_append_right _ h
    exact ⟨F, hF, hFtrue⟩
  | andLeftL A B Γ Δ' =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (A :: Γ) := hF
    match hF' with
    | .head _ =>
      have hconj := hAll (FormulaN.conj F B) (List.Mem.head _)
      simp [formulaEvalN] at hconj
      exact hconj.1
    | .tail _ h => exact hAll F (List.Mem.tail _ h)
  | andLeftR A B Γ Δ' =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (B :: Γ) := hF
    match hF' with
    | .head _ =>
      have hconj := hAll (FormulaN.conj A F) (List.Mem.head _)
      simp [formulaEvalN] at hconj
      exact hconj.2
    | .tail _ h => exact hAll F (List.Mem.tail _ h)
  | orRightL A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [A] := hFmem
    rcases List.mem_append.mp hFmem' with hd | ha
    · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
    · match ha with
      | .head _ =>
        refine ⟨FormulaN.disj F B,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]; left; exact hFtrue
      | .tail _ ha => exact (nomatch ha)
  | orRightR A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [B] := hFmem
    rcases List.mem_append.mp hFmem' with hd | ha
    · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
    · match ha with
      | .head _ =>
        refine ⟨FormulaN.disj A F,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]; right; exact hFtrue
      | .tail _ ha => exact (nomatch ha)
  | implRight A B Γ Δ' =>
    intro M val hAll
    by_cases hA : formulaEvalN M A val
    · obtain ⟨F, hFmem, hFtrue⟩ := hprem M val (fun G hG => by
        have hG' : G ∈ (A :: Γ) := hG
        match hG' with
        | .head _ => exact hA
        | .tail _ h => exact hAll G h)
      have hFmem' : F ∈ Δ' ++ [B] := hFmem
      rcases List.mem_append.mp hFmem' with h | h
      · exact ⟨F, List.mem_append_left _ h, hFtrue⟩
      · match h with
        | .head _ =>
          refine ⟨FormulaN.impl A F,
            List.mem_append_right _ (List.Mem.head _), ?_⟩
          simp [formulaEvalN]; intro; exact hFtrue
        | .tail _ h => exact (nomatch h)
    · refine ⟨FormulaN.impl A B,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]; intro hA'; exact absurd hA' hA
  | negLeft A Γ Δ' =>
    intro M val hAll
    have hneg := hAll (FormulaN.neg A) (List.Mem.head _)
    simp [formulaEvalN] at hneg
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ hF)
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hΓ
    have hFmem' : F ∈ Δ' ++ [A] := hFmem
    rcases List.mem_append.mp hFmem' with h | h
    · exact ⟨F, h, hFtrue⟩
    · match h with
      | .head _ => exact absurd hFtrue hneg
      | .tail _ h => exact (nomatch h)
  | negRight A Γ Δ' =>
    intro M val hAll
    by_cases hA : formulaEvalN M A val
    · obtain ⟨F, hFmem, hFtrue⟩ := hprem M val (fun G hG => by
        have hG' : G ∈ (A :: Γ) := hG
        match hG' with
        | .head _ => exact hA
        | .tail _ h => exact hAll G h)
      exact ⟨F, List.mem_append_left _ hFmem, hFtrue⟩
    · refine ⟨FormulaN.neg A,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]; exact hA
  | allLeft t_sub x A Γ Δ' hfree =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (formulaSubstN A t_sub x :: Γ) := hF
    cases hF' with
    | head =>
      have hall := hAll (FormulaN.all x A) (List.Mem.head _)
      simp [formulaEvalN] at hall
      exact (formulaSubstEvalDirectN val A t_sub x hfree).mpr
        (hall (termEval M val t_sub))
    | tail _ h => exact hAll F (List.Mem.tail _ h)
  | allRight y_eig x A Γ Δ' hfresh hfreeFor =>
    intro M val hAll
    by_cases hΔ : ∃ B ∈ Δ', formulaEvalN M B val
    · obtain ⟨B, hB, hBt⟩ := hΔ
      exact ⟨B, List.mem_append_left _ hB, hBt⟩
    · suffices hall : ∀ a, formulaEvalN M A (assignUpdate val x a) from
        ⟨FormulaN.all x A,
          List.mem_append_right _ (List.Mem.head _), hall⟩
      intro a
      have hfreshΓ : ∀ F ∈ Γ, y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_left _ hF)
      have hfreshSucc : ∀ F ∈ Δ' ++ [FormulaN.all x A],
          y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_right _ hF)
      have hfreshΔ : ∀ F ∈ Δ', y_eig ∉ formulaFVN F := fun F hF =>
        hfreshSucc F (List.mem_append_left _ hF)
      have hantY : ∀ F ∈ Γ,
          formulaEvalN M F (assignUpdate val y_eig a) := fun F hF => by
        have hFs := hAll F hF
        exact (coincidenceLemmaN M F val (assignUpdate val y_eig a)
          (fun y hy => by
            simp [assignUpdate]; intro hzy
            exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
      obtain ⟨B, hBmem, hBtrue⟩ :=
        hprem M (assignUpdate val y_eig a) hantY
      have hBmem' : B ∈ Δ' ++ [formulaSubstN A (Term.var y_eig) x] := hBmem
      rcases List.mem_append.mp hBmem' with hBΔ | hBsub
      · have hBs : formulaEvalN M B val := by
          exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
            (fun y hy => by
              simp [assignUpdate]; intro hzy
              exact absurd (hzy ▸ hy) (hfreshΔ B hBΔ))).mp hBtrue
        exact absurd ⟨B, hBΔ, hBs⟩ hΔ
      · have hBeq : B = formulaSubstN A (Term.var y_eig) x := by
          cases hBsub with
          | head => rfl
          | tail _ h => exact (nomatch h)
        subst hBeq
        rw [formulaSubstEvalDirectN (assignUpdate val y_eig a) A
            (Term.var y_eig) x hfreeFor] at hBtrue
        simp [termEval, assignUpdate] at hBtrue
        have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
          intro z hz hzx hzy; subst hzy
          exact hfreshSucc (FormulaN.all x A)
            (List.mem_append_right _ (List.Mem.head _))
            (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
        exact (coincidenceLemmaN M A
          (fun k => if k = x then a
                    else if k = y_eig then a else val k)
          (assignUpdate val x a)
          (fun z hz => by
            simp [assignUpdate]
            split
            · rfl
            · rename_i hzx; split
              · rename_i hzy
                exact absurd hzy (yA z hz hzx)
              · rfl)).mp hBtrue
  | exLeft y_eig x A Γ Δ' hfresh hfreeFor =>
    intro M val hAll
    have hexA := hAll (FormulaN.ex x A) (List.Mem.head _)
    simp [formulaEvalN] at hexA
    obtain ⟨a, ha⟩ := hexA
    have hfreshΓ : ∀ F ∈ Γ, y_eig ∉ formulaFVN F := fun F hF =>
      hfresh F (List.mem_append_left _ (List.Mem.tail _ hF))
    have hfreshΔ : ∀ F ∈ Δ', y_eig ∉ formulaFVN F := fun F hF =>
      hfresh F (List.mem_append_right _ hF)
    have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
      intro z hz hzx hzy; subst hzy
      exact hfresh (FormulaN.ex x A)
        (List.mem_append_left _ (List.Mem.head _))
        (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
    have hAyx : formulaEvalN M (formulaSubstN A (Term.var y_eig) x)
        (assignUpdate val y_eig a) := by
      rw [formulaSubstEvalDirectN (assignUpdate val y_eig a) A
        (Term.var y_eig) x hfreeFor]
      simp [termEval, assignUpdate]
      exact (coincidenceLemmaN M A (assignUpdate val x a)
        (fun k => if k = x then a
                  else if k = y_eig then a else val k)
        (fun z hz => by
          simp [assignUpdate]
          split
          · rfl
          · rename_i hzx; split
            · rename_i hzy
              exact absurd hzy (yA z hz hzx)
            · rfl)).mp ha
    have hΓy : ∀ F ∈ Γ,
        formulaEvalN M F (assignUpdate val y_eig a) := fun F hF => by
      have hFs := hAll F (List.Mem.tail _ hF)
      exact (coincidenceLemmaN M F val (assignUpdate val y_eig a)
        (fun y hy => by
          simp [assignUpdate]; intro hzy
          exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
    have hantY : ∀ F ∈ (formulaSubstN A (Term.var y_eig) x :: Γ),
        formulaEvalN M F (assignUpdate val y_eig a) := by
      intro F hF
      cases hF with
      | head => exact hAyx
      | tail _ h => exact hΓy F h
    obtain ⟨B, hBmem, hBtrue⟩ :=
      hprem M (assignUpdate val y_eig a) hantY
    exact ⟨B, hBmem, by
      exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
        (fun y hy => by
          simp [assignUpdate]; intro hzy
          exact absurd (hzy ▸ hy) (hfreshΔ B hBmem))).mp hBtrue⟩
  | exRight t_sub x A Γ Δ' hfree =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [formulaSubstN A t_sub x] := hFmem
    rcases List.mem_append.mp hFmem' with h | h
    · exact ⟨F, List.mem_append_left _ h, hFtrue⟩
    · have hFeq : F = formulaSubstN A t_sub x := by
        cases h with
        | head => rfl
        | tail _ h => exact (nomatch h)
      subst hFeq
      refine ⟨FormulaN.ex x A,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]
      exact ⟨termEval M val t_sub,
        (formulaSubstEvalDirectN val A t_sub x hfree).mp hFtrue⟩

-- retained: used by LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (two-premise rules preserve validity): For every
two-premise rule of LK (including cut), if both premises are valid,
then the conclusion is valid. -/
theorem lemma_6_2_1_rules2_preserve_validity {L : Language}
    {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
    (hprem1 : sequentValid prem1) (hprem2 : sequentValid prem2) :
    sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | cut A Γ Δ' Λ Θ =>
    intro M val hAll
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.mem_append_left _ hF)
    have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
      hAll F (List.mem_append_right _ hF)
    obtain ⟨B, hBmem, hBtrue⟩ := hprem1 M val hΓ
    have hBmem' : B ∈ Δ' ++ [A] := hBmem
    rcases List.mem_append.mp hBmem' with h | h
    · exact ⟨B, List.mem_append_left _ h, hBtrue⟩
    · match h with
      | .head _ =>
        obtain ⟨C, hCmem, hCtrue⟩ := hprem2 M val (fun F hF => by
          have hF' : F ∈ (B :: Λ) := hF
          match hF' with
          | .head _ => exact hBtrue
          | .tail _ h => exact hΛ F h)
        exact ⟨C, List.mem_append_right _ hCmem, hCtrue⟩
      | .tail _ h => exact (nomatch h)
  | andRight A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F1, hF1mem, hF1true⟩ := hprem1 M val hAll
    have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
    rcases List.mem_append.mp hF1mem' with h | h
    · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
    · match h with
      | .head _ =>
        obtain ⟨F2, hF2mem, hF2true⟩ := hprem2 M val hAll
        have hF2mem' : F2 ∈ Δ' ++ [B] := hF2mem
        rcases List.mem_append.mp hF2mem' with h2 | h2
        · exact ⟨F2, List.mem_append_left _ h2, hF2true⟩
        · match h2 with
          | .head _ =>
            refine ⟨FormulaN.conj F1 F2,
              List.mem_append_right _ (List.Mem.head _), ?_⟩
            simp [formulaEvalN]
            exact ⟨hF1true, hF2true⟩
          | .tail _ h2 => exact (nomatch h2)
      | .tail _ h => exact (nomatch h)
  | orLeft A B Γ Δ' =>
    intro M val hAll
    have hdisj := hAll (FormulaN.disj A B) (List.Mem.head _)
    simp [formulaEvalN] at hdisj
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ hF)
    cases hdisj with
    | inl hA =>
      apply hprem1 M val
      intro F hF
      have hF' : F ∈ (A :: Γ) := hF
      match hF' with
      | .head _ => exact hA
      | .tail _ h => exact hΓ F h
    | inr hB =>
      apply hprem2 M val
      intro F hF
      have hF' : F ∈ (B :: Γ) := hF
      match hF' with
      | .head _ => exact hB
      | .tail _ h => exact hΓ F h
  | implLeft A B Γ Δ' Λ Θ =>
    intro M val hAll
    have himpl := hAll (FormulaN.impl A B) (List.Mem.head _)
    simp [formulaEvalN] at himpl
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ (List.mem_append_left _ hF))
    have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ (List.mem_append_right _ hF))
    obtain ⟨F1, hF1mem, hF1true⟩ := hprem1 M val hΓ
    have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
    rcases List.mem_append.mp hF1mem' with h | h
    · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
    · match h with
      | .head _ =>
        have hB := himpl hF1true
        obtain ⟨F2, hF2mem, hF2true⟩ := hprem2 M val (fun F hF => by
          have hF' : F ∈ (B :: Λ) := hF
          match hF' with
          | .head _ => exact hB
          | .tail _ h => exact hΛ F h)
        exact ⟨F2, List.mem_append_right _ hF2mem, hF2true⟩
      | .tail _ h => exact (nomatch h)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LK.Part2, LCS.FOResolution.Method.Completeness.Completeness
/-- Helper: proofTreeValid — induction on the indexed FOLKProofTree
establishes validity of the (indexed) conclusion. The per-rule
validity arguments are delegated to the Lemma 6.2.1 companion
theorems `lemma_6_2_1_rules1_preserve_validity` and
`lemma_6_2_1_rules2_preserve_validity`. -/
theorem proofTreeValid {L : Language} {s : Sequent L}
    (t : FOLKProofTree s) : sequentValid s := by
-- BEGIN PROOF
  induction t with
  | axiom_ s hax => exact lemma_6_2_1_axioms_valid s hax
  | onePremise rule _t ih =>
    exact lemma_6_2_1_rules1_preserve_validity rule ih
  | twoPremise rule _t1 _t2 ih1 ih2 =>
    exact lemma_6_2_1_rules2_preserve_validity rule ih1 ih2

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LK.Part2, LCS.FOResolution.Method.Completeness.Completeness
/-- Lemma 6.2.1 (provable sequent valid): Every LK-provable sequent
is valid. -/
theorem soundness_FOLK {L : Language} (seq : Sequent L)
    (h : folkProvable seq) : sequentValid seq := by
-- BEGIN PROOF
  obtain ⟨t⟩ := h
  exact proofTreeValid t

/-- Lemma 6.2.1: Over a language without equality, every LK axiom is valid,
every LK rule preserves validity, and every LK-provable sequent is valid. -/
@[blueprint "chap6__lemma_6_2_1" (main := true)]
theorem lemma_6_2_1NoEq {L : Language} (hL : L.withoutEquality) :
    (∀ s : Sequent L, isFOLKAxiomNoEq hL s → sequentValid s) ∧
    (∀ {prem conc : Sequent L}, (rule : FOLKStep1NoEq hL prem conc) →
      sequentValid prem → sequentValid conc) ∧
    (∀ {prem1 prem2 conc : Sequent L}, (rule : FOLKStep2NoEq hL prem1 prem2 conc) →
      sequentValid prem1 → sequentValid prem2 → sequentValid conc) ∧
    (∀ seq : Sequent L, folkProvableNoEq hL seq → sequentValid seq) 

end LCS.CutElim.LK
end
