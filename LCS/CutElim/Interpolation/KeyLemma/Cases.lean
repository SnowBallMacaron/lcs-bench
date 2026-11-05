import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair
import LCS.CutElim.Interpolation.QuantifierCases
import Attach
import LCS.CutElim.Interpolation.KeyLemma.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exLeft_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A (Term.var y) x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (d₁ g₂ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₁' : List (FormulaN L))
    (hg' : List.Interleaving g₁' g₂ Γ)
    (hg : List.Interleaving (FormulaN.ex x A :: g₁') g₂ (FormulaN.ex x A :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (FormulaN.ex x A :: Γ) (Δ))
          { gamma1 := FormulaN.ex x A :: g₁', delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A (.var y) x
  let q : SequentPartition (Sequent.mk (X :: Γ) Δ) := ⟨X :: g₁', d₁, g₂, d₂, .left X hg', hd⟩
  obtain ⟨C, hI⟩ := ih q
  have hFreshOther : ∀ F ∈ g₂ ++ d₂, y ∉ formulaFVN F := by
    intro F hF hy
    apply hfresh F ?_ hy
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl <| List.Mem.tail _ (hg'.mem_right hF))
    · exact List.mem_append.mpr (Or.inr (hd.mem_right hF))
  have hyC : y ∉ formulaFVN C := by
    intro hy
    have hi := (hI.fv_common y hy).2
    dsimp [q] at hi
    exact let ⟨F, hF, hyF⟩ := hi
      hFreshOther F hF hyF
  have hp := listFormulaPredSymbols_cons_replace (rest := g₁') (tail := d₁)
    (formulaPredSymbolsN_subst_le_ex A (.var y) x)
  have hc := listFormulaConstSymbols_cons_replace (rest := g₁') (tail := d₁)
    (formulaConstSymbolsN_subst_var_le_ex A y x)
  have hfv : formulaFVN C ⊆ listFormulaFV ((.ex x A :: g₁') ++ d₁) ∩ listFormulaFV (g₂ ++ d₂) := by
    intro v hv
    have hi := hI.fv_common v hv
    dsimp [q] at hi
    exact listFormulaFV_cons_replace_fresh (formulaFV_subst_var_le_ex_union A y x) hFreshOther v hi
  have hn := allNoEq_cons_replace (X := X) (Y := .ex x A) (rest := g₁') (tail := d₁)
    (fun h => formulaSubstN_noEq A (.var y) x h)
  refine ⟨C, ?_⟩
  refine
    { left_provable := ?_
      right_provable := hI.right_provable
      pred_common := ?_
      const_common := ?_
      fv_common := hfv
      no_eq := ?_ }
  · have hfresh' : ∀ F ∈ (Sequent.mk (.ex x A :: g₁') (d₁ ++ [C])).antecedent ++ (Sequent.mk (.ex x A :: g₁')
            (d₁ ++ [C])).succedent,
          y ∉ formulaFVN F := by
      intro F hF
      change F ∈ (.ex x A :: g₁') ++ (d₁ ++ [C]) at hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hF | hF
        · subst F
          exact hfresh _ (by simp)
        · exact hfresh F (List.mem_append.mpr (Or.inl <| List.Mem.tail _ (hg'.mem_left hF)))
      · rcases List.mem_append.mp hF with hF | hF
        · exact hfresh F (List.mem_append.mpr (Or.inr (hd.mem_left hF)))
        · have hFC : F = C := by simpa using hF
          subst F
          exact hyC
    exact lkBot_onePremise (.exLeft y x A g₁' (d₁ ++ [C]) hfresh' hfree)
      (by simpa [q, X, List.append_assoc] using hI.left_provable)
  · intro P hP hne
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hp P hi.1, hi.2⟩
  · intro c hcC
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hc c hi.1, hi.2⟩
  · exact hI.no_eq ∘ allNoEq_rel hn (fun F hF => ⟨F, hF, id⟩)

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exLeft_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A (Term.var y) x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₂' : List (FormulaN L))
    (hg' : List.Interleaving g₁ g₂' Γ)
    (hg : List.Interleaving g₁ (FormulaN.ex x A :: g₂') (FormulaN.ex x A :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (FormulaN.ex x A :: Γ) (Δ))
          { gamma1 := g₁, delta1 := d₁, gamma2 := FormulaN.ex x A :: g₂', delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A (.var y) x
  let q : SequentPartition (Sequent.mk (X :: Γ) Δ) := ⟨g₁, d₁, X :: g₂', d₂, .right X hg', hd⟩
  obtain ⟨C, hI⟩ := ih q
  have hFreshOther : ∀ F ∈ g₁ ++ d₁, y ∉ formulaFVN F := by
    intro F hF hy
    apply hfresh F ?_ hy
    rcases List.mem_append.mp hF with hF | hF
    · exact List.mem_append.mpr (Or.inl <| List.Mem.tail _ (hg'.mem_left hF))
    · exact List.mem_append.mpr (Or.inr (hd.mem_left hF))
  have hyC : y ∉ formulaFVN C := by
    intro hy
    have hi := (hI.fv_common y hy).1
    dsimp [q] at hi
    exact let ⟨F, hF, hyF⟩ := hi
      hFreshOther F hF hyF
  have hp := listFormulaPredSymbols_cons_replace (rest := g₂') (tail := d₂)
    (formulaPredSymbolsN_subst_le_ex A (.var y) x)
  have hc := listFormulaConstSymbols_cons_replace (rest := g₂') (tail := d₂)
    (formulaConstSymbolsN_subst_var_le_ex A y x)
  have hfv : formulaFVN C ⊆ listFormulaFV (g₁ ++ d₁) ∩ listFormulaFV ((.ex x A :: g₂') ++ d₂) := by
    intro v hv
    have hi := hI.fv_common v hv
    dsimp [q] at hi
    have mapped := listFormulaFV_cons_replace_fresh (rest := g₂') (tail := d₂) (other := g₁ ++ d₁)
      (formulaFV_subst_var_le_ex_union A y x)
      hFreshOther v ⟨hi.2, hi.1⟩
    exact ⟨mapped.2, mapped.1⟩
  have hn := allNoEq_cons_replace (X := X) (Y := .ex x A) (rest := g₂') (tail := d₂)
    (fun h => formulaSubstN_noEq A (.var y) x h)
  refine ⟨C, ?_⟩
  refine
    { left_provable := hI.left_provable
      right_provable := ?_
      pred_common := ?_
      const_common := ?_
      fv_common := hfv
      no_eq := ?_ }
  · have h := hI.right_provable
    change lkBotProvable botP hBotArity ⟨[C] ++ (X :: g₂'), d₂⟩ at h
    have h₁ := lkBot_exchangeLeft_at [] C X g₂' d₂ (by simpa using h)
    have hfresh' : ∀ F ∈ (Sequent.mk (.ex x A :: C :: g₂') d₂).antecedent ++
          (Sequent.mk (.ex x A :: C :: g₂') d₂).succedent,
          y ∉ formulaFVN F := by
      intro F hF
      change F ∈ (.ex x A :: C :: g₂') ++ d₂ at hF
      rcases List.mem_append.mp hF with hF | hF
      · rcases List.mem_cons.mp hF with hF | hF
        · subst F
          exact hfresh _ (by simp)
        · rcases List.mem_cons.mp hF with hF | hF
          · subst F
            exact hyC
          · exact hfresh F (List.mem_append.mpr (Or.inl <| List.Mem.tail _ (hg'.mem_right hF)))
      · exact hfresh F (List.mem_append.mpr (Or.inr (hd.mem_right hF)))
    have h₂ := lkBot_onePremise (.exLeft y x A (C :: g₂') d₂ hfresh' hfree) (by simpa [X] using h₁)
    simpa using lkBot_exchangeLeft_at [] (.ex x A) C g₂' d₂ (by simpa using h₂)
  · intro P hP hne
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hi.1, hp P hi.2⟩
  · intro c hcC
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hi.1, hc c hi.2⟩
  · exact hI.no_eq ∘ allNoEq_rel (fun F hF => ⟨F, hF, id⟩) hn

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (y x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F)
    (hfree : isFreeForN (Term.var y) x A)
    (ih : ∀ (p : SequentPartition { antecedent := formulaSubstN A (Term.var y) x :: Γ, succedent := Δ }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := FormulaN.ex x A :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · exact interpolation_exists_exLeft_left L botP hBotArity y x A Γ Δ hfresh hfree (ih) d₁ g₂ d₂ hd g₁' hg' hg
  · exact interpolation_exists_exLeft_right L botP hBotArity y x A Γ Δ hfresh hfree (ih) g₁ d₁ d₂ hd g₂' hg' hg

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exRight_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A t₀ x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ g₂ d₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₁' : List (FormulaN L))
    (hd' : List.Interleaving d₁' d₂ Δ)
    (hd : List.Interleaving (d₁' ++ [FormulaN.ex x A]) d₂ (Δ ++ [FormulaN.ex x A]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A]))
          { gamma1 := g₁, delta1 := d₁' ++ [FormulaN.ex x A], gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A t₀ x
  let q : SequentPartition (Sequent.mk Γ (Δ ++ [X])) := ⟨g₁, d₁' ++ [X], g₂, d₂, hg, hd'.append_left [X]⟩
  obtain ⟨C, hI⟩ := ih q
  have hLeft : lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [.ex x A]) ++ [C]⟩ := by
    have h := hI.left_provable
    change lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [X]) ++ [C]⟩ at h
    have h₁ := lkBot_exchangeRight_at g₁ d₁' X C [] (by simpa [List.append_assoc] using h)
    have h₂ := lkBot_onePremise (.exRight t₀ x A g₁ (d₁' ++ [C]) hfree)
      (by simpa [X, List.append_assoc] using h₁)
    simpa [List.append_assoc] using lkBot_exchangeRight_at g₁ d₁' C (.ex x A) []
        (by simpa [List.append_assoc] using h₂)
  have hRight : lkBotProvable botP hBotArity ⟨[C] ++ g₂, d₂⟩ := hI.right_provable
  let side₁ := g₁ ++ (d₁' ++ [.ex x A])
  let cs := (termConstList t₀).filter (fun c => ¬ listFormulaConstSymbols side₁ c)
  obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ := interpolant_fix_consts
      g₁ (d₁' ++ [.ex x A]) g₂ d₂ C cs hLeft hRight (by
        intro c hc F hF hFc
        have hnot := of_decide_eq_true (List.mem_filter.mp hc).2
        exact hnot ⟨F, by simpa [side₁] using hF, hFc⟩)
  let vs := (termFVList t₀).filter (fun v => ¬ listFormulaFV side₁ v)
  obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ := interpolant_fix_fvs
      g₁ (d₁' ++ [.ex x A]) g₂ d₂ C₁ vs hLeft₁ hRight₁ (by
        intro v hv F hF hFv
        have hnot := of_decide_eq_true (List.mem_filter.mp hv).2
        exact hnot ⟨F, by simpa [side₁] using hF, hFv⟩)
  have hp := listFormulaPredSymbols_snoc_replace (head := g₁) (tail := d₁')
    (formulaPredSymbolsN_subst_le_ex A t₀ x)
  have liftConst : ∀ c, c ∉ cs → listFormulaConstSymbols (g₁ ++ (d₁' ++ [X])) c →
      listFormulaConstSymbols side₁ c := by
    intro c hcs hc
    rcases hc with ⟨F, hF, hFc⟩
    rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inl hF), hFc⟩
    · rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), hFc⟩
      · have hFX : F = X := by simpa using hF
        subst F
        rcases formulaConstSymbolsN_formulaSubst A t₀ x c hFc with hA | ht
        · exact ⟨.ex x A, by simp [side₁], hA⟩
        · exact Classical.byContradiction (fun hnot =>
            hcs (List.mem_filter.mpr ⟨(termConstList_mem t₀ c).mpr ht, decide_eq_true hnot⟩))
  have liftFV : ∀ v, v ∉ vs → listFormulaFV (g₁ ++ (d₁' ++ [X])) v → listFormulaFV side₁ v := by
    intro v hvs hv
    rcases hv with ⟨F, hF, hFv⟩
    rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inl hF), hFv⟩
    · rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), hFv⟩
      · have hFX : F = X := by simpa using hF
        subst F
        rcases formulaFV_formulaSubst A t₀ x v hFv with
          ⟨hA, hvx⟩ | ht
        · exact ⟨.ex x A, by simp [side₁], ⟨hA, hvx⟩⟩
        · exact Classical.byContradiction (fun hnot =>
            hvs (List.mem_filter.mpr ⟨(termFVList_mem t₀ v).mpr ht, decide_eq_true hnot⟩))
  have hn := allNoEq_snoc_replace (X := X) (Y := .ex x A) (head := g₁) (tail := d₁')
    (fun h => formulaSubstN_noEq A t₀ x h)
  refine ⟨C₂, ?_⟩
  refine
    { left_provable := hLeft₂
      right_provable := hRight₂
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rw [hPred₂, hPred₁] at hP
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hp P hi.1, hi.2⟩
  · intro c hc
    rw [hConst₂] at hc
    obtain ⟨hcC, hcs⟩ := hConst₁ c hc
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨liftConst c hcs hi.1, hi.2⟩
  · intro v hv
    obtain ⟨hvC₁, hvs⟩ := hFV₂ v hv
    have hvC := hFV₁ v hvC₁
    have hi := hI.fv_common v hvC
    dsimp [q] at hi
    exact ⟨liftFV v hvs hi.1, hi.2⟩
  · intro h
    apply hNoEq₂
    apply hNoEq₁
    apply hI.no_eq
    exact allNoEq_rel
      (p := { gamma1 := g₁
              delta1 := d₁' ++ [.ex x A]
              gamma2 := g₂
              delta2 := d₂
              gamma_partition := hg
              delta_partition := hd })
      (q := q) hn (fun F hF => ⟨F, hF, id⟩) h

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exRight_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A t₀ x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ g₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₂' : List (FormulaN L))
    (hd' : List.Interleaving d₁ d₂' Δ)
    (hd : List.Interleaving d₁ (d₂' ++ [FormulaN.ex x A]) (Δ ++ [FormulaN.ex x A]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A]))
          { gamma1 := g₁, delta1 := d₁, gamma2 := g₂, delta2 := d₂' ++ [FormulaN.ex x A], gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let X := formulaSubstN A t₀ x
  let q : SequentPartition (Sequent.mk Γ (Δ ++ [X])) := ⟨g₁, d₁, g₂, d₂' ++ [X], hg, hd'.append_right [X]⟩
  obtain ⟨C, hI⟩ := ih q
  have hLeft : lkBotProvable botP hBotArity ⟨g₁, d₁ ++ [C]⟩ := hI.left_provable
  have hRight : lkBotProvable botP hBotArity ⟨[C] ++ g₂, d₂' ++ [.ex x A]⟩ :=
    lkBot_onePremise (.exRight t₀ x A ([C] ++ g₂) d₂' hfree)
      (by simpa [q, X, List.append_assoc] using hI.right_provable)
  let side₂ := g₂ ++ (d₂' ++ [.ex x A])
  let cs := (termConstList t₀).filter (fun c => ¬ listFormulaConstSymbols side₂ c)
  obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ := interpolant_fix_consts_right
      g₁ d₁ g₂ (d₂' ++ [.ex x A]) C cs hLeft hRight (by
        intro c hc F hF hFc
        have hnot := of_decide_eq_true (List.mem_filter.mp hc).2
        exact hnot ⟨F, by simpa [side₂] using hF, hFc⟩)
  let vs := (termFVList t₀).filter (fun v => ¬ listFormulaFV side₂ v)
  obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ := interpolant_fix_fvs_right
      g₁ d₁ g₂ (d₂' ++ [.ex x A]) C₁ vs hLeft₁ hRight₁ (by
        intro v hv F hF hFv
        have hnot := of_decide_eq_true (List.mem_filter.mp hv).2
        exact hnot ⟨F, by simpa [side₂] using hF, hFv⟩)
  have hp := listFormulaPredSymbols_snoc_replace (head := g₂) (tail := d₂')
    (formulaPredSymbolsN_subst_le_ex A t₀ x)
  have liftConst : ∀ c, c ∉ cs → listFormulaConstSymbols (g₂ ++ (d₂' ++ [X])) c →
      listFormulaConstSymbols side₂ c := by
    intro c hcs hc
    rcases hc with ⟨F, hF, hFc⟩
    rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inl hF), hFc⟩
    · rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), hFc⟩
      · have hFX : F = X := by simpa using hF
        subst F
        rcases formulaConstSymbolsN_formulaSubst A t₀ x c hFc with hA | ht
        · exact ⟨.ex x A, by simp [side₂], hA⟩
        · exact Classical.byContradiction (fun hnot =>
            hcs (List.mem_filter.mpr ⟨(termConstList_mem t₀ c).mpr ht, decide_eq_true hnot⟩))
  have liftFV : ∀ v, v ∉ vs → listFormulaFV (g₂ ++ (d₂' ++ [X])) v → listFormulaFV side₂ v := by
    intro v hvs hv
    rcases hv with ⟨F, hF, hFv⟩
    rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inl hF), hFv⟩
    · rcases List.mem_append.mp hF with hF | hF
      · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), hFv⟩
      · have hFX : F = X := by simpa using hF
        subst F
        rcases formulaFV_formulaSubst A t₀ x v hFv with
          ⟨hA, hvx⟩ | ht
        · exact ⟨.ex x A, by simp [side₂], ⟨hA, hvx⟩⟩
        · exact Classical.byContradiction (fun hnot =>
            hvs (List.mem_filter.mpr ⟨(termFVList_mem t₀ v).mpr ht, decide_eq_true hnot⟩))
  have hn := allNoEq_snoc_replace (X := X) (Y := .ex x A) (head := g₂) (tail := d₂')
    (fun h => formulaSubstN_noEq A t₀ x h)
  refine ⟨C₂, ?_⟩
  refine
    { left_provable := hLeft₂
      right_provable := hRight₂
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rw [hPred₂, hPred₁] at hP
    have hi := hI.pred_common P hP hne
    dsimp [q] at hi
    exact ⟨hi.1, hp P hi.2⟩
  · intro c hc
    rw [hConst₂] at hc
    obtain ⟨hcC, hcs⟩ := hConst₁ c hc
    have hi := hI.const_common c hcC
    dsimp [q] at hi
    exact ⟨hi.1, liftConst c hcs hi.2⟩
  · intro v hv
    obtain ⟨hvC₁, hvs⟩ := hFV₂ v hv
    have hvC := hFV₁ v hvC₁
    have hi := hI.fv_common v hvC
    dsimp [q] at hi
    exact ⟨hi.1, liftFV v hvs hi.2⟩
  · intro h
    apply hNoEq₂
    apply hNoEq₁
    apply hI.no_eq
    exact allNoEq_rel
      (p := { gamma1 := g₁
              delta1 := d₁
              gamma2 := g₂
              delta2 := d₂' ++ [.ex x A]
              gamma_partition := hg
              delta_partition := hd })
      (q := q) (fun F hF => ⟨F, hF, id⟩) hn h

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_exRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (t₀ : Term L)
    (x : Nat)
    (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t₀ x A)
    (ih : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [formulaSubstN A t₀ x] }),
          ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [FormulaN.ex x A] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · exact interpolation_exists_exRight_left L botP hBotArity t₀ x A Γ Δ hfree (ih) g₁ g₂ d₂ hg d₁' hd' hd
  · exact interpolation_exists_exRight_right L botP hBotArity t₀ x A Γ Δ hfree (ih) g₁ d₁ g₂ hg d₂' hd' hd

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_andRight_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [B] }), ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ g₂ d₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₁' : List (FormulaN L))
    (hd' : List.Interleaving d₁' d₂ Δ)
    (hd : List.Interleaving (d₁' ++ [A.conj B]) d₂ (Δ ++ [A.conj B]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [A.conj B]))
          { gamma1 := g₁, delta1 := d₁' ++ [A.conj B], gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let q₁ : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁, d₁' ++ [A], g₂, d₂, hg, hd'.append_left [A]⟩
  let q₂ : SequentPartition (Sequent.mk Γ (Δ ++ [B])) := ⟨g₁, d₁' ++ [B], g₂, d₂, hg, hd'.append_left [B]⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  dsimp [q₁] at hI₁
  dsimp [q₂] at hI₂
  have hLeft₁ : lkBotProvable botP hBotArity ⟨g₁, (d₁' ++ [.conj A B]) ++ [.disj C₁ C₂]⟩ := by
    have h₁ := lkBot_onePremise (.orRightL C₁ C₂ g₁ (d₁' ++ [A])) hI₁.left_provable
    have h₂ := lkBot_exchangeRight_at g₁ d₁' A (.disj C₁ C₂) [] (by simpa [List.append_assoc] using h₁)
    have h₃ := lkBot_onePremise (.orRightR C₁ C₂ g₁ (d₁' ++ [B])) hI₂.left_provable
    have h₄ := lkBot_exchangeRight_at g₁ d₁' B (.disj C₁ C₂) [] (by simpa [List.append_assoc] using h₃)
    have h₅ := lkBot_twoPremise (.andRight A B g₁ (d₁' ++ [.disj C₁ C₂]))
      (by simpa [List.append_assoc] using h₂)
      (by simpa [List.append_assoc] using h₄)
    simpa [List.append_assoc] using (lkBot_exchangeRight_at g₁ d₁' (.disj C₁ C₂)
        (.conj A B) [] (by simpa [List.append_assoc] using h₅))
  have hRight : lkBotProvable botP hBotArity ⟨[.disj C₁ C₂] ++ g₂, d₂⟩ :=
    lkBot_twoPremise (.orLeft C₁ C₂ g₂ d₂) hI₁.right_provable hI₂.right_provable
  have pred₁A : listFormulaPredSymbols (g₁ ++ (d₁' ++ [A])) ⊆
        listFormulaPredSymbols (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaPredSymbols_snoc_replace (formulaPredSymbolsN_conj_left A B)
  have pred₁B : listFormulaPredSymbols (g₁ ++ (d₁' ++ [B])) ⊆
        listFormulaPredSymbols (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaPredSymbols_snoc_replace (formulaPredSymbolsN_conj_right A B)
  have const₁A : listFormulaConstSymbols (g₁ ++ (d₁' ++ [A])) ⊆
        listFormulaConstSymbols (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaConstSymbols_snoc_replace (formulaConstSymbolsN_conj_left A B)
  have const₁B : listFormulaConstSymbols (g₁ ++ (d₁' ++ [B])) ⊆
        listFormulaConstSymbols (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaConstSymbols_snoc_replace (formulaConstSymbolsN_conj_right A B)
  have fv₁A : listFormulaFV (g₁ ++ (d₁' ++ [A])) ⊆ listFormulaFV (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaFV_snoc_replace (formulaFV_conj_left A B)
  have fv₁B : listFormulaFV (g₁ ++ (d₁' ++ [B])) ⊆ listFormulaFV (g₁ ++ (d₁' ++ [.conj A B])) :=
    listFormulaFV_snoc_replace (formulaFV_conj_right A B)
  have noEqA := allNoEq_snoc_replace (X := A) (Y := .conj A B) (head := g₁) (tail := d₁') (fun h => h.1)
  have noEqB := allNoEq_snoc_replace (X := B) (Y := .conj A B) (head := g₁) (tail := d₁') (fun h => h.2)
  refine ⟨.disj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft₁
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨pred₁A P hi.1, hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨pred₁B P hi.1, hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨const₁A c hi.1, hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨const₁B c hi.1, hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨fv₁A v hi.1, hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨fv₁B v hi.1, hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁' ++ [.conj A B]
                  gamma2 := g₂
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) noEqA (fun F hF => ⟨F, hF, id⟩) h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁' ++ [.conj A B]
                  gamma2 := g₂
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) noEqB (fun F hF => ⟨F, hF, id⟩) h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_andRight_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [B] }), ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ g₂ : List (FormulaN L))
    (hg : List.Interleaving g₁ g₂ (Γ))
    (d₂' : List (FormulaN L))
    (hd' : List.Interleaving d₁ d₂' Δ)
    (hd : List.Interleaving d₁ (d₂' ++ [A.conj B]) (Δ ++ [A.conj B]))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (Γ) (Δ ++ [A.conj B]))
          { gamma1 := g₁, delta1 := d₁, gamma2 := g₂, delta2 := d₂' ++ [A.conj B], gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let q₁ : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁, d₁, g₂, d₂' ++ [A], hg, hd'.append_right [A]⟩
  let q₂ : SequentPartition (Sequent.mk Γ (Δ ++ [B])) := ⟨g₁, d₁, g₂, d₂' ++ [B], hg, hd'.append_right [B]⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  have hLeft : lkBotProvable botP hBotArity ⟨g₁, d₁ ++ [.conj C₁ C₂]⟩ :=
    lkBot_twoPremise (.andRight C₁ C₂ g₁ d₁) hI₁.left_provable hI₂.left_provable
  have hRight₁ := lkBot_onePremise (.andLeftL C₁ C₂ g₂ (d₂' ++ [A])) hI₁.right_provable
  have hRight₂ := lkBot_onePremise (.andLeftR C₁ C₂ g₂ (d₂' ++ [B])) hI₂.right_provable
  have hRight : lkBotProvable botP hBotArity ⟨[.conj C₁ C₂] ++ g₂, d₂' ++ [.conj A B]⟩ := lkBot_twoPremise
      (.andRight A B (.conj C₁ C₂ :: g₂) d₂')
      (by simpa [List.append_assoc] using hRight₁)
      (by simpa [List.append_assoc] using hRight₂)
  have pred₂A : listFormulaPredSymbols (g₂ ++ (d₂' ++ [A])) ⊆
        listFormulaPredSymbols (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaPredSymbols_snoc_replace (formulaPredSymbolsN_conj_left A B)
  have pred₂B : listFormulaPredSymbols (g₂ ++ (d₂' ++ [B])) ⊆
        listFormulaPredSymbols (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaPredSymbols_snoc_replace (formulaPredSymbolsN_conj_right A B)
  have const₂A : listFormulaConstSymbols (g₂ ++ (d₂' ++ [A])) ⊆
        listFormulaConstSymbols (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaConstSymbols_snoc_replace (formulaConstSymbolsN_conj_left A B)
  have const₂B : listFormulaConstSymbols (g₂ ++ (d₂' ++ [B])) ⊆
        listFormulaConstSymbols (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaConstSymbols_snoc_replace (formulaConstSymbolsN_conj_right A B)
  have fv₂A : listFormulaFV (g₂ ++ (d₂' ++ [A])) ⊆ listFormulaFV (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaFV_snoc_replace (formulaFV_conj_left A B)
  have fv₂B : listFormulaFV (g₂ ++ (d₂' ++ [B])) ⊆ listFormulaFV (g₂ ++ (d₂' ++ [.conj A B])) :=
    listFormulaFV_snoc_replace (formulaFV_conj_right A B)
  have noEqA := allNoEq_snoc_replace (X := A) (Y := .conj A B) (head := g₂) (tail := d₂') (fun h => h.1)
  have noEqB := allNoEq_snoc_replace (X := B) (Y := .conj A B) (head := g₂) (tail := d₂') (fun h => h.2)
  refine ⟨.conj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨hi.1, pred₂A P hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨hi.1, pred₂B P hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨hi.1, const₂A c hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨hi.1, const₂B c hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨hi.1, fv₂A v hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨hi.1, fv₂B v hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁
                  gamma2 := g₂
                  delta2 := d₂' ++ [.conj A B]
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) (fun F hF => ⟨F, hF, id⟩) noEqA h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁
                  gamma2 := g₂
                  delta2 := d₂' ++ [.conj A B]
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) (fun F hF => ⟨F, hF, id⟩) noEqB h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_andRight (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [B] }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A.conj B] })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hd.append_single_inv with
    ⟨d₁', rfl, hd'⟩ | ⟨d₂', rfl, hd'⟩
  · exact interpolation_exists_andRight_left L botP hBotArity A B Γ Δ (ih₁) (ih₂) g₁ g₂ d₂ hg d₁' hd' hd
  · exact interpolation_exists_andRight_right L botP hBotArity A B Γ Δ (ih₁) (ih₂) g₁ d₁ g₂ hg d₂' hd' hd

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_orLeft_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (d₁ g₂ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₁' : List (FormulaN L))
    (hg' : List.Interleaving g₁' g₂ Γ)
    (hg : List.Interleaving (A.disj B :: g₁') g₂ (A.disj B :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (A.disj B :: Γ) (Δ))
          { gamma1 := A.disj B :: g₁', delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let q₁ : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨A :: g₁', d₁, g₂, d₂, .left A hg', hd⟩
  let q₂ : SequentPartition (Sequent.mk (B :: Γ) Δ) := ⟨B :: g₁', d₁, g₂, d₂, .left B hg', hd⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  have hLeft₁ := lkBot_onePremise (.orRightL C₁ C₂ (A :: g₁') d₁) hI₁.left_provable
  have hLeft₂ := lkBot_onePremise (.orRightR C₁ C₂ (B :: g₁') d₁) hI₂.left_provable
  have hLeft : lkBotProvable botP hBotArity ⟨.disj A B :: g₁', d₁ ++ [.disj C₁ C₂]⟩ := lkBot_twoPremise
      (.orLeft A B g₁' (d₁ ++ [.disj C₁ C₂]))
      (by simpa [List.append_assoc] using hLeft₁)
      (by simpa [List.append_assoc] using hLeft₂)
  have hRight : lkBotProvable botP hBotArity ⟨[.disj C₁ C₂] ++ g₂, d₂⟩ :=
    lkBot_twoPremise (.orLeft C₁ C₂ g₂ d₂) hI₁.right_provable hI₂.right_provable
  have pred₁A : listFormulaPredSymbols ((A :: g₁') ++ d₁) ⊆
        listFormulaPredSymbols ((.disj A B :: g₁') ++ d₁) :=
    listFormulaPredSymbols_cons_replace (formulaPredSymbolsN_disj_left A B)
  have pred₁B : listFormulaPredSymbols ((B :: g₁') ++ d₁) ⊆
        listFormulaPredSymbols ((.disj A B :: g₁') ++ d₁) :=
    listFormulaPredSymbols_cons_replace (formulaPredSymbolsN_disj_right A B)
  have const₁A : listFormulaConstSymbols ((A :: g₁') ++ d₁) ⊆
        listFormulaConstSymbols ((.disj A B :: g₁') ++ d₁) :=
    listFormulaConstSymbols_cons_replace (formulaConstSymbolsN_disj_left A B)
  have const₁B : listFormulaConstSymbols ((B :: g₁') ++ d₁) ⊆
        listFormulaConstSymbols ((.disj A B :: g₁') ++ d₁) :=
    listFormulaConstSymbols_cons_replace (formulaConstSymbolsN_disj_right A B)
  have fv₁A : listFormulaFV ((A :: g₁') ++ d₁) ⊆ listFormulaFV ((.disj A B :: g₁') ++ d₁) :=
    listFormulaFV_cons_replace (formulaFV_disj_left A B)
  have fv₁B : listFormulaFV ((B :: g₁') ++ d₁) ⊆ listFormulaFV ((.disj A B :: g₁') ++ d₁) :=
    listFormulaFV_cons_replace (formulaFV_disj_right A B)
  have noEqA := allNoEq_cons_replace (X := A) (Y := .disj A B) (rest := g₁') (tail := d₁) (fun h => h.1)
  have noEqB := allNoEq_cons_replace (X := B) (Y := .disj A B) (rest := g₁') (tail := d₁) (fun h => h.2)
  refine ⟨.disj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨pred₁A P hi.1, hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨pred₁B P hi.1, hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨const₁A c hi.1, hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨const₁B c hi.1, hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨fv₁A v hi.1, hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨fv₁B v hi.1, hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := .disj A B :: g₁'
                  delta1 := d₁
                  gamma2 := g₂
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) noEqA (fun F hF => ⟨F, hF, id⟩) h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := .disj A B :: g₁'
                  delta1 := d₁
                  gamma2 := g₂
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) noEqB (fun F hF => ⟨F, hF, id⟩) h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_orLeft_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ))
    (g₂' : List (FormulaN L))
    (hg' : List.Interleaving g₁ g₂' Γ)
    (hg : List.Interleaving g₁ (A.disj B :: g₂') (A.disj B :: Γ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (A.disj B :: Γ) (Δ))
          { gamma1 := g₁, delta1 := d₁, gamma2 := A.disj B :: g₂', delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  let q₁ : SequentPartition (Sequent.mk (A :: Γ) Δ) := ⟨g₁, d₁, A :: g₂', d₂, .right A hg', hd⟩
  let q₂ : SequentPartition (Sequent.mk (B :: Γ) Δ) := ⟨g₁, d₁, B :: g₂', d₂, .right B hg', hd⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  have hLeft : lkBotProvable botP hBotArity ⟨g₁, d₁ ++ [.conj C₁ C₂]⟩ :=
    lkBot_twoPremise (.andRight C₁ C₂ g₁ d₁) hI₁.left_provable hI₂.left_provable
  have hRight₁ := lkBot_onePremise (.andLeftL C₁ C₂ (A :: g₂') d₂) hI₁.right_provable
  have hRight₁' := lkBot_exchangeLeft_at [] (.conj C₁ C₂) A g₂' d₂ (by simpa using hRight₁)
  have hRight₂ := lkBot_onePremise (.andLeftR C₁ C₂ (B :: g₂') d₂) hI₂.right_provable
  have hRight₂' := lkBot_exchangeLeft_at [] (.conj C₁ C₂) B g₂' d₂ (by simpa using hRight₂)
  have hRight₃ := lkBot_twoPremise (.orLeft A B (.conj C₁ C₂ :: g₂') d₂)
    (by simpa using hRight₁') (by simpa using hRight₂')
  have hRight : lkBotProvable botP hBotArity ⟨[.conj C₁ C₂] ++ (.disj A B :: g₂'), d₂⟩ :=
    lkBot_exchangeLeft_at [] (.disj A B) (.conj C₁ C₂) g₂' d₂ (by simpa using hRight₃)
  have pred₂A : listFormulaPredSymbols ((A :: g₂') ++ d₂) ⊆
        listFormulaPredSymbols ((.disj A B :: g₂') ++ d₂) :=
    listFormulaPredSymbols_cons_replace (formulaPredSymbolsN_disj_left A B)
  have pred₂B : listFormulaPredSymbols ((B :: g₂') ++ d₂) ⊆
        listFormulaPredSymbols ((.disj A B :: g₂') ++ d₂) :=
    listFormulaPredSymbols_cons_replace (formulaPredSymbolsN_disj_right A B)
  have const₂A : listFormulaConstSymbols ((A :: g₂') ++ d₂) ⊆
        listFormulaConstSymbols ((.disj A B :: g₂') ++ d₂) :=
    listFormulaConstSymbols_cons_replace (formulaConstSymbolsN_disj_left A B)
  have const₂B : listFormulaConstSymbols ((B :: g₂') ++ d₂) ⊆
        listFormulaConstSymbols ((.disj A B :: g₂') ++ d₂) :=
    listFormulaConstSymbols_cons_replace (formulaConstSymbolsN_disj_right A B)
  have fv₂A : listFormulaFV ((A :: g₂') ++ d₂) ⊆ listFormulaFV ((.disj A B :: g₂') ++ d₂) :=
    listFormulaFV_cons_replace (formulaFV_disj_left A B)
  have fv₂B : listFormulaFV ((B :: g₂') ++ d₂) ⊆ listFormulaFV ((.disj A B :: g₂') ++ d₂) :=
    listFormulaFV_cons_replace (formulaFV_disj_right A B)
  have noEqA := allNoEq_cons_replace (X := A) (Y := .disj A B) (rest := g₂') (tail := d₂) (fun h => h.1)
  have noEqB := allNoEq_cons_replace (X := B) (Y := .disj A B) (rest := g₂') (tail := d₂) (fun h => h.2)
  refine ⟨.conj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨hi.1, pred₂A P hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨hi.1, pred₂B P hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨hi.1, const₂A c hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨hi.1, const₂B c hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨hi.1, fv₂A v hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨hi.1, fv₂B v hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁
                  gamma2 := .disj A B :: g₂'
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) (fun F hF => ⟨F, hF, id⟩) noEqA h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := g₁
                  delta1 := d₁
                  gamma2 := .disj A B :: g₂'
                  delta2 := d₂
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) (fun F hF => ⟨F, hF, id⟩) noEqB h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_orLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := A :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Γ, succedent := Δ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A.disj B :: Γ, succedent := Δ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with
    ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · exact interpolation_exists_orLeft_left L botP hBotArity A B Γ Δ (ih₁) (ih₂) d₁ g₂ d₂ hd g₁' hg' hg
  · exact interpolation_exists_orLeft_right L botP hBotArity A B Γ Δ (ih₁) (ih₂) g₁ d₁ d₂ hd g₂' hg' hg

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_left_cover₁₁ (L : Language) (A B : FormulaN L)
    (g₁Γ g₁Λ d₁Δ d₁Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₁Γ ++ (d₁Δ ++ [A]) → ∃ G, G ∈ A.impl B :: (g₁Γ ++ g₁Λ) ++ (d₁Δ ++ d₁Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.Mem.tail _ (List.mem_append.mpr (Or.inl hF))),
      FormulaCover.refl F⟩
  · rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩
    · have hFA : F = A := by simpa using hF
      subst F
      exact ⟨.impl A B, List.mem_append.mpr (Or.inl (List.Mem.head _)), FormulaCover.impl_left A B⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_left_cover₁₂ (L : Language)
    (g₂Γ g₂Λ d₂Δ d₂Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₂Γ ++ d₂Δ → ∃ G, G ∈ g₂Γ ++ g₂Λ ++ (d₂Δ ++ d₂Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_left_cover₂₁ (L : Language) (A B : FormulaN L)
    (g₁Γ g₁Λ d₁Δ d₁Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ B :: g₁Λ ++ d₁Θ → ∃ G, G ∈ A.impl B :: (g₁Γ ++ g₁Λ) ++ (d₁Δ ++ d₁Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with hF | hF
    · subst F
      exact ⟨.impl A B, List.mem_append.mpr (Or.inl (List.Mem.head _)), FormulaCover.impl_right A B⟩
    · exact ⟨F, List.mem_append.mpr (Or.inl <| List.Mem.tail _ (List.mem_append.mpr (Or.inr hF))),
        FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_left_cover₂₂ (L : Language)
    (g₂Γ g₂Λ d₂Δ d₂Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₂Λ ++ d₂Θ → ∃ G, G ∈ g₂Γ ++ g₂Λ ++ (d₂Δ ++ d₂Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_left (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ Λ Θ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Λ, succedent := Θ }), ∃ C, IsInterpolant botP hBotArity p C)
    (d₁ g₂ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ ++ Θ))
    (g₁' : List (FormulaN L))
    (hg' : List.Interleaving g₁' g₂ (Γ.append Λ))
    (hg : List.Interleaving (A.impl B :: g₁') g₂ (A.impl B :: Γ ++ Λ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (A.impl B :: Γ ++ Λ) (Δ ++ Θ))
          { gamma1 := A.impl B :: g₁', delta1 := d₁, gamma2 := g₂, delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  obtain ⟨g₁Γ, g₁Λ, g₂Γ, g₂Λ, rfl, rfl, hgΓ, hgΛ⟩ := hg'.append_split
  obtain ⟨d₁Δ, d₁Θ, d₂Δ, d₂Θ, rfl, rfl, hdΔ, hdΘ⟩ := hd.append_split
  let q₁ : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁Γ, d₁Δ ++ [A], g₂Γ, d₂Δ, hgΓ, hdΔ.append_left [A]⟩
  let q₂ : SequentPartition (Sequent.mk (B :: Λ) Θ) := ⟨B :: g₁Λ, d₁Θ, g₂Λ, d₂Θ, .left B hgΛ, hdΘ⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  dsimp [q₁] at hI₁
  dsimp [q₂] at hI₂
  have hPrem₁ := lkBot_exchangeRight_at g₁Γ d₁Δ A C₁ [] (by simpa [List.append_assoc] using hI₁.left_provable)
  have hLeft₀ := lkBot_twoPremise (.implLeft A B g₁Γ (d₁Δ ++ [C₁]) g₁Λ (d₁Θ ++ [C₂]))
    (by simpa [List.append_assoc] using hPrem₁)
    hI₂.left_provable
  have hLeft₁ := lkBot_sinkRight (.impl A B :: (g₁Γ ++ g₁Λ)) d₁Δ C₁ d₁Θ [C₂]
    (by simpa [List.append_assoc] using hLeft₀)
  have hLeft : lkBotProvable botP hBotArity ⟨.impl A B :: (g₁Γ ++ g₁Λ), (d₁Δ ++ d₁Θ) ++ [.disj C₁ C₂]⟩ :=
    lkBot_disjRight_both C₁ C₂ (.impl A B :: (g₁Γ ++ g₁Λ)) (d₁Δ ++ d₁Θ)
      (by simpa [List.append_assoc] using hLeft₁)
  have hRight₁ : lkBotProvable botP hBotArity ⟨C₁ :: (g₂Γ ++ g₂Λ), d₂Δ ++ d₂Θ⟩ := lkBot_weaken_to
      (C₁ :: g₂Γ) d₂Δ
      (C₁ :: (g₂Γ ++ g₂Λ)) (d₂Δ ++ d₂Θ)
      (by
        intro F hF
        simp only [List.mem_cons, List.mem_append] at hF ⊢
        exact hF.elim Or.inl (fun h => Or.inr (Or.inl h)))
      (by
        intro F hF
        exact List.mem_append.mpr (Or.inl hF))
      hI₁.right_provable
  have hRight₂ : lkBotProvable botP hBotArity ⟨C₂ :: (g₂Γ ++ g₂Λ), d₂Δ ++ d₂Θ⟩ := lkBot_weaken_to
      (C₂ :: g₂Λ) d₂Θ
      (C₂ :: (g₂Γ ++ g₂Λ)) (d₂Δ ++ d₂Θ)
      (by
        intro F hF
        simp only [List.mem_cons, List.mem_append] at hF ⊢
        exact hF.elim Or.inl (fun h => Or.inr (Or.inr h)))
      (by
        intro F hF
        exact List.mem_append.mpr (Or.inr hF))
      hI₂.right_provable
  have hRight : lkBotProvable botP hBotArity ⟨[.disj C₁ C₂] ++ (g₂Γ ++ g₂Λ), d₂Δ ++ d₂Θ⟩ := lkBot_twoPremise
      (.orLeft C₁ C₂ (g₂Γ ++ g₂Λ) (d₂Δ ++ d₂Θ))
      hRight₁ hRight₂
  have cover₁₁ : ∀ F, F ∈ g₁Γ ++ (d₁Δ ++ [A]) → ∃ G ∈ (.impl A B :: (g₁Γ ++ g₁Λ)) ++ (d₁Δ ++ d₁Θ),
        FormulaCover F G := by
    exact interpolation_exists_implLeft_left_cover₁₁ L A B g₁Γ g₁Λ d₁Δ d₁Θ
  have cover₁₂ : ∀ F, F ∈ g₂Γ ++ d₂Δ → ∃ G ∈ (g₂Γ ++ g₂Λ) ++ (d₂Δ ++ d₂Θ), FormulaCover F G := by
    exact interpolation_exists_implLeft_left_cover₁₂ L g₂Γ g₂Λ d₂Δ d₂Θ
  have cover₂₁ : ∀ F, F ∈ (B :: g₁Λ) ++ d₁Θ → ∃ G ∈ (.impl A B :: (g₁Γ ++ g₁Λ)) ++ (d₁Δ ++ d₁Θ),
        FormulaCover F G := by
    exact interpolation_exists_implLeft_left_cover₂₁ L A B g₁Γ g₁Λ d₁Δ d₁Θ
  have cover₂₂ : ∀ F, F ∈ g₂Λ ++ d₂Θ → ∃ G ∈ (g₂Γ ++ g₂Λ) ++ (d₂Δ ++ d₂Θ), FormulaCover F G := by
    exact interpolation_exists_implLeft_left_cover₂₂ L g₂Γ g₂Λ d₂Δ d₂Θ
  have lift₁₁ := listFormulaCover cover₁₁
  have lift₁₂ := listFormulaCover cover₁₂
  have lift₂₁ := listFormulaCover cover₂₁
  have lift₂₂ := listFormulaCover cover₂₂
  refine ⟨.disj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨lift₁₁.1 P hi.1, lift₁₂.1 P hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨lift₂₁.1 P hi.1, lift₂₂.1 P hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨lift₁₁.2.1 c hi.1, lift₁₂.2.1 c hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨lift₂₁.2.1 c hi.1, lift₂₂.2.1 c hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨lift₁₁.2.2.1 v hi.1, lift₁₂.2.2.1 v hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨lift₂₁.2.2.1 v hi.1, lift₂₂.2.2.1 v hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := .impl A B :: (g₁Γ ++ g₁Λ)
                  delta1 := d₁Δ ++ d₁Θ
                  gamma2 := g₂Γ ++ g₂Λ
                  delta2 := d₂Δ ++ d₂Θ
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) lift₁₁.2.2.2 lift₁₂.2.2.2 h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := .impl A B :: (g₁Γ ++ g₁Λ)
                  delta1 := d₁Δ ++ d₁Θ
                  gamma2 := g₂Γ ++ g₂Λ
                  delta2 := d₂Δ ++ d₂Θ
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) lift₂₁.2.2.2 lift₂₂.2.2.2 h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_memTo (L : Language) (A B : FormulaN L)
    (g₂Γ g₂Λ : List (FormulaN L))
    (C₁ C₂ : FormulaN L)
    : ∀ (F : FormulaN L), F ∈ C₁ :: C₂ :: A.impl B :: (g₂Γ ++ g₂Λ) → F ∈ A.impl B :: (C₁ :: g₂Γ ++ C₂ :: g₂Λ) := by
  classical
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact List.Mem.tail _ (List.mem_append.mpr <| Or.inl (List.Mem.head _))
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact List.Mem.tail _ (List.mem_append.mpr <| Or.inr (List.Mem.head _))
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact List.Mem.head _
      · rcases List.mem_append.mp hF with hF | hF
        · exact List.Mem.tail _ (List.mem_append.mpr <| Or.inl (List.Mem.tail _ hF))
        · exact List.Mem.tail _ (List.mem_append.mpr <| Or.inr (List.Mem.tail _ hF))

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_memFrom (L : Language) (A B : FormulaN L)
    (g₂Γ g₂Λ : List (FormulaN L))
    (C₁ C₂ : FormulaN L)
    : ∀ (F : FormulaN L), F ∈ A.impl B :: (C₁ :: g₂Γ ++ C₂ :: g₂Λ) → F ∈ C₁ :: C₂ :: A.impl B :: (g₂Γ ++ g₂Λ) := by
  classical
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · rcases List.mem_append.mp hF with hF | hF
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.tail _ <| List.Mem.tail _ (List.mem_append.mpr (Or.inl hF)))
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.tail _ (List.Mem.tail _ <| List.Mem.tail _ (List.mem_append.mpr (Or.inr hF)))

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_cover₁₁ (L : Language)
    (g₁Γ g₁Λ d₁Δ d₁Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₁Γ ++ d₁Δ → ∃ G, G ∈ g₁Γ ++ g₁Λ ++ (d₁Δ ++ d₁Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_cover₁₂ (L : Language) (A B : FormulaN L)
    (g₂Γ g₂Λ d₂Δ d₂Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₂Γ ++ (d₂Δ ++ [A]) → ∃ G, G ∈ A.impl B :: (g₂Γ ++ g₂Λ) ++ (d₂Δ ++ d₂Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.Mem.tail _ (List.mem_append.mpr (Or.inl hF))),
      FormulaCover.refl F⟩
  · rcases List.mem_append.mp hF with hF | hF
    · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inl hF)), FormulaCover.refl F⟩
    · have hFA : F = A := by simpa using hF
      subst F
      exact ⟨.impl A B, List.mem_append.mpr (Or.inl (List.Mem.head _)), FormulaCover.impl_left A B⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_cover₂₁ (L : Language)
    (g₁Γ g₁Λ d₁Δ d₁Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ g₁Λ ++ d₁Θ → ∃ G, G ∈ g₁Γ ++ g₁Λ ++ (d₁Δ ++ d₁Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · exact ⟨F, List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right_cover₂₂ (L : Language) (A B : FormulaN L)
    (g₂Γ g₂Λ d₂Δ d₂Θ : List (FormulaN L))
    : ∀ (F : FormulaN L), F ∈ B :: g₂Λ ++ d₂Θ → ∃ G, G ∈ A.impl B :: (g₂Γ ++ g₂Λ) ++ (d₂Δ ++ d₂Θ) ∧ FormulaCover F G := by
  classical
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_cons.mp hF with hF | hF
    · subst F
      exact ⟨.impl A B, List.mem_append.mpr (Or.inl (List.Mem.head _)), FormulaCover.impl_right A B⟩
    · exact ⟨F, List.mem_append.mpr (Or.inl <| List.Mem.tail _ (List.mem_append.mpr (Or.inr hF))),
        FormulaCover.refl F⟩
  · exact ⟨F, List.mem_append.mpr (Or.inr <| List.mem_append.mpr (Or.inr hF)), FormulaCover.refl F⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft_right (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ Λ Θ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Λ, succedent := Θ }), ∃ C, IsInterpolant botP hBotArity p C)
    (g₁ d₁ d₂ : List (FormulaN L))
    (hd : List.Interleaving d₁ d₂ (Δ ++ Θ))
    (g₂' : List (FormulaN L))
    (hg' : List.Interleaving g₁ g₂' (Γ.append Λ))
    (hg : List.Interleaving g₁ (A.impl B :: g₂') (A.impl B :: Γ ++ Λ))
    : ∃ C, IsInterpolant botP hBotArity (s := Sequent.mk (A.impl B :: Γ ++ Λ) (Δ ++ Θ))
          { gamma1 := g₁, delta1 := d₁, gamma2 := A.impl B :: g₂', delta2 := d₂, gamma_partition := hg,
            delta_partition := hd }
          C := by
  classical
  obtain ⟨g₁Γ, g₁Λ, g₂Γ, g₂Λ, rfl, rfl, hgΓ, hgΛ⟩ := hg'.append_split
  obtain ⟨d₁Δ, d₁Θ, d₂Δ, d₂Θ, rfl, rfl, hdΔ, hdΘ⟩ := hd.append_split
  let q₁ : SequentPartition (Sequent.mk Γ (Δ ++ [A])) := ⟨g₁Γ, d₁Δ, g₂Γ, d₂Δ ++ [A],
      hgΓ, hdΔ.append_right [A]⟩
  let q₂ : SequentPartition (Sequent.mk (B :: Λ) Θ) := ⟨g₁Λ, d₁Θ, B :: g₂Λ, d₂Θ, .right B hgΛ, hdΘ⟩
  obtain ⟨C₁, hI₁⟩ := ih₁ q₁
  obtain ⟨C₂, hI₂⟩ := ih₂ q₂
  dsimp [q₁] at hI₁
  dsimp [q₂] at hI₂
  have hLeft₁ : lkBotProvable botP hBotArity ⟨g₁Γ ++ g₁Λ, (d₁Δ ++ d₁Θ) ++ [C₁]⟩ := lkBot_weaken_to
      g₁Γ (d₁Δ ++ [C₁])
      (g₁Γ ++ g₁Λ) ((d₁Δ ++ d₁Θ) ++ [C₁])
      (by
        intro F hF
        exact List.mem_append.mpr (Or.inl hF))
      (by
        intro F hF
        rcases List.mem_append.mp hF with hF | hF
        · exact List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inl hF))
        · exact List.mem_append.mpr (Or.inr hF))
      hI₁.left_provable
  have hLeft₂ : lkBotProvable botP hBotArity ⟨g₁Γ ++ g₁Λ, (d₁Δ ++ d₁Θ) ++ [C₂]⟩ := lkBot_weaken_to
      g₁Λ (d₁Θ ++ [C₂])
      (g₁Γ ++ g₁Λ) ((d₁Δ ++ d₁Θ) ++ [C₂])
      (by
        intro F hF
        exact List.mem_append.mpr (Or.inr hF))
      (by
        intro F hF
        rcases List.mem_append.mp hF with hF | hF
        · exact List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inr hF))
        · exact List.mem_append.mpr (Or.inr hF))
      hI₂.left_provable
  have hLeft : lkBotProvable botP hBotArity ⟨g₁Γ ++ g₁Λ, (d₁Δ ++ d₁Θ) ++ [.conj C₁ C₂]⟩ := lkBot_twoPremise
      (.andRight C₁ C₂ (g₁Γ ++ g₁Λ) (d₁Δ ++ d₁Θ))
      hLeft₁ hLeft₂
  have hPrem₂ := lkBot_exchangeLeft_at [] C₂ B g₂Λ d₂Θ (by simpa using hI₂.right_provable)
  have hRight₀ := lkBot_twoPremise (.implLeft A B (C₁ :: g₂Γ) d₂Δ (C₂ :: g₂Λ) d₂Θ)
    hI₁.right_provable (by simpa using hPrem₂)
  have memTo : ∀ F, F ∈ C₁ :: C₂ :: .impl A B :: (g₂Γ ++ g₂Λ) →
      F ∈ .impl A B :: ((C₁ :: g₂Γ) ++ (C₂ :: g₂Λ)) := by
    exact interpolation_exists_implLeft_right_memTo L A B g₂Γ g₂Λ C₁ C₂
  have memFrom : ∀ F, F ∈ .impl A B :: ((C₁ :: g₂Γ) ++ (C₂ :: g₂Λ)) →
      F ∈ C₁ :: C₂ :: .impl A B :: (g₂Γ ++ g₂Λ) := by
    exact interpolation_exists_implLeft_right_memFrom L A B g₂Γ g₂Λ C₁ C₂
  have hRight₁ : lkBotProvable botP hBotArity ⟨C₁ :: C₂ :: .impl A B :: (g₂Γ ++ g₂Λ), d₂Δ ++ d₂Θ⟩ :=
    lkBot_mem_equiv_antecedent (.impl A B :: ((C₁ :: g₂Γ) ++ (C₂ :: g₂Λ)))
      (C₁ :: C₂ :: .impl A B :: (g₂Γ ++ g₂Λ))
      (d₂Δ ++ d₂Θ) memTo memFrom
      (by simpa [List.append_assoc] using hRight₀)
  have hRight : lkBotProvable botP hBotArity ⟨[.conj C₁ C₂] ++ (.impl A B :: (g₂Γ ++ g₂Λ)), d₂Δ ++ d₂Θ⟩ :=
    lkBot_conjLeft_both C₁ C₂ (.impl A B :: (g₂Γ ++ g₂Λ)) (d₂Δ ++ d₂Θ) hRight₁
  have cover₁₁ : ∀ F, F ∈ g₁Γ ++ d₁Δ → ∃ G ∈ (g₁Γ ++ g₁Λ) ++ (d₁Δ ++ d₁Θ), FormulaCover F G := by
    exact interpolation_exists_implLeft_right_cover₁₁ L g₁Γ g₁Λ d₁Δ d₁Θ
  have cover₁₂ : ∀ F, F ∈ g₂Γ ++ (d₂Δ ++ [A]) → ∃ G ∈ (.impl A B :: (g₂Γ ++ g₂Λ)) ++ (d₂Δ ++ d₂Θ),
        FormulaCover F G := by
    exact interpolation_exists_implLeft_right_cover₁₂ L A B g₂Γ g₂Λ d₂Δ d₂Θ
  have cover₂₁ : ∀ F, F ∈ g₁Λ ++ d₁Θ → ∃ G ∈ (g₁Γ ++ g₁Λ) ++ (d₁Δ ++ d₁Θ), FormulaCover F G := by
    exact interpolation_exists_implLeft_right_cover₂₁ L g₁Γ g₁Λ d₁Δ d₁Θ
  have cover₂₂ : ∀ F, F ∈ (B :: g₂Λ) ++ d₂Θ → ∃ G ∈ (.impl A B :: (g₂Γ ++ g₂Λ)) ++ (d₂Δ ++ d₂Θ),
        FormulaCover F G := by
    exact interpolation_exists_implLeft_right_cover₂₂ L A B g₂Γ g₂Λ d₂Δ d₂Θ
  have lift₁₁ := listFormulaCover cover₁₁
  have lift₁₂ := listFormulaCover cover₁₂
  have lift₂₁ := listFormulaCover cover₂₁
  have lift₂₂ := listFormulaCover cover₂₂
  refine ⟨.conj C₁ C₂, ?_⟩
  refine
    { left_provable := hLeft
      right_provable := hRight
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    rcases hP with hP | hP
    · have hi := hI₁.pred_common P hP hne
      exact ⟨lift₁₁.1 P hi.1, lift₁₂.1 P hi.2⟩
    · have hi := hI₂.pred_common P hP hne
      exact ⟨lift₂₁.1 P hi.1, lift₂₂.1 P hi.2⟩
  · intro c hc
    rcases hc with hc | hc
    · have hi := hI₁.const_common c hc
      exact ⟨lift₁₁.2.1 c hi.1, lift₁₂.2.1 c hi.2⟩
    · have hi := hI₂.const_common c hc
      exact ⟨lift₂₁.2.1 c hi.1, lift₂₂.2.1 c hi.2⟩
  · intro v hv
    rcases hv with hv | hv
    · have hi := hI₁.fv_common v hv
      exact ⟨lift₁₁.2.2.1 v hi.1, lift₁₂.2.2.1 v hi.2⟩
    · have hi := hI₂.fv_common v hv
      exact ⟨lift₂₁.2.2.1 v hi.1, lift₂₂.2.2.1 v hi.2⟩
  · intro h
    exact ⟨hI₁.no_eq (allNoEq_rel
          (p := { gamma1 := g₁Γ ++ g₁Λ
                  delta1 := d₁Δ ++ d₁Θ
                  gamma2 := .impl A B :: (g₂Γ ++ g₂Λ)
                  delta2 := d₂Δ ++ d₂Θ
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₁) lift₁₁.2.2.2 lift₁₂.2.2.2 h),
        hI₂.no_eq (allNoEq_rel
          (p := { gamma1 := g₁Γ ++ g₁Λ
                  delta1 := d₁Δ ++ d₁Θ
                  gamma2 := .impl A B :: (g₂Γ ++ g₂Λ)
                  delta2 := d₂Δ ++ d₂Θ
                  gamma_partition := hg
                  delta_partition := hd })
          (q := q₂) lift₂₁.2.2.2 lift₂₂.2.2.2 h)⟩

-- ATTACH-BLOCKER: private declaration
theorem interpolation_exists_implLeft (L : Language) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0)
    (A B : FormulaN L)
    (Γ Δ Λ Θ : List (FormulaN L))
    (ih₁ : ∀ (p : SequentPartition { antecedent := Γ, succedent := Δ ++ [A] }), ∃ C, IsInterpolant botP hBotArity p C)
    (ih₂ : ∀ (p : SequentPartition { antecedent := B :: Λ, succedent := Θ }), ∃ C, IsInterpolant botP hBotArity p C)
    (p : SequentPartition { antecedent := A.impl B :: Γ ++ Λ, succedent := Δ ++ Θ })
    : ∃ C, IsInterpolant botP hBotArity p C := by
  classical
  rcases p with ⟨g₁, d₁, g₂, d₂, hg, hd⟩
  rcases hg.cons_inv with
    ⟨g₁', rfl, hg'⟩ | ⟨g₂', rfl, hg'⟩
  · exact interpolation_exists_implLeft_left L botP hBotArity A B Γ Δ Λ Θ (ih₁) (ih₂) d₁ g₂ d₂ hd g₁' hg' hg
  · exact interpolation_exists_implLeft_right L botP hBotArity A B Γ Δ Λ Θ (ih₁) (ih₂) g₁ d₁ d₂ hd g₂' hg' hg

end LCS.CutElim.Interpolation
end
