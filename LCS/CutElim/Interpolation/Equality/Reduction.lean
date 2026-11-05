import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.Axioms
import LCS.CutElim.Interpolation.Equality.Support
import LCS.CutElim.Interpolation.Equality.Replay
import Attach
import LCS.CutElim.Interpolation.Equality.Reduction.ProofsStamp

section
namespace LCS.CutElim.Interpolation.Equality
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
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka



-- ===================================================================
-- Lemma 6.5.4 (companion theorem): bot_equiv_neg_refl_lke
-- ===================================================================



-- ===================================================================
-- Helper: FOLKBot soundness under restricted bot-false semantics
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Restricted validity for sequents in `LK_bot`: the conclusion must hold
in every structure in which the distinguished nullary predicate representing
falsum is interpreted as false.  The transport along `hBotArity` makes the
unique empty tuple of arguments explicit. -/
def sequentValidWithBotFalse {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) : Prop :=
  ∀ (M : Structure L),
    (¬ M.interpPred botP
      (hBotArity ▸ (Fin.elim0 : Fin 0 → M.carrier))) →
    ∀ (σ : Assignment M),
      (∀ A ∈ s.antecedent, formulaEvalN M A σ) →
      (∃ B, B ∈ s.succedent ∧ formulaEvalN M B σ)

-- The restricted class of structures is nonempty: interpreting every
-- predicate as false supplies a concrete member for every language.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0) :
    ∃ M : Structure L,
      ¬ M.interpPred botP
        (hBotArity ▸ (Fin.elim0 : Fin 0 → M.carrier)) := by
  let M : Structure L :=
    { carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => False }
  exact ⟨M, by simp [M]⟩

-- The `LK_bot` axiom is valid under the restricted semantics.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0) :
    sequentValidWithBotFalse botP hBotArity
      (Sequent.mk [botFormula botP hBotArity] []) := by
  intro M hBotFalse σ hAnte
  have hBotTrue := hAnte (botFormula botP hBotArity) (List.Mem.head _)
  apply False.elim
  apply hBotFalse
  simp only [botFormula, formulaEvalN] at hBotTrue
  have hArgs :
      (fun i => termEval M σ
        ((hBotArity ▸ (Fin.elim0 : Fin 0 → Term L)) i)) =
      (hBotArity ▸ (Fin.elim0 : Fin 0 → M.carrier)) := by
    funext i
    exact Fin.elim0 (hBotArity ▸ i)
  rw [← hArgs]
  exact hBotTrue

-- In ordinary semantics the same sequent is not valid, because a structure
-- may interpret the distinguished nullary predicate as true.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0) :
    ¬ sequentValid (Sequent.mk [botFormula botP hBotArity] []) := by
  intro hValid
  let M : Structure L :=
    { carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => True }
  have hAnte :
      ∀ A ∈ [botFormula botP hBotArity],
        formulaEvalN M A (fun _ => ()) := by
    intro A hA
    simp only [List.mem_singleton] at hA
    subst A
    simp [botFormula, formulaEvalN, M]
  obtain ⟨B, hB, _⟩ := hValid M (fun _ => ()) hAnte
  simp at hB

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Soundness of FOLKBot proof trees: every well-formed FOLKBot proof
tree has a valid conclusion in every structure interpreting `botP`
as false. -/
theorem folkBotProofTree_valid {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s) :
    sequentValidWithBotFalse botP hBotArity s := by
  intro M hBotFalse
  induction t with
  | axiom_ s hax =>
    rcases hax with hax | ⟨hAnt, _hSucc⟩
    · exact lemma_6_2_1_axioms_valid s hax M
    · intro val hAll
      have hBotTrue :=
        hAll (botFormula botP hBotArity) (by
          rw [hAnt]
          exact List.Mem.head _)
      apply False.elim
      apply hBotFalse
      simp only [botFormula, formulaEvalN] at hBotTrue
      have hArgs :
          (fun i => termEval M val
            ((hBotArity ▸ (Fin.elim0 : Fin 0 → Term L)) i)) =
          (hBotArity ▸ (Fin.elim0 : Fin 0 → M.carrier)) := by
        funext i
        exact Fin.elim0 (hBotArity ▸ i)
      rw [← hArgs]
      exact hBotTrue
  | onePremise rule _t ih =>
    cases rule with
    | weakenLeft A Γ Δ =>
      intro val hAll
      exact ih val (fun F hF => hAll F (List.Mem.tail _ hF))
    | weakenRight A Γ Δ =>
      intro val hAll
      obtain ⟨B, hBmem, hBtrue⟩ := ih val hAll
      exact ⟨B, List.mem_append_left _ hBmem, hBtrue⟩
    | contractLeft A Γ Δ =>
      intro val hAll
      apply ih val
      intro F hF
      have hF' : F ∈ (A :: A :: Γ) := hF
      match hF' with
      | .head _ => exact hAll F (List.Mem.head _)
      | .tail _ (.head _) => exact hAll F (List.Mem.head _)
      | .tail _ (.tail _ h) => exact hAll F (List.Mem.tail _ h)
    | contractRight A Γ Δ =>
      intro val hAll
      obtain ⟨B, hBmem, hBtrue⟩ := ih val hAll
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
      intro val hAll
      apply ih val
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
      intro val hAll
      obtain ⟨F, hFmem, hFtrue⟩ := ih val hAll
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
      intro val hAll
      apply ih val
      intro F hF
      have hF' : F ∈ (A :: Γ) := hF
      match hF' with
      | .head _ =>
        have hconj := hAll (FormulaN.conj F B) (List.Mem.head _)
        simp [formulaEvalN] at hconj
        exact hconj.1
      | .tail _ h => exact hAll F (List.Mem.tail _ h)
    | andLeftR A B Γ Δ' =>
      intro val hAll
      apply ih val
      intro F hF
      have hF' : F ∈ (B :: Γ) := hF
      match hF' with
      | .head _ =>
        have hconj := hAll (FormulaN.conj A F) (List.Mem.head _)
        simp [formulaEvalN] at hconj
        exact hconj.2
      | .tail _ h => exact hAll F (List.Mem.tail _ h)
    | orRightL A B Γ Δ' =>
      intro val hAll
      obtain ⟨F, hFmem, hFtrue⟩ := ih val hAll
      have hFmem' : F ∈ Δ' ++ [A] := hFmem
      rcases List.mem_append.mp hFmem' with hd | ha
      · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
      · match ha with
        | .head _ =>
          refine ⟨FormulaN.disj F B,
            List.mem_append_right _ (List.Mem.head _), ?_⟩
          simp [formulaEvalN]
          left
          exact hFtrue
        | .tail _ ha => exact (nomatch ha)
    | orRightR A B Γ Δ' =>
      intro val hAll
      obtain ⟨F, hFmem, hFtrue⟩ := ih val hAll
      have hFmem' : F ∈ Δ' ++ [B] := hFmem
      rcases List.mem_append.mp hFmem' with hd | ha
      · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
      · match ha with
        | .head _ =>
          refine ⟨FormulaN.disj A F,
            List.mem_append_right _ (List.Mem.head _), ?_⟩
          simp [formulaEvalN]
          right
          exact hFtrue
        | .tail _ ha => exact (nomatch ha)
    | implRight A B Γ Δ' =>
      intro val hAll
      by_cases hA : formulaEvalN M A val
      · obtain ⟨F, hFmem, hFtrue⟩ := ih val (fun G hG => by
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
            simp [formulaEvalN]
            intro
            exact hFtrue
          | .tail _ h => exact (nomatch h)
      · refine ⟨FormulaN.impl A B,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]
        intro hA'
        exact absurd hA' hA
    | negLeft A Γ Δ' =>
      intro val hAll
      have hneg := hAll (FormulaN.neg A) (List.Mem.head _)
      simp [formulaEvalN] at hneg
      have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
        hAll F (List.Mem.tail _ hF)
      obtain ⟨F, hFmem, hFtrue⟩ := ih val hΓ
      have hFmem' : F ∈ Δ' ++ [A] := hFmem
      rcases List.mem_append.mp hFmem' with h | h
      · exact ⟨F, h, hFtrue⟩
      · match h with
        | .head _ => exact absurd hFtrue hneg
        | .tail _ h => exact (nomatch h)
    | negRight A Γ Δ' =>
      intro val hAll
      by_cases hA : formulaEvalN M A val
      · obtain ⟨F, hFmem, hFtrue⟩ := ih val (fun G hG => by
          have hG' : G ∈ (A :: Γ) := hG
          match hG' with
          | .head _ => exact hA
          | .tail _ h => exact hAll G h)
        exact ⟨F, List.mem_append_left _ hFmem, hFtrue⟩
      · refine ⟨FormulaN.neg A,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]
        exact hA
    | allLeft t_sub x A Γ Δ' hfree =>
      intro val hAll
      apply ih val
      intro F hF
      have hF' : F ∈
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN A t_sub x :: Γ) := hF
      cases hF' with
      | head =>
        have hall := hAll (FormulaN.all x A) (List.Mem.head _)
        simp [formulaEvalN] at hall
        exact
          (LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN
            val A t_sub x hfree).mpr
          (hall (termEval M val t_sub))
      | tail _ h => exact hAll F (List.Mem.tail _ h)
    | allRight y_eig x A Γ Δ' hfresh hfreeFor =>
      intro val hAll
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
              simp [assignUpdate]
              intro hzy
              exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
        obtain ⟨B, hBmem, hBtrue⟩ :=
          ih (assignUpdate val y_eig a) hantY
        have hBmem' :
            B ∈ Δ' ++
              [LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
                A (Term.var y_eig) x] := hBmem
        rcases List.mem_append.mp hBmem' with hBΔ | hBsub
        · have hBs : formulaEvalN M B val := by
            exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
              (fun y hy => by
                simp [assignUpdate]
                intro hzy
                exact absurd (hzy ▸ hy) (hfreshΔ B hBΔ))).mp hBtrue
          exact absurd ⟨B, hBΔ, hBs⟩ hΔ
        · have hBeq :
              B = LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
                A (Term.var y_eig) x := by
            cases hBsub with
            | head => rfl
            | tail _ h => exact (nomatch h)
          subst hBeq
          rw [LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN
              (assignUpdate val y_eig a) A (Term.var y_eig) x hfreeFor] at hBtrue
          simp [termEval, assignUpdate] at hBtrue
          have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
            intro z hz hzx hzy
            subst hzy
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
              · rename_i hzx
                split
                · rename_i hzy
                  exact absurd hzy (yA z hz hzx)
                · rfl)).mp hBtrue
    | exLeft y_eig x A Γ Δ' hfresh hfreeFor =>
      intro val hAll
      have hexA := hAll (FormulaN.ex x A) (List.Mem.head _)
      simp [formulaEvalN] at hexA
      obtain ⟨a, ha⟩ := hexA
      have hfreshΓ : ∀ F ∈ Γ, y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_left _ (List.Mem.tail _ hF))
      have hfreshΔ : ∀ F ∈ Δ', y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_right _ hF)
      have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
        intro z hz hzx hzy
        subst hzy
        exact hfresh (FormulaN.ex x A)
          (List.mem_append_left _ (List.Mem.head _))
          (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
      have hAyx : formulaEvalN M
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
            A (Term.var y_eig) x) (assignUpdate val y_eig a) := by
        rw [LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN
          (assignUpdate val y_eig a) A (Term.var y_eig) x hfreeFor]
        simp [termEval, assignUpdate]
        exact (coincidenceLemmaN M A (assignUpdate val x a)
          (fun k => if k = x then a
                    else if k = y_eig then a else val k)
          (fun z hz => by
            simp [assignUpdate]
            split
            · rfl
            · rename_i hzx
              split
              · rename_i hzy
                exact absurd hzy (yA z hz hzx)
              · rfl)).mp ha
      have hΓy : ∀ F ∈ Γ,
          formulaEvalN M F (assignUpdate val y_eig a) := fun F hF => by
        have hFs := hAll F (List.Mem.tail _ hF)
        exact (coincidenceLemmaN M F val (assignUpdate val y_eig a)
          (fun y hy => by
            simp [assignUpdate]
            intro hzy
            exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
      have hantY : ∀ F ∈
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
            A (Term.var y_eig) x :: Γ),
          formulaEvalN M F (assignUpdate val y_eig a) := by
        intro F hF
        cases hF with
        | head => exact hAyx
        | tail _ h => exact hΓy F h
      obtain ⟨B, hBmem, hBtrue⟩ :=
        ih (assignUpdate val y_eig a) hantY
      exact ⟨B, hBmem, by
        exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
          (fun y hy => by
            simp [assignUpdate]
            intro hzy
            exact absurd (hzy ▸ hy) (hfreshΔ B hBmem))).mp hBtrue⟩
    | exRight t_sub x A Γ Δ' hfree =>
      intro val hAll
      obtain ⟨F, hFmem, hFtrue⟩ := ih val hAll
      have hFmem' : F ∈ Δ' ++
          [LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN A t_sub x] := hFmem
      rcases List.mem_append.mp hFmem' with h | h
      · exact ⟨F, List.mem_append_left _ h, hFtrue⟩
      · have hFeq :
            F = LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN A t_sub x := by
          cases h with
          | head => rfl
          | tail _ h => exact (nomatch h)
        subst hFeq
        refine ⟨FormulaN.ex x A,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]
        exact ⟨termEval M val t_sub,
          (LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN
            val A t_sub x hfree).mp hFtrue⟩
  | twoPremise rule _t1 _t2 ih1 ih2 =>
    cases rule with
    | cut A Γ Δ' Λ Θ =>
      intro val hAll
      have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
        hAll F (List.mem_append_left _ hF)
      have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
        hAll F (List.mem_append_right _ hF)
      obtain ⟨B, hBmem, hBtrue⟩ := ih1 val hΓ
      have hBmem' : B ∈ Δ' ++ [A] := hBmem
      rcases List.mem_append.mp hBmem' with h | h
      · exact ⟨B, List.mem_append_left _ h, hBtrue⟩
      · match h with
        | .head _ =>
          obtain ⟨C, hCmem, hCtrue⟩ := ih2 val (fun F hF => by
            have hF' : F ∈ (B :: Λ) := hF
            match hF' with
            | .head _ => exact hBtrue
            | .tail _ h => exact hΛ F h)
          exact ⟨C, List.mem_append_right _ hCmem, hCtrue⟩
        | .tail _ h => exact (nomatch h)
    | andRight A B Γ Δ' =>
      intro val hAll
      obtain ⟨F1, hF1mem, hF1true⟩ := ih1 val hAll
      have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
      rcases List.mem_append.mp hF1mem' with h | h
      · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
      · match h with
        | .head _ =>
          obtain ⟨F2, hF2mem, hF2true⟩ := ih2 val hAll
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
      intro val hAll
      have hdisj := hAll (FormulaN.disj A B) (List.Mem.head _)
      simp [formulaEvalN] at hdisj
      have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
        hAll F (List.Mem.tail _ hF)
      cases hdisj with
      | inl hA =>
        apply ih1 val
        intro F hF
        have hF' : F ∈ (A :: Γ) := hF
        match hF' with
        | .head _ => exact hA
        | .tail _ h => exact hΓ F h
      | inr hB =>
        apply ih2 val
        intro F hF
        have hF' : F ∈ (B :: Γ) := hF
        match hF' with
        | .head _ => exact hB
        | .tail _ h => exact hΓ F h
    | implLeft A B Γ Δ' Λ Θ =>
      intro val hAll
      have himpl := hAll (FormulaN.impl A B) (List.Mem.head _)
      simp [formulaEvalN] at himpl
      have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
        hAll F (List.Mem.tail _ (List.mem_append_left _ hF))
      have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
        hAll F (List.Mem.tail _ (List.mem_append_right _ hF))
      obtain ⟨F1, hF1mem, hF1true⟩ := ih1 val hΓ
      have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
      rcases List.mem_append.mp hF1mem' with h | h
      · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
      · match h with
        | .head _ =>
          have hB := himpl hF1true
          obtain ⟨F2, hF2mem, hF2true⟩ := ih2 val (fun F hF => by
            have hF' : F ∈ (B :: Λ) := hF
            match hF' with
            | .head _ => exact hB
            | .tail _ h => exact hΛ F h)
          exact ⟨F2, List.mem_append_right _ hF2mem, hF2true⟩
        | .tail _ h => exact (nomatch h)

-- ===================================================================
-- Helper: restricted semantic validity of lkBotProvable
-- ===================================================================



-- ===================================================================
-- Helper: List.Interleaving.prepend_right
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Prepending a prefix to the second list in an interleaving:
if l1 interleave l2 = l, then l1 interleave (pfx ++ l2) = pfx ++ l. -/
theorem List.Interleaving.prepend_right {α : Type} (pfx : List α)
    {l1 l2 l : List α} (h : List.Interleaving l1 l2 l) :
    List.Interleaving l1 (pfx ++ l2) (pfx ++ l) := by
-- BEGIN PROOF
  induction pfx with
  | nil => exact h
  | cons a p ih => exact .right a ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Prepending a prefix to the first list in an interleaving:
if l1 interleave l2 = l, then (pfx ++ l1) interleave l2 = pfx ++ l. -/
theorem List.Interleaving.prepend_left {α : Type} (pfx : List α)
    {l1 l2 l : List α} (h : List.Interleaving l1 l2 l) :
    List.Interleaving (pfx ++ l1) l2 (pfx ++ l) := by
-- BEGIN PROOF
  induction pfx with
  | nil => exact h
  | cons a p ih => exact .left a ih

-- ===================================================================
-- Helper: formulaConstSymbolsN/formulaPredSymbolsN pass through quantifyAll
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaConstSymbolsN_quantifyAll {L : Language}
    (start count : Nat) (inner : FormulaN L) :
    formulaConstSymbolsN ((List.range count).foldr
      (fun i acc => FormulaN.all (start + i) acc) inner) =
    formulaConstSymbolsN inner := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => simp [List.range_zero]
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    exact ih (FormulaN.all (start + n) inner)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaPredSymbolsN_quantifyAll {L : Language}
    (start count : Nat) (inner : FormulaN L) :
    formulaPredSymbolsN ((List.range count).foldr
      (fun i acc => FormulaN.all (start + i) acc) inner) =
    formulaPredSymbolsN inner := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => simp [List.range_zero]
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    exact ih (FormulaN.all (start + n) inner)

-- ===================================================================
-- Helper: eqPairs have empty const/pred symbols
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem eqPairs_constSymbols_empty {L : Language} (hL : L.hasEquality = true) (n : Nat) :
    ∀ A ∈ (List.finRange n).map (fun (i : Fin n) =>
      FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (n + (i : Nat)))),
    formulaConstSymbolsN A = ∅ := by
-- BEGIN PROOF
  intro A hA; rw [List.mem_map] at hA; obtain ⟨i, _, rfl⟩ := hA
  simp only [formulaConstSymbolsN, termConstSymbols]
  ext c; simp [Set.union, Set.empty]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem eqPairs_predSymbols_empty {L : Language} (hL : L.hasEquality = true) (n : Nat) :
    ∀ A ∈ (List.finRange n).map (fun (i : Fin n) =>
      FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (n + (i : Nat)))),
    formulaPredSymbolsN A = ∅ := by
-- BEGIN PROOF
  intro A hA; rw [List.mem_map] at hA; obtain ⟨i, _, rfl⟩ := hA
  rfl

-- ===================================================================
-- Helper: right-nested conjunction preserves empty const/pred symbols
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem conjoin_constSymbols_empty {L : Language}
    (hd : FormulaN L) (tl : List (FormulaN L))
    (h : ∀ A ∈ hd :: tl, formulaConstSymbolsN A = ∅) :
    formulaConstSymbolsN (conjoinFormulae hd (hd :: tl)) = ∅ := by
  induction tl generalizing hd with
  | nil => exact h hd List.mem_cons_self
  | cons x xs ih =>
    rw [conjoin_cons_cons]
    simp only [formulaConstSymbolsN,
      h hd List.mem_cons_self,
      ih x (fun A hA => h A (List.mem_cons_of_mem hd hA))]
    ext v
    simp [Set.union, Set.empty]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem conjoin_predSymbols_empty {L : Language}
    (hd : FormulaN L) (tl : List (FormulaN L))
    (h : ∀ A ∈ hd :: tl, formulaPredSymbolsN A = ∅) :
    formulaPredSymbolsN (conjoinFormulae hd (hd :: tl)) = ∅ := by
  induction tl generalizing hd with
  | nil => exact h hd List.mem_cons_self
  | cons x xs ih =>
    rw [conjoin_cons_cons]
    simp only [formulaPredSymbolsN,
      h hd List.mem_cons_self,
      ih x (fun A hA => h A (List.mem_cons_of_mem hd hA))]
    ext v
    simp [Set.union, Set.empty]

-- ===================================================================
-- Helper: closedReflAxiom has empty const/pred symbols
-- ===================================================================









-- ===================================================================
-- Helper: closedFunCongAxiom has empty const/pred symbols
-- ===================================================================

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option maxHeartbeats 1600000 in
theorem closedFunCongAxiom_constSymbols_empty {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) :
    formulaConstSymbolsN (closedFunCongAxiom hL f) = ∅ := by
-- BEGIN PROOF
  unfold closedFunCongAxiom; simp only []
  rw [formulaConstSymbolsN_quantifyAll, formulaConstSymbolsN_quantifyAll]
  generalize hep : (List.finRange (L.funArity f)).map
    (fun (i : Fin (L.funArity f)) =>
      FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (L.funArity f + (i : Nat)))) = eqPairs
  cases eqPairs with
  | nil =>
    simp only [formulaConstSymbolsN, termConstSymbols]
    ext c; simp only [Set.union, Set.empty]; constructor
    · intro h; rcases h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact hi
    · exact False.elim
  | cons hd tl =>
    show formulaConstSymbolsN (FormulaN.impl _ _) = ∅
    simp only [formulaConstSymbolsN]
    have hAnte :
        formulaConstSymbolsN (conjoinFormulae hd (hd :: tl)) = ∅ := by
      apply conjoin_constSymbols_empty
      intro A hA
      exact eqPairs_constSymbols_empty hL _ A (hep ▸ hA)
    ext c; simp only [Set.union, Set.empty]; constructor
    · intro h; rcases h with hLeft | hRight
      · rw [hAnte] at hLeft; exact hLeft
      · simp only [termConstSymbols] at hRight
        rcases hRight with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact hi
    · exact False.elim

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option maxHeartbeats 1600000 in
theorem closedFunCongAxiom_predSymbols_empty {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) :
    formulaPredSymbolsN (closedFunCongAxiom hL f) = ∅ := by
-- BEGIN PROOF
  unfold closedFunCongAxiom; simp only []
  rw [formulaPredSymbolsN_quantifyAll, formulaPredSymbolsN_quantifyAll]
  generalize hep : (List.finRange (L.funArity f)).map
    (fun (i : Fin (L.funArity f)) =>
      FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (L.funArity f + (i : Nat)))) = eqPairs
  cases eqPairs with
  | nil => rfl
  | cons hd tl =>
    show formulaPredSymbolsN (FormulaN.impl _ _) = ∅
    simp only [formulaPredSymbolsN]
    have hAnte :
        formulaPredSymbolsN (conjoinFormulae hd (hd :: tl)) = ∅ := by
      apply conjoin_predSymbols_empty
      intro A hA
      exact eqPairs_predSymbols_empty hL _ A (hep ▸ hA)
    rw [hAnte]; ext; simp [Set.union, Set.empty]

-- ===================================================================
-- Helper: closedPredCongAxiom has empty const symbols
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem predN_ys_constSymbols_empty {L : Language}
    (P : L.predSymbols) :
    let n := L.predArity P
    formulaConstSymbolsN (FormulaN.predN P
      (fun (i : Fin n) => Term.var (n + (i : Nat)))) = ∅ := by
-- BEGIN PROOF
  intro n
  simp only [formulaConstSymbolsN, termConstSymbols]
  ext c; simp only [Set.empty]; constructor
  · intro ⟨i, hi⟩; exact hi
  · exact False.elim

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem premises_constSymbols_empty {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols) :
    let n := L.predArity P
    ∀ A ∈ (List.finRange n).map (fun (i : Fin n) =>
        FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
          (Term.var (n + (i : Nat)))) ++
      [FormulaN.predN P (fun (i : Fin n) => Term.var (i : Nat))],
    formulaConstSymbolsN A = ∅ := by
-- BEGIN PROOF
  intro n A hA
  rcases List.mem_append.mp hA with hEq | hPred
  · rw [List.mem_map] at hEq; obtain ⟨i, _, rfl⟩ := hEq
    simp only [formulaConstSymbolsN, termConstSymbols]
    ext c; simp [Set.union, Set.empty]
  · simp only [List.mem_singleton] at hPred; subst hPred
    simp only [formulaConstSymbolsN, termConstSymbols]
    ext c; simp only [Set.empty]; constructor
    · intro ⟨i, hi⟩; exact hi
    · exact False.elim

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option maxHeartbeats 1600000 in
theorem closedPredCongAxiom_constSymbols_empty {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols) :
    formulaConstSymbolsN (closedPredCongAxiom hL P) = ∅ := by
-- BEGIN PROOF
  unfold closedPredCongAxiom; simp only []
  rw [formulaConstSymbolsN_quantifyAll, formulaConstSymbolsN_quantifyAll]
  generalize hprem : (List.finRange (L.predArity P)).map
    (fun (i : Fin (L.predArity P)) =>
      FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (L.predArity P + (i : Nat)))) ++
    [FormulaN.predN P (fun (i : Fin (L.predArity P)) =>
      Term.var (i : Nat))] = premises
  cases premises with
  | nil => exact predN_ys_constSymbols_empty P
  | cons hd tl =>
    show formulaConstSymbolsN (FormulaN.impl _ _) = ∅
    simp only [formulaConstSymbolsN]
    have hAnte :
        formulaConstSymbolsN (conjoinFormulae hd (hd :: tl)) = ∅ := by
      apply conjoin_constSymbols_empty
      intro A hA
      exact premises_constSymbols_empty hL P A (hprem ▸ hA)
    ext c; simp only [Set.union, Set.empty]; constructor
    · intro h; rcases h with h | ⟨i, hi⟩
      · rw [hAnte] at h; exact h
      · simp only [termConstSymbols] at hi; exact hi
    · exact False.elim

-- ===================================================================
-- Helper: closedEqualityAxioms have empty const symbols
-- ===================================================================



-- ===================================================================
-- Helper: closedEqualityAxiomsForSide have empty const symbols
-- ===================================================================



-- ===================================================================
-- Helper: closedReflAxiom/closedFunCongAxiom have empty pred symbols
-- (closedPredCongAxiom P has pred symbols = {P})
-- ===================================================================







-- ===================================================================
-- Helper: bridge from sequentPredSymbolsList to listFormulaPredSymbols
-- ===================================================================





-- ===================================================================
-- Helper: closedEqualityAxiomsForSide formulas are universally valid
-- ===================================================================



-- ===================================================================
-- Helper: closedEqualityAxiomsForSide formulas are closed
-- ===================================================================



-- ===================================================================
-- Lemma 6.5.4 (companion def): interpolation_key_lemma_equality_partition
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 6.5.4 (required helper): Augments a partition `p` of a
sequent `s` by prepending the closed equality axioms `Se1` (for the
left side `Gamma_1 ∪ Delta_1`) and `Se2` (for the right side
`Gamma_2 ∪ Delta_2`) to their respective left/right gammas. This is
the partition used in the textbook reduction of Lem 6.5.4 to
Lem 6.5.2 via Lem 6.5.3. -/
noncomputable def interpolation_key_lemma_equality_partition {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {s : Sequent L} (p : SequentPartition s) :
    SequentPartition
      (Sequent.mk ((closedEqualityAxiomsForSide hL p.gamma1 p.delta1
                  ++ closedEqualityAxiomsForSide hL p.gamma2 p.delta2)
                ++ s.antecedent) s.succedent) :=
  let Se1 := closedEqualityAxiomsForSide hL p.gamma1 p.delta1
  let Se2 := closedEqualityAxiomsForSide hL p.gamma2 p.delta2
  { gamma1 := Se1 ++ p.gamma1
    gamma2 := Se2 ++ p.gamma2
    delta1 := p.delta1
    delta2 := p.delta2
    gamma_partition := by
      rw [show (Se1 ++ Se2) ++ s.antecedent =
        Se1 ++ (Se2 ++ s.antecedent) from List.append_assoc ..]
      exact List.Interleaving.prepend_left Se1
        (List.Interleaving.prepend_right Se2 p.gamma_partition)
    delta_partition := p.delta_partition }

-- ===================================================================
-- Lemma 6.5.4 (required helper): cut-free provability of augmented sequent
-- ===================================================================

/-- Lemma 6.5.4 (required helper): By Lemma 6.5.3, an LKe-provable
sequent `s = Gamma -> Delta` yields a cut-free LK-proof of the
augmented sequent `S_e, Gamma -> Delta` where `S_e` is the closed
equality axioms for `s`. This is the key reduction from LKe to LK
used in the proof of Lem 6.5.4. -/
theorem interpolation_key_lemma_equality_cutfree {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s) :
    folkCutFreeProvable
      (Sequent.mk ((closedEqualityAxiomsForSide hL p.gamma1 p.delta1
                  ++ closedEqualityAxiomsForSide hL p.gamma2 p.delta2)
                ++ s.antecedent) s.succedent) := by
-- BEGIN PROOF
  -- DEBT(Lemma 6.5.4 proof step: cut-free LK-proof of the sequent augmented with the closed equality axioms; proof pending)
  sorry

-- ===================================================================
-- Lemma 6.5.4: fixed-falsum construction under an explicit freshness guard
-- ===================================================================

-- ATTACH-BLOCKER: private declaration
/-- If `botP` is fresh in the root sequent, it is fresh on every side
of every partition of that sequent.  This is the regression boundary
needed by the fixed-falsum construction below. -/
private theorem botFresh_on_partition_sides {L : Language}
    {botP : L.predSymbols} {s : Sequent L} (p : SequentPartition s)
    (hBotFresh :
      ¬ listFormulaPredSymbols (s.antecedent ++ s.succedent) botP) :
    (¬ listFormulaPredSymbols p.gamma1 botP) ∧
    (¬ listFormulaPredSymbols p.delta1 botP) ∧
    (¬ listFormulaPredSymbols p.gamma2 botP) ∧
    (¬ listFormulaPredSymbols p.delta2 botP) := by
  have fresh_of_mem
      (fs : List (FormulaN L))
      (hMem : ∀ A, A ∈ fs → A ∈ s.antecedent ++ s.succedent) :
      ¬ listFormulaPredSymbols fs botP := by
    intro hOccurs
    obtain ⟨A, hA, hPred⟩ := hOccurs
    exact hBotFresh ⟨A, hMem A hA, hPred⟩
  refine ⟨fresh_of_mem p.gamma1 ?_, fresh_of_mem p.delta1 ?_,
    fresh_of_mem p.gamma2 ?_, fresh_of_mem p.delta2 ?_⟩
  · intro A hA
    exact List.mem_append_left _ (p.gamma_partition.mem_left hA)
  · intro A hA
    exact List.mem_append_right _ (p.delta_partition.mem_left hA)
  · intro A hA
    exact List.mem_append_left _ (p.gamma_partition.mem_right hA)
  · intro A hA
    exact List.mem_append_right _ (p.delta_partition.mem_right hA)

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Fixed-falsum construction used by the planned proof of Lemma 6.5.4.
Unlike the public textbook statement, this internal route must assume
that its designated nullary predicate is fresh in the original
sequent.  The replacement is closed, so the fixed bound-variable
index `0` introduces no free-variable capture. -/
noncomputable def interpolation_key_lemma_equality_witness_of_botFresh
    {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s)
    (hBotFresh :
      ¬ listFormulaPredSymbols (s.antecedent ++ s.succedent) botP) :
    FormulaN L := by
  have _ := botFresh_on_partition_sides p hBotFresh
  exact replaceBotByNegRefl hL botP hBotArity
    (interpolation_key_lemma_witness_cutFree
      (botP := botP) (hBotArity := hBotArity)
      _
      (interpolation_key_lemma_equality_cutfree hL s hProv p)
      (interpolation_key_lemma_equality_partition hL p))
    0

/-- The fixed-falsum construction yields LKₑ proofs of both interpolant
sequents under the explicit root-sequent freshness premise. -/
theorem interpolation_key_lemma_equality_witness_of_botFresh_spec
    {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s)
    (hBotFresh :
      ¬ listFormulaPredSymbols (s.antecedent ++ s.succedent) botP) :
    IsLKeInterpolant hL botP hBotArity p
      (interpolation_key_lemma_equality_witness_of_botFresh
        hL (hBotArity := hBotArity) s hProv p hBotFresh) :=
-- BEGIN PROOF
by
  -- REPAIR(T6-V2-08): proof pending
  sorry

-- ===================================================================
-- Lemma 6.5.4: public textbook statement and witness
-- ===================================================================

/-- Lemma 6.5.4 (interpolation key lemma with equality): every
partition of an LKₑ-provable sequent has an interpolant whose two
sequents are LKₑ-provable (OD-A18, D6-2 A).
The common-predicate condition exempts only equality (OD-A20).
The designated nullary predicate represents ⊥. Partitions are partitions
of formula occurrences. -/
@[attach_debt, blueprint "chap6__lemma_6_5_4" (main := true)]
theorem interpolation_key_lemma_equality {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s) :
    ∃ C : FormulaN L, IsLKeInterpolant hL botP hBotArity p C 





-- ===================================================================
-- Theorem 6.5.2 (required structure): IsLKeImplicationInterpolant
-- ===================================================================

/-- Theorem 6.5.2 (required): A formula C is an interpolant of an
implication A implies B in the LKe setting if: (1) A implies C is
LKe-provable (i.e., [A] -> [C] is LKe-provable), (2) C implies B
is LKe-provable (i.e., [C] -> [B] is LKe-provable), and (3) all
predicate symbols except equality, constant symbols, and free
variables in C occur in both A and B. -/
@[blueprint "chap6__theorem_6_5_2"]
structure IsLKeImplicationInterpolant {L : Language}
    (A B C : FormulaN L) : Prop where
  /-- A implies C is LKe-provable -/
  left_provable :
    lkeProvable { antecedent := [A], succedent := [C] }
  /-- C implies B is LKe-provable -/
  right_provable :
    lkeProvable { antecedent := [C], succedent := [B] }
  /-- All non-equality predicate symbols in C occur in both
      A and B -/
  pred_common_except_eq :
    formulaNonEqPredSymbols C ⊆
      formulaNonEqPredSymbols A ∩ formulaNonEqPredSymbols B
  /-- All constant symbols in C occur in both A and B -/
  const_common :
    formulaConstSymbolsN C ⊆
      formulaConstSymbolsN A ∩ formulaConstSymbolsN B
  /-- All free variables in C occur in both A and B -/
  fv_common :
    formulaFVN C ⊆ formulaFVN A ∩ formulaFVN B

-- ===================================================================
-- Theorem 6.5.2 (companion def): craig_interpolation_equality_partition
-- ===================================================================



-- ===================================================================
-- Theorem 6.5.2: public textbook statement and witness
-- ===================================================================

/-- Theorem 6.5.2 (Craig's interpolation theorem, with equality):
if `A ⊃ B` is LKe-provable, there is an interpolant `C` whose
non-equality predicate symbols, constants, and free variables occur
in both `A` and `B`. -/
@[attach_debt, blueprint "chap6__theorem_6_5_2" (main := true)]
theorem craig_interpolation_equality {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (A B : FormulaN L)
    (hProv : lkeProvable
      { antecedent := [A], succedent := [B] }) :
    ∃ C : FormulaN L, IsLKeImplicationInterpolant A B C 





-- ===================================================================
-- Remark after Theorem 6.5.2: strong interpolation with equality
-- ===================================================================

/-- Function symbols occurring in a formula, including function heads and
nested subterms in predicate and equality atoms. -/
@[blueprint "chap6__theorem_6_5_2"]
def formulaFunSymbolsSet {L : Language} (A : FormulaN L) : Set L.funSymbols :=
  formulaFunSymsN A

/-- Strong Craig interpolation with equality: if A → B is LKₑ-provable,
there is an interpolant C whose non-equality predicate symbols, function
symbols, constant symbols, and free variables occur in both A and B.
The constant-symbol condition is `IsLKeImplicationInterpolant.const_common`,
expressed using `formulaConstSymbolsN`. -/
@[attach_debt, blueprint "chap6__theorem_6_5_2"]
theorem craig_interpolation_equality_strong {L : Language}
    (hL : L.hasEquality = true) (A B : FormulaN L)
    (hProv : lkeProvable { antecedent := [A], succedent := [B] }) :
    ∃ C : FormulaN L, IsLKeImplicationInterpolant A B C ∧
      formulaFunSymbolsSet C ⊆ formulaFunSymbolsSet A ∩ formulaFunSymbolsSet B 

-- ===================================================================
-- Theorem 6.3.1 (companion): lkeProvableN_of_sequentValidN
-- ===================================================================



end LCS.CutElim.Interpolation.Equality
end

