import LCS.CutElim.Interpolation.Craig

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

proof_of craig_interpolant_common_pred_exists := by
  let s : Sequent L := { antecedent := [A], succedent := [B] }
  let sFresh : Sequent (CraigFreshBot.FreshBotLanguage L) :=
    CraigFreshBot.freshLiftSequent s
  let p : SequentPartition sFresh :=
    { gamma1 := [CraigFreshBot.freshLiftFormula A]
      delta1 := []
      gamma2 := []
      delta2 := [CraigFreshBot.freshLiftFormula B]
      gamma_partition := by
        exact .left _ .nil
      delta_partition := by
        exact .right _ .nil }
  have hLift : folkProvable sFresh := by
    rcases hProv with ⟨t⟩
    exact ⟨CraigFreshBot.freshLift_folkProofTree t⟩
  obtain ⟨C₀, hC₀⟩ := interpolation_key_lemma_lk
    ((CraigFreshBot.freshLanguage_withoutEquality).mpr hNoEq)
    CraigFreshBot.freshBot CraigFreshBot.freshBot_arity sFresh hLift p
  rcases
      CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
        P hC₀.left_provable hC₀.right_provable with
    ⟨v, hLeft, hRight⟩
  let C : FormulaN L :=
    CraigFreshBot.freshLowerFormula
      (CraigFreshBot.sharedPredFalse P v) C₀
  refine ⟨C, ?_⟩
  refine
    { left_provable := ?_
      right_provable := ?_
      pred_common := ?_
      const_common := ?_
      fv_common := ?_ }
  · simpa only [C, p, CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil,
      CraigFreshBot.freshLowerFormula_lift] using hLeft
  · simpa only [C, p, CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil,
      CraigFreshBot.freshLowerFormula_lift] using hRight
  · intro Q hQ
    rcases
        (CraigFreshBot.freshLowerFormula_sharedPredFalse_predSymbols
          P Q v C₀).mp hQ with
      hOld | ⟨hBot, hQP⟩
    · have hCommon := hC₀.pred_common (.inl Q) hOld
          (by
            intro h
            cases h)
      constructor
      · have hA := hCommon.1
        change
          ∃ F ∈ [CraigFreshBot.freshLiftFormula A],
            formulaPredSymbolsN F (.inl Q) at hA
        rcases hA with ⟨F, hF, hFQ⟩
        have hFA : F = CraigFreshBot.freshLiftFormula A :=
          List.mem_singleton.mp hF
        subst F
        exact
          (CraigFreshBot.freshLiftFormula_predSymbols_inl A Q).mp hFQ
      · have hB := hCommon.2
        change
          ∃ F ∈ [CraigFreshBot.freshLiftFormula B],
            formulaPredSymbolsN F (.inl Q) at hB
        rcases hB with ⟨F, hF, hFQ⟩
        have hFB : F = CraigFreshBot.freshLiftFormula B :=
          List.mem_singleton.mp hF
        subst F
        exact
          (CraigFreshBot.freshLiftFormula_predSymbols_inl B Q).mp hFQ
    · subst Q
      exact ⟨hPA, hPB⟩
  · intro c hc
    have hOld :
        formulaConstSymbolsN C₀ c :=
      CraigFreshBot.freshLowerFormula_sharedPredFalse_constSymbols
        P v C₀ c hc
    have hCommon := hC₀.const_common c hOld
    constructor
    · simpa only [p, listFormulaConstSymbols, List.append_nil,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_constSymbols] using hCommon.1
    · simpa only [p, listFormulaConstSymbols, List.nil_append,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_constSymbols] using hCommon.2
  · intro x hx
    have hOld : formulaFVN C₀ x :=
      CraigFreshBot.freshLowerFormula_sharedPredFalse_fv P v C₀ x hx
    have hCommon := hC₀.fv_common x hOld
    constructor
    · simpa only [p, listFormulaFV, List.append_nil,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_fv] using hCommon.1
    · simpa only [p, listFormulaFV, List.nil_append,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_fv] using hCommon.2


proof_of craig_interpolation_no_common_pred := by
  have hANoEq : formulaNoEq A :=
    validBridgeFormulaNoEq_of_false hNoEq A
  have hBNoEq : formulaNoEq B :=
    validBridgeFormulaNoEq_of_false hNoEq B
  have hPredNonempty : Nonempty L.predSymbols :=
    Classical.byContradiction fun hEmpty =>
      formula_empty_pred_no_base hEmpty A hANoEq
  rcases hPredNonempty with ⟨P⟩
  let s : Sequent L := { antecedent := [A], succedent := [B] }
  let sFresh : Sequent (CraigFreshBot.FreshBotLanguage L) :=
    CraigFreshBot.freshLiftSequent s
  let p : SequentPartition sFresh :=
    { gamma1 := [CraigFreshBot.freshLiftFormula A]
      delta1 := []
      gamma2 := []
      delta2 := [CraigFreshBot.freshLiftFormula B]
      gamma_partition := by
        exact .left _ .nil
      delta_partition := by
        exact .right _ .nil }
  have hLift : folkProvable sFresh := by
    rcases hProv with ⟨t⟩
    exact ⟨CraigFreshBot.freshLift_folkProofTree t⟩
  obtain ⟨C, hC⟩ := interpolation_key_lemma_lk
    ((CraigFreshBot.freshLanguage_withoutEquality).mpr hNoEq)
    CraigFreshBot.freshBot CraigFreshBot.freshBot_arity sFresh hLift p
  have hOnlyBot :
      ∀ Q : (CraigFreshBot.FreshBotLanguage L).predSymbols,
        formulaPredSymbolsN C Q → Q = CraigFreshBot.freshBot := by
    intro Q hQ
    cases Q with
    | inl Q =>
        have hCommon := hC.pred_common (.inl Q) hQ
          (by
            intro h
            cases h)
        have hQA : formulaPredSymbolsN A Q := by
          have hLeft := hCommon.1
          change
            ∃ F ∈ [CraigFreshBot.freshLiftFormula A],
              formulaPredSymbolsN F (.inl Q) at hLeft
          rcases hLeft with ⟨F, hF, hFQ⟩
          have hFA : F = CraigFreshBot.freshLiftFormula A :=
            List.mem_singleton.mp hF
          subst F
          exact
            (CraigFreshBot.freshLiftFormula_predSymbols_inl A Q).mp hFQ
        have hQB : formulaPredSymbolsN B Q := by
          have hRight := hCommon.2
          change
            ∃ F ∈ [CraigFreshBot.freshLiftFormula B],
              formulaPredSymbolsN F (.inl Q) at hRight
          rcases hRight with ⟨F, hF, hFQ⟩
          have hFB : F = CraigFreshBot.freshLiftFormula B :=
            List.mem_singleton.mp hF
          subst F
          exact
            (CraigFreshBot.freshLiftFormula_predSymbols_inl B Q).mp hFQ
        exact (hNoPred Q ⟨hQA, hQB⟩).elim
    | inr u =>
        cases u
        rfl
  have hCNoEq : formulaNoEq C := by
    apply hC.no_eq
    intro F hF
    change
      F ∈ [CraigFreshBot.freshLiftFormula A,
        CraigFreshBot.freshLiftFormula B] at hF
    have hCases :
        F = CraigFreshBot.freshLiftFormula A ∨
          F = CraigFreshBot.freshLiftFormula B := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hF
    rcases hCases with hFA | hFB
    · subst F
      exact (CraigFreshBot.freshLiftFormula_noEq A).mpr hANoEq
    · subst F
      exact (CraigFreshBot.freshLiftFormula_noEq B).mpr hBNoEq
  rcases botFormula_lkBotProvable_or_lkBotRefutable C hOnlyBot hCNoEq with
    hCProv | hCRef
  · have hRight :=
      lkBot_twoPremise
        (.cut C [] [] [] [CraigFreshBot.freshLiftFormula B])
        hCProv hC.right_provable
    rcases
        CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
          P hRight hRight with
      ⟨v, hLower, _⟩
    right
    simpa only [CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append,
      CraigFreshBot.freshLowerFormula_lift] using hLower
  · have hLeft :=
      lkBot_twoPremise
        (.cut C [CraigFreshBot.freshLiftFormula A] [] [] [])
        hC.left_provable hCRef
    rcases
        CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
          P hLeft hLeft with
      ⟨v, hLower, _⟩
    left
    simpa only [CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append,
      CraigFreshBot.freshLowerFormula_lift] using hLower


end LCS.CutElim.Interpolation

end
