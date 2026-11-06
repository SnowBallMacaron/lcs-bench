import LCS.Propositional.Systems.G.Search.Completeness
open LCS.Propositional.Systems.G.Search.FalsificationPropagation.Proofs
open LCS.Propositional.Systems.G.Search.Procedure.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem valid_atomic_is_axiom (s : Sequent)
    (hv : sequentValid s)
    (hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, ∃ n, A = .var n) :
    isAxiom s :=
-- BEGIN PROOF
  Classical.byContradiction fun hNotAxiom => by
    simp only [isAxiom, not_exists, not_and] at hNotAxiom
    let v : Valuation := fun n =>
      if PropFormulaNormalized.var n ∈ s.antecedent then BoolVal.T else BoolVal.F
    have hAntT : ∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T := by
      intro A hA
      obtain ⟨n, rfl⟩ := hAllVar A (List.mem_append.mpr (Or.inl hA))
      simp [evalExtN, v, hA]
    have hSuccF : ∀ B ∈ s.succedent, evalExtN v B = BoolVal.F := by
      intro B hB
      obtain ⟨n, rfl⟩ := hAllVar B (List.mem_append.mpr (Or.inr hB))
      simp [evalExtN, v]
      intro h; exact absurd hB (hNotAxiom _ h)
    obtain ⟨B, hBmem, hBtrue⟩ := hv v hAntT
    exact absurd hBtrue (by rw [hSuccF B hBmem]; decide)

helper theorem valid_atomic_provable (s : Sequent)
    (hv : sequentValid s)
    (hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, ∃ n, A = .var n) :
    sequentProvable s := by
-- BEGIN PROOF
  have hax := valid_atomic_is_axiom s hv hAllVar
  exact ⟨ProofTree.axiom_ s hax⟩

helper theorem list_split_s {a : PropFormulaNormalized} {L : List PropFormulaNormalized}
    (h : a ∈ L) : ∃ before after, L = before ++ [a] ++ after := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hxs
    · exact ⟨[], xs, rfl⟩
    · obtain ⟨b, a2, rfl⟩ := ih hxs; exact ⟨x :: b, a2, by simp⟩

helper theorem foldl_shift_s (n : Nat) (L : List Nat) :
    L.foldl (· + ·) n = n + L.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction L generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih x]; omega

helper theorem foldl_eq_sum_s (L : List Nat) : L.foldl (· + ·) 0 = L.sum := by
-- BEGIN PROOF
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.sum_cons]
    rw [foldl_shift_s]; omega

helper theorem sc_sum_s (s : Sequent) :
    sequentComplexity s = (s.antecedent.map formulaComplexity).sum +
                          (s.succedent.map formulaComplexity).sum := by
-- BEGIN PROOF
  simp only [sequentComplexity, foldl_eq_sum_s]

helper theorem sum_zero_s {f : α → Nat} {L : List α}
    (h : ∀ x ∈ L, f x = 0) : (L.map f).sum = 0 := by
-- BEGIN PROOF
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp [List.sum_cons, h x (List.Mem.head _),
          ih (fun y hy => h y (List.Mem.tail _ hy))]

helper theorem step1_backward_valid {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (hconc : sequentValid conc) :
    sequentValid prem := by
-- BEGIN PROOF
  cases rule with
  | andLeft Γ Δ Λ A B =>
    intro v hAnt
    apply hconc v
    intro X hX
    rcases mc_s hX with hΓ | rfl | hΔ
    · exact hAnt X (tl_s hΓ)
    · simp [evalExtN, hAnd, hAnt A tf_s, hAnt B ts_s]
    · exact hAnt X (tr_s hΔ)
  | orRight Γ Δ Λ A B =>
    intro v hAnt
    obtain ⟨X, hXm, hXt⟩ := hconc v hAnt
    rcases mc_s hXm with hΔ | rfl | hΛ
    · exact ⟨X, tl_s hΔ, hXt⟩
    · simp [evalExtN, hOr] at hXt
      cases ha : evalExtN v A with
      | T => exact ⟨A, tf_s, ha⟩
      | F =>
        cases hb : evalExtN v B with
        | T => exact ⟨B, ts_s, hb⟩
        | F => simp [ha, hb] at hXt
    · exact ⟨X, tr_s hΛ, hXt⟩
  | implRight Γ Δ Λ A B =>
    intro v hAnt
    obtain ⟨X, hXm, hXt⟩ := hconc v (fun X hX => hAnt X (List.Mem.tail _ hX))
    rcases mc_s hXm with hΔ | rfl | hΛ
    · exact ⟨X, List.Mem.tail _ (List.mem_append.mpr (Or.inl hΔ)), hXt⟩
    · simp [evalExtN, hImplies] at hXt
      cases hb : evalExtN v B with
      | T => exact ⟨B, List.Mem.head _, hb⟩
      | F => cases ha : evalExtN v A <;> simp_all
    · exact ⟨X, List.Mem.tail _ (List.mem_append.mpr (Or.inr hΛ)), hXt⟩
  | negLeft Γ Δ Λ A =>
    intro v hAnt
    cases ha : evalExtN v A with
    | T => exact ⟨A, List.Mem.head _, ha⟩
    | F =>
      have hN : evalExtN v (.neg A) = BoolVal.T := by simp [evalExtN, hNeg, ha]
      obtain ⟨X, hXm, hXt⟩ := hconc v (fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (List.mem_append.mpr (Or.inl hΓ))
        | Or.inr (Or.inl h) => h ▸ hN
        | Or.inr (Or.inr hΔ) => hAnt X (List.mem_append.mpr (Or.inr hΔ)))
      exact ⟨X, List.Mem.tail _ hXm, hXt⟩
  | negRight Γ Δ Λ A =>
    intro v hAnt
    obtain ⟨X, hXm, hXt⟩ := hconc v (fun X hX => hAnt X (List.Mem.tail _ hX))
    rcases mc_s hXm with hΔ | rfl | hΛ
    · exact ⟨X, List.mem_append.mpr (Or.inl hΔ), hXt⟩
    · simp [evalExtN, hNeg] at hXt; cases evalExtN v A <;> simp_all
    · exact ⟨X, List.mem_append.mpr (Or.inr hΛ), hXt⟩

helper theorem step2_backward_valid {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) (hconc : sequentValid conc) :
    sequentValid p1 ∧ sequentValid p2 := by
-- BEGIN PROOF
  cases rule with
  | andRight Γ Δ Λ A B =>
    constructor
    · intro v hAnt
      obtain ⟨X, hXm, hXt⟩ := hconc v hAnt
      rcases mc_s hXm with hΔ | rfl | hΛ
      · exact ⟨X, ml_s hΔ, hXt⟩
      · simp [evalExtN, hAnd] at hXt
        cases ha : evalExtN v A with
        | T => exact ⟨A, mm_s, ha⟩
        | F => simp [ha] at hXt
      · exact ⟨X, mr_s hΛ, hXt⟩
    · intro v hAnt
      obtain ⟨X, hXm, hXt⟩ := hconc v hAnt
      rcases mc_s hXm with hΔ | rfl | hΛ
      · exact ⟨X, ml_s hΔ, hXt⟩
      · simp [evalExtN, hAnd] at hXt
        cases hb : evalExtN v B with
        | T => exact ⟨B, mm_s, hb⟩
        | F => simp [hb] at hXt
      · exact ⟨X, mr_s hΛ, hXt⟩
  | orLeft Γ Δ Λ A B =>
    constructor
    · intro v hAnt
      exact hconc v (fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸
            (by simp [evalExtN, hOr, hAnt A (mm_s (Γ:=Γ) (Δ:=Δ))])
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ))
    · intro v hAnt
      exact hconc v (fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸ (by
            simp [evalExtN, hOr]
            cases evalExtN v A <;> simp [hAnt B (mm_s (Γ:=Γ) (Δ:=Δ))])
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ))
  | implLeft Γ Δ Λ A B =>
    constructor
    · intro v hAnt
      cases ha : evalExtN v A with
      | T => exact ⟨A, List.Mem.head _, ha⟩
      | F =>
        have hI : evalExtN v (.impl A B) = BoolVal.T := by
          simp [evalExtN, hImplies, ha]
        obtain ⟨X, hXm, hXt⟩ := hconc v (fun X hX => match mc_s hX with
          | Or.inl hΓ => hAnt X (List.mem_append.mpr (Or.inl hΓ))
          | Or.inr (Or.inl h) => h ▸ hI
          | Or.inr (Or.inr hΔ) => hAnt X (List.mem_append.mpr (Or.inr hΔ)))
        exact ⟨X, List.Mem.tail _ hXm, hXt⟩
    · intro v hAnt
      have hB := hAnt B (List.Mem.head _)
      have hI : evalExtN v (.impl A B) = BoolVal.T := by
        simp [evalExtN, hImplies]; cases evalExtN v A <;> simp [hB]
      exact hconc v (fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X
            (List.Mem.tail _ (List.mem_append.mpr (Or.inl hΓ)))
        | Or.inr (Or.inl h) => h ▸ hI
        | Or.inr (Or.inr hΔ) => hAnt X
            (List.Mem.tail _ (List.mem_append.mpr (Or.inr hΔ))))

helper theorem exists_complex_formula (s : Sequent)
    (hpos : sequentComplexity s > 0) :
    (∃ A ∈ s.antecedent, formulaComplexity A > 0) ∨
    (∃ B ∈ s.succedent, formulaComplexity B > 0) :=
-- BEGIN PROOF
  Classical.byContradiction fun hContra => by
    have hNA := fun h => hContra (Or.inl h)
    have hNB := fun h => hContra (Or.inr h)
    have hA : ∀ A ∈ s.antecedent, formulaComplexity A = 0 := fun A hA =>
      Classical.byContradiction fun hc =>
        hNA ⟨A, hA, Nat.pos_of_ne_zero hc⟩
    have hB : ∀ B ∈ s.succedent, formulaComplexity B = 0 := fun B hB =>
      Classical.byContradiction fun hc =>
        hNB ⟨B, hB, Nat.pos_of_ne_zero hc⟩
    have hsc : sequentComplexity s = 0 := by
      rw [sc_sum_s]
      have h1 := sum_zero_s hA
      have h2 := sum_zero_s hB
      omega
    exact absurd hsc (by omega)

helper theorem complex_classification (A : PropFormulaNormalized)
    (hc : formulaComplexity A > 0) :
    (∃ B, A = .neg B) ∨
    (∃ B C, A = .conj B C) ∨
    (∃ B C, A = .disj B C) ∨
    (∃ B C, A = .impl B C) := by
-- BEGIN PROOF
  cases A with
  | var _ => simp [formulaComplexity] at hc
  | neg B => exact Or.inl ⟨B, rfl⟩
  | conj B C => exact Or.inr (Or.inl ⟨B, C, rfl⟩)
  | disj B C => exact Or.inr (Or.inr (Or.inl ⟨B, C, rfl⟩))
  | impl B C => exact Or.inr (Or.inr (Or.inr ⟨B, C, rfl⟩))

helper theorem completeness_by_complexity (n : Nat) :
    ∀ (s : Sequent), sequentComplexity s = n →
      sequentValid s → sequentProvable s := by
-- BEGIN PROOF
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s hsc hv
  by_cases hc : n = 0
  · -- Base case: complexity 0, all formulas are variables
    subst hc
    have ⟨hAnt0, hSucc0⟩ := sequentComplexity_zero_all_zero s (by omega)
    have hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, ∃ m, A = .var m := by
      intro A hA
      rcases List.mem_append.mp hA with hAntA | hSuccA
      · exact complexity_zero_is_var A (hAnt0 A hAntA)
      · exact complexity_zero_is_var A (hSucc0 A hSuccA)
    exact valid_atomic_provable s hv hAllVar
  · have hpos : sequentComplexity s > 0 := by omega
    -- IH for any sequent with smaller complexity
    have ihS : ∀ (s' : Sequent), sequentComplexity s' < sequentComplexity s →
        sequentValid s' → sequentProvable s' :=
      fun s' hlt hv' => ih (sequentComplexity s') (by omega) s' rfl hv'
    -- There exists a formula with positive complexity on one side
    rcases exists_complex_formula s hpos with
      ⟨A, hAmem, hAc⟩ | ⟨B, hBmem, hBc⟩
    · -- Case: positive-complexity formula A in the antecedent
      obtain ⟨Γ, Δ, hant⟩ := list_split_s hAmem
      have hseq : s = Sequent.mk (Γ ++ [A] ++ Δ) s.succedent := by
        cases s; simp at hant ⊢; exact hant
      rcases complex_classification A hAc with
        ⟨C, rfl⟩ | ⟨C, D, rfl⟩ | ⟨C, D, rfl⟩ | ⟨C, D, rfl⟩
      · -- negLeft
        let r := GentzenStep1.negLeft Γ Δ s.succedent C
        have hpv := step1_backward_valid r (hseq ▸ hv)
        obtain ⟨t⟩ := ihS _ (by rw [hseq]; exact step1_complexity_decrease r) hpv
        rw [hseq]; exact ⟨ProofTree.onePremise r t⟩
      · -- andLeft
        let r := GentzenStep1.andLeft Γ Δ s.succedent C D
        have hpv := step1_backward_valid r (hseq ▸ hv)
        obtain ⟨t⟩ := ihS _ (by rw [hseq]; exact step1_complexity_decrease r) hpv
        rw [hseq]; exact ⟨ProofTree.onePremise r t⟩
      · -- orLeft
        let r := GentzenStep2.orLeft Γ Δ s.succedent C D
        have ⟨hpv1, hpv2⟩ := step2_backward_valid r (hseq ▸ hv)
        have hcd := step2_complexity_decrease r
        obtain ⟨t1⟩ := ihS _ (by rw [hseq]; exact hcd.1) hpv1
        obtain ⟨t2⟩ := ihS _ (by rw [hseq]; exact hcd.2) hpv2
        rw [hseq]; exact ⟨ProofTree.twoPremise r t1 t2⟩
      · -- implLeft
        let r := GentzenStep2.implLeft Γ Δ s.succedent C D
        have ⟨hpv1, hpv2⟩ := step2_backward_valid r (hseq ▸ hv)
        have hcd := step2_complexity_decrease r
        obtain ⟨t1⟩ := ihS _ (by rw [hseq]; exact hcd.1) hpv1
        obtain ⟨t2⟩ := ihS _ (by rw [hseq]; exact hcd.2) hpv2
        rw [hseq]; exact ⟨ProofTree.twoPremise r t1 t2⟩
    · -- Case: positive-complexity formula B in the succedent
      obtain ⟨Δ', Λ, hsucc⟩ := list_split_s hBmem
      have hseq : s = Sequent.mk s.antecedent (Δ' ++ [B] ++ Λ) := by
        cases s; simp at hsucc ⊢; exact hsucc
      rcases complex_classification B hBc with
        ⟨C, rfl⟩ | ⟨C, D, rfl⟩ | ⟨C, D, rfl⟩ | ⟨C, D, rfl⟩
      · -- negRight
        let r := GentzenStep1.negRight s.antecedent Δ' Λ C
        have hpv := step1_backward_valid r (hseq ▸ hv)
        obtain ⟨t⟩ := ihS _ (by rw [hseq]; exact step1_complexity_decrease r) hpv
        rw [hseq]; exact ⟨ProofTree.onePremise r t⟩
      · -- andRight
        let r := GentzenStep2.andRight s.antecedent Δ' Λ C D
        have ⟨hpv1, hpv2⟩ := step2_backward_valid r (hseq ▸ hv)
        have hcd := step2_complexity_decrease r
        obtain ⟨t1⟩ := ihS _ (by rw [hseq]; exact hcd.1) hpv1
        obtain ⟨t2⟩ := ihS _ (by rw [hseq]; exact hcd.2) hpv2
        rw [hseq]; exact ⟨ProofTree.twoPremise r t1 t2⟩
      · -- orRight
        let r := GentzenStep1.orRight s.antecedent Δ' Λ C D
        have hpv := step1_backward_valid r (hseq ▸ hv)
        obtain ⟨t⟩ := ihS _ (by rw [hseq]; exact step1_complexity_decrease r) hpv
        rw [hseq]; exact ⟨ProofTree.onePremise r t⟩
      · -- implRight
        let r := GentzenStep1.implRight s.antecedent Δ' Λ C D
        have hpv := step1_backward_valid r (hseq ▸ hv)
        obtain ⟨t⟩ := ihS _ (by rw [hseq]; exact step1_complexity_decrease r) hpv
        rw [hseq]; exact ⟨ProofTree.onePremise r t⟩

proof_of completeness_G := completeness_by_complexity (sequentComplexity s) s rfl hv

helper theorem boolval_eq_F_of_ne_T {b : BoolVal} (h : b ≠ BoolVal.T) :
    b = BoolVal.F := by cases b <;> simp_all

helper def formulaVarsN : PropFormulaNormalized → Set Nat
  | .var n => fun m => m = n
  | .neg A => formulaVarsN A
  | .conj A B => formulaVarsN A ∪ formulaVarsN B
  | .disj A B => formulaVarsN A ∪ formulaVarsN B
  | .impl A B => formulaVarsN A ∪ formulaVarsN B

helper theorem evalExtN_depends_on_vars (A : PropFormulaNormalized) (v v' : Valuation)
    (h : ∀ n : Nat, formulaVarsN A n → v n = v' n) :
    evalExtN v A = evalExtN v' A := by
-- BEGIN PROOF
  induction A with
  | var n => simp only [evalExtN]; exact h n rfl
  | neg A ih => simp only [evalExtN]; rw [ih h]
  | conj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | disj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | impl A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]

helper theorem formulaVarIndices_complete (A : PropFormulaNormalized) (n : Nat)
    (h : formulaVarsN A n) : n ∈ formulaVarIndices A := by
-- BEGIN PROOF
  induction A with
  | var m =>
    simp only [formulaVarsN] at h; subst h; simp [formulaVarIndices]
  | neg B ih => exact ih h
  | conj B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))
  | disj B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))
  | impl B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))

helper theorem sequentVarIndices_complete (s : Sequent) (A : PropFormulaNormalized)
    (hA : A ∈ s.antecedent ++ s.succedent) (n : Nat) (hn : formulaVarsN A n) :
    n ∈ sequentVarIndices s :=
-- BEGIN PROOF
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨A, hA, formulaVarIndices_complete A n hn⟩)

helper theorem allValuations_covers (vars : List Nat) (v : Valuation) :
    ∃ w ∈ allValuations vars, ∀ i ∈ vars, w i = v i := by
-- BEGIN PROOF
  induction vars with
  | nil => exact ⟨fun _ => BoolVal.F, List.Mem.head _, fun _ h => (List.not_mem_nil h).elim⟩
  | cons n ns ih =>
    obtain ⟨w0, hw0mem, hw0eq⟩ := ih
    -- Construct the covering valuation
    rcases boolval_T_or_F (v n) with hvn | hvn
    · -- v n = T: use the T-branch
      refine ⟨fun m => if m == n then BoolVal.T else w0 m, ?_, ?_⟩
      · simp only [allValuations]
        exact List.mem_flatMap.mpr ⟨w0, hw0mem, List.Mem.head _⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hns
        · simp [hvn]
        · -- i ∈ ns; need: (if i == n then T else w0 i) = v i
          by_cases hin : i = n
          · subst hin; simp [hvn]
          · simp [beq_eq_false_iff_ne.mpr hin]; exact hw0eq i hns
    · -- v n = F: use the F-branch
      refine ⟨fun m => if m == n then BoolVal.F else w0 m, ?_, ?_⟩
      · simp only [allValuations]
        exact List.mem_flatMap.mpr ⟨w0, hw0mem, List.Mem.tail _ (List.Mem.head _)⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hns
        · simp [hvn]
        · by_cases hin : i = n
          · subst hin; simp [hvn]
          · simp [beq_eq_false_iff_ne.mpr hin]; exact hw0eq i hns

helper theorem checkSequentValidFor_iff (s : Sequent) (v : Valuation) :
    checkSequentValidFor s v = true ↔
    ((∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) →
     (∃ B ∈ s.succedent, evalExtN v B = BoolVal.T)) := by
-- BEGIN PROOF
  constructor
  · -- Forward: checkSequentValidFor true → implication holds
    intro hcheck hAllT
    simp only [checkSequentValidFor] at hcheck
    have hallb : (s.antecedent.all (fun A => evalExtN v A == BoolVal.T)) = true := by
      rw [List.all_eq_true]
      intro A hA; exact beq_iff_eq.mpr (hAllT A hA)
    simp [hallb] at hcheck
    exact hcheck
  · -- Backward: implication holds → checkSequentValidFor true
    intro hf
    simp only [checkSequentValidFor]
    by_cases hallb : (s.antecedent.all (fun A => evalExtN v A == BoolVal.T)) = true
    · simp [hallb]
      rw [List.all_eq_true] at hallb
      have hAllT : ∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T :=
        fun A hA => beq_iff_eq.mp (hallb A hA)
      exact hf hAllT
    · simp [Bool.eq_false_iff.mpr hallb]

proof_of checkSequentValid_correct := by
  -- BEGIN PROOF
    simp [checkSequentValid, List.all_eq_true]
    constructor
    · -- Forward: checkSequentValid s = true → sequentValid s
      intro hall v hAntT
      -- Find a valuation w in allValuations that agrees with v on sequent vars
      obtain ⟨w, hwmem, hwagree⟩ := allValuations_covers (sequentVarIndices s) v
      -- w satisfies checkSequentValidFor
      have hwcheck := (checkSequentValidFor_iff s w).mp (hall w hwmem)
      -- Show w makes all antecedents T (since it agrees with v on relevant vars)
      have hAntW : ∀ A ∈ s.antecedent, evalExtN w A = BoolVal.T := by
        intro A hA
        have heq : evalExtN w A = evalExtN v A :=
          evalExtN_depends_on_vars A w v (fun n hn =>
            (hwagree n (sequentVarIndices_complete s A
              (List.mem_append.mpr (Or.inl hA)) n hn)))
        rw [heq]; exact hAntT A hA
      -- Get a succedent formula B true under w
      obtain ⟨B, hBmem, hBw⟩ := hwcheck hAntW
      -- Transfer back to v
      have heqB : evalExtN v B = evalExtN w B :=
        evalExtN_depends_on_vars B v w (fun n hn =>
          (hwagree n (sequentVarIndices_complete s B
            (List.mem_append.mpr (Or.inr hBmem)) n hn)).symm)
      exact ⟨B, hBmem, heqB.trans hBw⟩
    · -- Backward: sequentValid s → checkSequentValid s = true
      intro hvalid w hwmem
      exact (checkSequentValidFor_iff s w).mpr (fun hAntW => hvalid w hAntW)

helper theorem falsifiedBy_of_checkFalse (s : Sequent) (v : Valuation)
    (h : checkSequentValidFor s v = false) :
    sequentFalsifiedBy s v := by
-- BEGIN PROOF
  simp only [checkSequentValidFor] at h
  -- h : (if cond = true then ... else true) = false
  -- Case split on the condition (Bool-valued, so decidable)
  cases hcond : s.antecedent.all (fun A => evalExtN v A == BoolVal.T) with
  | false =>
    -- If condition is false, the if-then-else gives `true`, contradicting h
    simp [hcond] at h
  | true =>
    -- Condition is true: all antecedent formulas evaluate to T
    simp [hcond] at h
    -- h : s.succedent.any (fun B => evalExtN v B == BoolVal.T) = false
    constructor
    · -- All antecedent formulas evaluate to T
      intro A hA
      exact beq_iff_eq.mp ((List.all_eq_true.mp hcond) A hA)
    · -- All succedent formulas evaluate to F (simp already converted h)
      intro B hB
      exact boolval_eq_F_of_ne_T (h B hB)

proof_of search_falsifying_extraction := by
  -- BEGIN PROOF
    -- Step 1: From ¬sequentValid s, derive checkSequentValid s = false
    --         using Bool case analysis (no Classical axioms needed).
    have hcheck : checkSequentValid s = false := by
      cases hb : checkSequentValid s with
      | false => rfl
      | true => exact absurd (checkSequentValid_correct s |>.mp hb) hf
    -- Step 2: Extract a valuation from allValuations that fails the check.
    rw [checkSequentValid] at hcheck
    obtain ⟨v, hv_mem, hv_fail⟩ := List.all_eq_false.mp hcheck
    -- Step 3: Convert checkSequentValidFor failure to falsification evidence.
    have hv_false : checkSequentValidFor s v = false :=
      Bool.eq_false_iff.mpr hv_fail
    have hfals := falsifiedBy_of_checkFalse s v hv_false
    -- Step 4: Wrap into sequentFalsifiable.
    exact ⟨v, hfals.1, hfals.2⟩

helper /-- All indexed deduction trees satisfy the structural well-formedness
    predicate. -/
theorem deductionTree_wf {c : Sequent} (dt : DeductionTree c) : WFTree dt := by
  induction dt with
  | leaf s => exact WFTree.leaf s
  | onePremise rule _ ih => exact WFTree.step1 rule ih
  | twoPremise rule _ _ ihL ihR => exact WFTree.step2 rule ihL ihR

helper /-- The search procedure terminates: starting from any sequent, search
    produces a finished tree. Proved by strong induction on
    maxUnfinishedLeafComplexity. -/
theorem search_terminates (s : Sequent) :
    isFinishedTree mode (search mode (DeductionTree.leaf s)) := by
-- BEGIN PROOF
  suffices h : ∀ (n : Nat) {c : Sequent} (dt : DeductionTree c),
      maxUnfinishedLeafComplexity mode dt = n →
      isFinishedTree mode (search mode dt) by
    exact h _ _ rfl
  intro n; induction n using Nat.strongRecOn with | ind n ih =>
  intro c dt hn
  by_cases hfin : isFinishedTreeBool mode dt = true
  · rw [search_of_finished dt hfin]
    exact (isFinishedTreeBool_iff_isFinishedTree dt).mp hfin
  · have hprog := searchRound_complexity_decrease dt hfin
    rw [search.eq_1 mode dt]
    simp only [hfin]
    exact ih _ (by omega) _ rfl

helper /-- search preserves the root conclusion of the deduction tree. Under the
    indexed form, this is `rfl`. -/
theorem search_conclusion {c : Sequent} (dt : DeductionTree c) :
    (search mode dt).conclusion = dt.conclusion := rfl

helper /-- search preserves WFTree. -/
theorem search_wf {c : Sequent} (dt : DeductionTree c) (_hwf : WFTree dt) :
    WFTree (search mode dt) := deductionTree_wf _

proof_of searchStart_atomic_closed := by
  simpa [isFinishedTree, isFinishedLeaf, searchStart] using
    (search_terminates (mode := .atomic) s)

proof_of search_theorem_3_4_1 := by
  -- BEGIN PROOF
    intro T
    have hwf : WFTree T := search_wf _ (WFTree.leaf s)
    have hconc : T.conclusion = s := search_conclusion _
    have hfin : isFinishedTree mode T := search_terminates s
    refine ⟨hfin, ?_, ?_⟩
    · -- Part 2: valid → isProofTree
      -- For each leaf l, if it were not an axiom, then since it's finished it
      -- must be all-atomic. By the contrapositive of valid_atomic_is_axiom,
      -- it is not valid, hence falsifiable. But by deductionTree_falsification_iff,
      -- any falsification of a leaf propagates to the root, contradicting validity.
      intro hv l hl
      exact Classical.byContradiction fun hna => by
        rcases hfin l hl with hax | hallat
        · exact hna hax.2
        · have hAllVar : ∀ A ∈ l.antecedent ++ l.succedent, ∃ n, A = .var n := by
            intro A hA; have hat := hallat A hA
            cases A with | var n => exact ⟨n, rfl⟩ | _ => simp [isAtomicFormula] at hat
          have hnv_l : ¬sequentValid l := fun hvl => hna (valid_atomic_is_axiom l hvl hAllVar)
          obtain ⟨v, hfals_l⟩ := search_falsifying_extraction l hnv_l
          have hfals_root := (deductionTree_falsification_iff v T hwf).mpr ⟨l, hl, hfals_l⟩
          rw [hconc] at hfals_root
          obtain ⟨hAnt, hSucc⟩ := hfals_root
          obtain ⟨B, hBmem, hBT⟩ := hv v hAnt
          have hBF := hSucc B hBmem; rw [hBT] at hBF; exact absurd hBF (by decide)
    · -- Part 3: ¬valid → falsifying valuations found in nonAxiomLeaves
      -- Given v falsifying s, propagate through the tree to find a leaf l
      -- falsified by v. Since l is falsified, it cannot be an axiom (an axiom
      -- has a shared formula evaluated both T and F). So l ∈ nonAxiomLeaves.
      intro _hnv v hfals_s
      have hfals_root : sequentFalsifiedBy T.conclusion v := by rw [hconc]; exact hfals_s
      obtain ⟨l, hl, hfals_l⟩ := (deductionTree_falsification_iff v T hwf).mp hfals_root
      have hna : ¬isAxiom l := by
        intro ⟨A, hA_ant, hA_succ⟩
        obtain ⟨hAnt, hSucc⟩ := hfals_l
        have hT := hAnt A hA_ant; have hF := hSucc A hA_succ
        rw [hT] at hF; exact absurd hF (by decide)
      have hl_na : l ∈ nonAxiomLeaves T := by
        simp only [nonAxiomLeaves, List.mem_filter]; refine ⟨hl, ?_⟩
        simp only [Bool.not_eq_true']; rw [Bool.eq_false_iff]; intro htrue
        apply hna; rw [List.any_eq_true] at htrue; obtain ⟨A, hA, htrue2⟩ := htrue
        rw [List.any_eq_true] at htrue2; obtain ⟨B, hB, hab⟩ := htrue2
        rw [beq_iff_eq] at hab; exact ⟨A, hA, hab ▸ hB⟩
      exact ⟨l, hl_na, hfals_l⟩

end LCS.Propositional.Systems.G.Search
end
