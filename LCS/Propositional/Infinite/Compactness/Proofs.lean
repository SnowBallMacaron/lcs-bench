import LCS.Propositional.Infinite.Compactness

namespace LCS.Propositional.Infinite.Compactness

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Systems.G.Search

open LCS.Propositional.Infinite

open Classical

helper /-- Right-weakening for G' proof trees: if there is a proof tree for the
    sequent Gamma -> Delta, then there is a proof tree for
    Gamma -> Delta ++ [C] for any formula C. This is admissible in G'
    because all rules carry the full succedent context and the extra
    formula simply extends the tail parameter. -/
noncomputable def proofTreeWeakenRight (C : PropFormulaNormalized) (s : Sequent)
    (t : ProofTree s) :
    ProofTree (Sequent.mk s.antecedent (s.succedent ++ [C])) := by
  induction t with
  | @axiom_ s h =>
    -- h : ∃ A, A ∈ s.antecedent ∧ A ∈ s.succedent
    -- The target ProofTree.axiom_ takes a Prop-valued existential, so we just
    -- transform the proof: any A in s.succedent is also in s.succedent ++ [C].
    exact ProofTree.axiom_ _
      (h.imp fun A ⟨hAnt, hSuc⟩ => ⟨hAnt, List.mem_append_left _ hSuc⟩)
  | onePremise rule _ ih =>
    cases rule with
    | andLeft Γ Δ Λ A B =>
      exact ProofTree.onePremise (GentzenStep1.andLeft Γ Δ (Λ ++ [C]) A B) ih
    | orRight Γ Δ Λ A B =>
      have : Δ ++ [A, B] ++ Λ ++ [C] = Δ ++ [A, B] ++ (Λ ++ [C]) := by
        simp [List.append_assoc]
      have : Δ ++ [PropFormulaNormalized.disj A B] ++ Λ ++ [C] =
             Δ ++ [PropFormulaNormalized.disj A B] ++ (Λ ++ [C]) := by
        simp [List.append_assoc]
      rw [show Δ ++ [A, B] ++ Λ ++ [C] = Δ ++ [A, B] ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih
      rw [show Δ ++ [PropFormulaNormalized.disj A B] ++ Λ ++ [C] =
          Δ ++ [PropFormulaNormalized.disj A B] ++ (Λ ++ [C]) from by simp [List.append_assoc]]
      exact ProofTree.onePremise (GentzenStep1.orRight Γ Δ (Λ ++ [C]) A B) ih
    | implRight Γ Δ Λ A B =>
      rw [show (B :: (Δ ++ Λ)) ++ [C] = B :: (Δ ++ (Λ ++ [C])) from by
        simp [List.append_assoc]] at ih
      rw [show Δ ++ [PropFormulaNormalized.impl A B] ++ Λ ++ [C] =
          Δ ++ [PropFormulaNormalized.impl A B] ++ (Λ ++ [C]) from by simp [List.append_assoc]]
      exact ProofTree.onePremise (GentzenStep1.implRight Γ Δ (Λ ++ [C]) A B) ih
    | negLeft Γ Δ Λ A =>
      rw [show [A] ++ Λ ++ [C] = [A] ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih
      exact ProofTree.onePremise (GentzenStep1.negLeft Γ Δ (Λ ++ [C]) A) ih
    | negRight Γ Δ Λ A =>
      rw [show Δ ++ Λ ++ [C] = Δ ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih
      rw [show Δ ++ [PropFormulaNormalized.neg A] ++ Λ ++ [C] =
          Δ ++ [PropFormulaNormalized.neg A] ++ (Λ ++ [C]) from by simp [List.append_assoc]]
      exact ProofTree.onePremise (GentzenStep1.negRight Γ Δ (Λ ++ [C]) A) ih
  | twoPremise rule _ _ ih1 ih2 =>
    cases rule with
    | andRight Γ Δ Λ A B =>
      rw [show Δ ++ [A] ++ Λ ++ [C] = Δ ++ [A] ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih1
      rw [show Δ ++ [B] ++ Λ ++ [C] = Δ ++ [B] ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih2
      rw [show Δ ++ [PropFormulaNormalized.conj A B] ++ Λ ++ [C] =
          Δ ++ [PropFormulaNormalized.conj A B] ++ (Λ ++ [C]) from by simp [List.append_assoc]]
      exact ProofTree.twoPremise (GentzenStep2.andRight Γ Δ (Λ ++ [C]) A B) ih1 ih2
    | orLeft Γ Δ Λ A B =>
      exact ProofTree.twoPremise (GentzenStep2.orLeft Γ Δ (Λ ++ [C]) A B) ih1 ih2
    | implLeft Γ Δ Λ A B =>
      rw [show [A] ++ Λ ++ [C] = [A] ++ (Λ ++ [C]) from by
        simp [List.append_assoc]] at ih1
      exact ProofTree.twoPremise (GentzenStep2.implLeft Γ Δ (Λ ++ [C]) A B) ih1 ih2

helper /-- If the list L is unsatisfiable (no valuation makes all true), then
    for any formula B, the sequent L -> [B] is provable in G'. The proof
    constructs L -> [] (valid, hence provable by completeness_G) and then
    right-weakens. -/
theorem unsatisfiable_provable (L : List PropFormulaNormalized)
    (hUnsat : ¬ ∃ v : Valuation, ∀ A ∈ L, evalExtN v A = BoolVal.T)
    (B : PropFormulaNormalized) : sequentProvable (Sequent.mk L [B]) := by
-- BEGIN PROOF
  -- Show ⟨L, []⟩ is valid (vacuously, since antecedent is unsatisfiable)
  have hValid : sequentValid (Sequent.mk L []) := by
    intro v hAnt
    exfalso; exact hUnsat ⟨v, hAnt⟩
  -- By completeness
  have ⟨tree⟩ := completeness_G (Sequent.mk L []) hValid
  -- Right-weaken to get ⟨L, [B]⟩
  exact ⟨proofTreeWeakenRight B _ tree⟩

helper /-- Variable set for a normalized formula. -/
def formulaVarsN : PropFormulaNormalized → Nat → Prop
  | .var m => fun n => n = m
  | .neg A => formulaVarsN A
  | .conj A B => fun n => formulaVarsN A n ∨ formulaVarsN B n
  | .disj A B => fun n => formulaVarsN A n ∨ formulaVarsN B n
  | .impl A B => fun n => formulaVarsN A n ∨ formulaVarsN B n

helper /-- Compute an upper bound on variable indices in a formula.
    All variables in A satisfy index < varBound A. -/
def varBound : PropFormulaNormalized → Nat
  | .var n => n + 1
  | .neg A => varBound A
  | .conj A B => max (varBound A) (varBound B)
  | .disj A B => max (varBound A) (varBound B)
  | .impl A B => max (varBound A) (varBound B)

helper theorem formulaVarsN_lt_varBound (A : PropFormulaNormalized) (n : Nat)
    (hn : formulaVarsN A n) : n < varBound A := by
-- BEGIN PROOF
  induction A with
  | var m => simp only [formulaVarsN] at hn; subst hn; simp [varBound]
  | neg A ih => exact ih hn
  | conj A B ihA ihB =>
    simp only [formulaVarsN] at hn
    cases hn with
    | inl h => exact Nat.lt_of_lt_of_le (ihA h) (Nat.le_max_left _ _)
    | inr h => exact Nat.lt_of_lt_of_le (ihB h) (Nat.le_max_right _ _)
  | disj A B ihA ihB =>
    simp only [formulaVarsN] at hn
    cases hn with
    | inl h => exact Nat.lt_of_lt_of_le (ihA h) (Nat.le_max_left _ _)
    | inr h => exact Nat.lt_of_lt_of_le (ihB h) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    simp only [formulaVarsN] at hn
    cases hn with
    | inl h => exact Nat.lt_of_lt_of_le (ihA h) (Nat.le_max_left _ _)
    | inr h => exact Nat.lt_of_lt_of_le (ihB h) (Nat.le_max_right _ _)

helper /-- evalExtN depends only on the variables occurring in the formula. -/
theorem evalExtN_depends_on_vars_local (A : PropFormulaNormalized) (v v' : Valuation)
    (h : ∀ n : Nat, formulaVarsN A n → v n = v' n) :
    evalExtN v A = evalExtN v' A := by
-- BEGIN PROOF
  induction A with
  | var n =>
    simp only [evalExtN]
    exact h n rfl
  | neg A ih =>
    simp only [evalExtN]
    rw [ih (fun n hn => h n hn)]
  | conj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)),
        ihB (fun n hn => h n (Or.inr hn))]
  | disj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)),
        ihB (fun n hn => h n (Or.inr hn))]
  | impl A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)),
        ihB (fun n hn => h n (Or.inr hn))]

helper /-- Any list L backs a finite set {a | a ∈ L}. -/
theorem list_finite_toSet (L : List α) :
    Set.Finite (fun a => a ∈ L) :=
-- BEGIN PROOF
  ⟨L, fun a => Iff.rfl⟩

helper /-- "good v n" means: for every nonempty list of Gamma-formulas, there exists a
    satisfying valuation agreeing with v on indices {0, ..., n-1}. -/
def good (Gamma : Set PropFormulaNormalized) (v : Valuation) (n : Nat) : Prop :=
  ∀ (L : List PropFormulaNormalized), (∀ A ∈ L, A ∈ Gamma) → L ≠ [] →
    ∃ w : Valuation, (∀ k, k < n → w k = v k) ∧ ∀ A ∈ L, evalExtN w A = BoolVal.T

helper /-- Update a valuation at index n. Replaces Function.update (which requires Mathlib). -/
def valUpdate (v : Valuation) (n : Nat) (b : BoolVal) : Valuation :=
  fun k => if k = n then b else v k

helper theorem valUpdate_same (v : Valuation) (n : Nat) (b : BoolVal) :
    valUpdate v n b n = b := by simp [valUpdate]

helper theorem valUpdate_ne (v : Valuation) (n : Nat) (b : BoolVal) (k : Nat)
    (hk : k ≠ n) : valUpdate v n b k = v k := by simp [valUpdate, hk]

helper theorem good_step (Gamma : Set PropFormulaNormalized) :
    ∀ (v : Valuation) (n : Nat), good Gamma v n →
      ∃ b : BoolVal, good Gamma (valUpdate v n b) (n + 1) := by
  intro v n hgood
  -- Extract a failing witness from ¬ good at a given boolean value
  -- ¬ good means: ∃ L from Gamma, L ≠ [], ∀ w agreeing on {0..n},
  --   some A ∈ L is not satisfied by w.
  suffices hKey : ∀ b, ¬ good Gamma (valUpdate v n b) (n + 1) →
      ∃ (L : List PropFormulaNormalized), (∀ A ∈ L, A ∈ Gamma) ∧ L ≠ [] ∧
        ∀ w, (∀ k, k < n + 1 → w k = valUpdate v n b k) →
          (∀ A ∈ L, evalExtN w A = BoolVal.T) → False by
    -- Now use hKey to close: at least one of T, F must work.
    exact Classical.byContradiction fun hBad => by
      have hNotT : ¬ good Gamma (valUpdate v n BoolVal.T) (n + 1) :=
        fun h => hBad ⟨BoolVal.T, h⟩
      have hNotF : ¬ good Gamma (valUpdate v n BoolVal.F) (n + 1) :=
        fun h => hBad ⟨BoolVal.F, h⟩
      obtain ⟨LT, hLTsub, hLTne, hLTfail⟩ := hKey BoolVal.T hNotT
      obtain ⟨LF, hLFsub, hLFne, hLFfail⟩ := hKey BoolVal.F hNotF
      have hUnion_sub : ∀ A ∈ LT ++ LF, A ∈ Gamma := by
        intro A hA; simp [List.mem_append] at hA
        cases hA with | inl h => exact hLTsub A h | inr h => exact hLFsub A h
      have hUnion_ne : LT ++ LF ≠ [] := by
        cases LT with
        | nil => exact absurd rfl hLTne
        | cons a t => simp
      obtain ⟨w, hwAgree, hwSat⟩ := hgood (LT ++ LF) hUnion_sub hUnion_ne
      cases hWn : w n with
      | T =>
        exact hLTfail w
          (fun k hk => by
            cases Nat.lt_succ_iff_lt_or_eq.mp hk with
            | inl hlt => rw [hwAgree k hlt, valUpdate_ne _ _ _ _ (by omega)]
            | inr heq => subst heq; rw [hWn, valUpdate_same])
          (fun A hA => hwSat A (List.mem_append_left LF hA))
      | F =>
        exact hLFfail w
          (fun k hk => by
            cases Nat.lt_succ_iff_lt_or_eq.mp hk with
            | inl hlt => rw [hwAgree k hlt, valUpdate_ne _ _ _ _ (by omega)]
            | inr heq => subst heq; rw [hWn, valUpdate_same])
          (fun A hA => hwSat A (List.mem_append_right LT hA))
  -- Prove hKey: extract a failing witness from ¬ good
  intro b hNot
  -- hNot : ¬ (∀ L, (∀ A ∈ L, A ∈ Gamma) → L ≠ [] → ∃ w, ...)
  -- We need to extract a witness L. Use Classical reasoning.
  exact Classical.byContradiction fun hNoWit => by
    apply hNot
    intro L hLsub hLne
    -- If no witness L exists, then for this L the conclusion must hold
    exact Classical.byContradiction fun hNoW => by
      apply hNoWit
      refine ⟨L, hLsub, hLne, fun w hwAgree hwSat => ?_⟩
      exact hNoW ⟨w, hwAgree, hwSat⟩

helper theorem exists_good_valuation (Gamma : Set PropFormulaNormalized)
    (hList : ∀ (L : List PropFormulaNormalized), (∀ A ∈ L, A ∈ Gamma) → L ≠ [] →
      ∃ w : Valuation, ∀ A ∈ L, evalExtN w A = BoolVal.T) :
    ∃ v : Valuation, ∀ n, good Gamma v n := by
  let v : Valuation := WellFounded.fix Nat.lt_wfRel.wf fun k rec =>
    let vPartial : Valuation := fun i =>
      if h : i < k then rec i h else BoolVal.T
    -- good vPartial k holds: any list from Gamma is sat by some w agreeing on {0..k-1}
    -- We'll prove this outside and use it here to pick the bit.
    -- For now, choose T if it preserves goodness, else F.
    if good Gamma (valUpdate vPartial k BoolVal.T) (k + 1)
    then BoolVal.T
    else BoolVal.F

  -- Show that v's partial prefix at level k equals vPartial
  -- Key: WellFounded.fix_eq gives v(k) = body(k, fun i h => v(i))
  have vUnfold : ∀ k, v k =
      let vPartial : Valuation := fun i => if h : i < k then v i else BoolVal.T
      if good Gamma (valUpdate vPartial k BoolVal.T) (k + 1)
      then BoolVal.T
      else BoolVal.F := by
    intro k
    show WellFounded.fix Nat.lt_wfRel.wf _ k = _
    rw [WellFounded.fix_eq]

  -- Define vPartialAt k = the partial valuation using v on {0..k-1}, T elsewhere
  let vPartialAt : Nat → Valuation := fun k i =>
    if i < k then v i else BoolVal.T

  -- good (vPartialAt k) k holds for all k, by induction
  have goodPartial : ∀ k, good Gamma (vPartialAt k) k := by
    intro k; induction k with
    | zero =>
      intro L hLsub hLne; obtain ⟨w, hw⟩ := hList L hLsub hLne
      exact ⟨w, fun _ hk => absurd hk (Nat.not_lt_zero _), hw⟩
    | succ k ih =>
      -- good (vPartialAt k) k holds by ih
      -- step gives us: ∃ b, good (valUpdate (vPartialAt k) k b) (k+1)
      -- valUpdate (vPartialAt k) k b = vPartialAt (k+1) when b = v(k)
      -- Because v(k) is chosen to be T if T-goodness holds, else F.
      -- And step guarantees at least one of T/F works.
      -- First, let's show that good (valUpdate (vPartialAt k) k (v k)) (k+1)
      have hStep := good_step Gamma (vPartialAt k) k ih
      obtain ⟨b, hb⟩ := hStep
      -- v(k) is defined as T if T-goodness holds, else F
      -- We need: good (valUpdate (vPartialAt k) k (v k)) (k + 1)
      -- Note: vPartialAt k = fun i => if i < k then v i else T
      -- And the condition in v's definition uses vPartial which is the same thing.
      -- The WF recursion defines v(k) in terms of vPartial = fun i => dite (i < k) ...
      -- We need to relate this to vPartialAt k = fun i => ite (i < k) ...
      -- These differ only in dite vs ite, which are the same when the branches
      -- don't depend on the proof.
      have hvk : v k =
          if good Gamma (valUpdate (vPartialAt k) k BoolVal.T) (k + 1)
          then BoolVal.T else BoolVal.F := by
        exact vUnfold k
      -- Helper: show vPartialAt (k+1) = valUpdate (vPartialAt k) k (v k)
      have hEqPartial : ∀ i, vPartialAt (k + 1) i = valUpdate (vPartialAt k) k (v k) i := by
        intro i
        show (if i < k + 1 then v i else BoolVal.T) =
          (if i = k then v k else (if i < k then v i else BoolVal.T))
        by_cases hik : i = k
        · subst hik; simp [Nat.lt_succ_of_le (Nat.le_refl _)]
        · by_cases hilk : i < k
          · have : i < k + 1 := by omega
            simp [this, hik, hilk]
          · have : ¬ (i < k + 1) := by omega
            simp [this, hik, hilk]
      -- Now case split on whether T preserves goodness
      cases Classical.em (good Gamma (valUpdate (vPartialAt k) k BoolVal.T) (k + 1)) with
      | inl hT =>
        have hvkT : v k = BoolVal.T := by rw [hvk, if_pos hT]
        -- vPartialAt (k+1) i = valUpdate (vPartialAt k) k (v k) i
        --                     = valUpdate (vPartialAt k) k T i  (by hvkT)
        -- And hT gives w with w i = valUpdate (vPartialAt k) k T i for i < k+1
        intro L hLsub hLne
        obtain ⟨w, hwAgree, hwSat⟩ := hT L hLsub hLne
        refine ⟨w, fun i hi => ?_, hwSat⟩
        -- Goal: w i = vPartialAt (k + 1) i
        have : w i = valUpdate (vPartialAt k) k BoolVal.T i := hwAgree i hi
        rw [this, ← hvkT, ← hEqPartial]
      | inr hNotT =>
        have hvkF : v k = BoolVal.F := by rw [hvk, if_neg hNotT]
        have hF : good Gamma (valUpdate (vPartialAt k) k BoolVal.F) (k + 1) := by
          cases b with
          | T => exact absurd hb hNotT
          | F => exact hb
        intro L hLsub hLne
        obtain ⟨w, hwAgree, hwSat⟩ := hF L hLsub hLne
        refine ⟨w, fun i hi => ?_, hwSat⟩
        have : w i = valUpdate (vPartialAt k) k BoolVal.F i := hwAgree i hi
        rw [this, ← hvkF, ← hEqPartial]

  -- Now show v is good at every level: good v n
  -- v agrees with vPartialAt n on {0..n-1} (they're the same for i < n)
  have vGoodN : ∀ n, good Gamma v n := by
    intro n L hLsub hLne
    obtain ⟨w, hwAgree, hwSat⟩ := goodPartial n L hLsub hLne
    refine ⟨w, fun k hk => ?_, hwSat⟩
    rw [hwAgree k hk]
    -- Need: vPartialAt n k = v k when k < n
    show (if k < n then v k else BoolVal.T) = v k
    rw [if_pos hk]
  exact ⟨v, vGoodN⟩

helper theorem good_valuation_satisfies (Gamma : Set PropFormulaNormalized)
    (v : Valuation) (vGoodN : ∀ n, good Gamma v n) : setSatisfiable Gamma := by
  refine ⟨v, fun A hA => ?_⟩
  let N := varBound A
  have hGoodN := vGoodN N [A] (fun X hX => by simp at hX; subst hX; exact hA)
    (by simp)
  obtain ⟨w, hwAgree, hwSat⟩ := hGoodN
  have hEq : evalExtN v A = evalExtN w A := by
    apply evalExtN_depends_on_vars_local A v w
    intro k hk
    exact (hwAgree k (formulaVarsN_lt_varBound A k hk)).symm
  rw [hEq]; exact hwSat A (List.Mem.head _)

proof_of compactness_G := by
  have hList : ∀ (L : List PropFormulaNormalized), (∀ A ∈ L, A ∈ Gamma) → L ≠ [] →
      ∃ w : Valuation, ∀ A ∈ L, evalExtN w A = BoolVal.T := by
    intro L hLsub hLne
    obtain ⟨w, hw⟩ := h (fun A => A ∈ L) hLsub (list_finite_toSet L)
      (match L, hLne with | a :: _, _ => ⟨a, List.Mem.head _⟩)
    exact ⟨w, fun A hA => hw A hA⟩
  obtain ⟨v, hv⟩ := exists_good_valuation Gamma hList
  exact good_valuation_satisfies Gamma v hv


proof_of model_existence_G := by
  -- BEGIN PROOF
    apply compactness_G
    -- Show finiteSubsetSatisfiable Gamma
    intro S hSsub hSfin ⟨A0, hA0⟩
    -- By contradiction: if S is not satisfiable, then Gamma is inconsistent.
    exact Classical.byContradiction fun hNotSat => by
      -- hNotSat : ¬ setSatisfiable S
      -- hCon gives a formula B that is not provable from Gamma
      obtain ⟨B, hNotProv⟩ := hCon
      apply hNotProv
      -- Need to show setProvable Gamma B
      obtain ⟨L, hL⟩ := hSfin
      refine ⟨L, fun A hA => hSsub A ((hL A).mpr hA), ?_⟩
      -- Need: sequentProvable ⟨L, [B]⟩
      -- L is unsatisfiable (from hNotSat), so by unsatisfiable_provable
      -- the sequent ⟨L, [B]⟩ is provable for any B.
      exact unsatisfiable_provable L
        (fun ⟨v, hv⟩ => hNotSat ⟨v, fun A' hA' => hv A' ((hL A').mp hA')⟩)
        B


proof_of consistency_lemma_G := by
  -- BEGIN PROOF
    obtain ⟨v, hv⟩ := hSat
    show setConsistent Gamma
    unfold setConsistent
    -- Use P0 ∧ ¬P0 as a formula that is always false
    let falsum := PropFormulaNormalized.conj (.var 0) (.neg (.var 0))
    refine ⟨falsum, fun ⟨Gamma_fin, hSub, hProv⟩ => ?_⟩
    have hValid := soundness_G (Sequent.mk Gamma_fin [falsum]) hProv
    have hAntT : ∀ A ∈ Gamma_fin, evalExtN v A = BoolVal.T := by
      intro A hA; exact hv A (hSub A hA)
    obtain ⟨B, hBmem, hBtrue⟩ := hValid v hAntT
    rcases List.mem_cons.mp hBmem with rfl | hB
    · -- B = falsum = P0 ∧ ¬P0, which cannot be true
      simp only [falsum, evalExtN, hAnd, hNeg] at hBtrue
      cases evalExtN v (.var 0) <;> simp_all
    · exact absurd hB (by simp)


proof_of maximallyConsistent_iff_proper_superset_inconsistent := by
  -- BEGIN PROOF
    constructor
    · intro ⟨hCon, hMax⟩
      exact ⟨hCon, fun Delta hSub hNeq hDeltaCon =>
        hNeq (hMax Delta hDeltaCon hSub)⟩
    · intro ⟨hCon, hIncon⟩
      refine ⟨hCon, fun Delta hDeltaCon hSub => ?_⟩
      exact Classical.byContradiction fun hNeq =>
        hIncon Delta hSub hNeq hDeltaCon


proof_of maximal_consistent_extension := by
  -- BEGIN PROOF
    have hSat := model_existence_G Gamma hCon
    obtain ⟨v, hv⟩ := hSat
    refine ⟨allSatisfiedPropositions v, ?_, ?_⟩
    · intro A hA; exact hv A hA
    · constructor
      · exact consistency_lemma_G _ ⟨v, fun A hA => hA⟩
      · intro Delta' hDeltaCon hSub
        funext A; apply propext
        constructor
        · exact hSub A
        · intro hA'
          exact Classical.byContradiction fun hNotInDelta => by
            have hAF : evalExtN v A = BoolVal.F := by
              cases heq : evalExtN v A with | F => rfl | T => exact absurd heq hNotInDelta
            have hNegA : allSatisfiedPropositions v (.neg A) := by
              simp only [allSatisfiedPropositions, evalExtN, hNeg, hAF]
            have hNegA' := hSub _ hNegA
            have hIncon : ¬setConsistent Delta' := by
              intro ⟨B, hNotProv⟩
              apply hNotProv
              refine ⟨[A, .neg A], fun X hX => ?_, ?_⟩
              · rcases List.mem_cons.mp hX with rfl | hX2
                · exact hA'
                · simp at hX2; subst hX2; exact hNegA'
              · refine ⟨ProofTree.onePremise
                  (GentzenStep1.negLeft [A] [] [B] A)
                  (ProofTree.axiom_ (Sequent.mk ([A]) ([A] ++ [B]))
                    ⟨A, List.Mem.head _, List.Mem.head _⟩)⟩
            exact hIncon hDeltaCon


end LCS.Propositional.Infinite.Compactness

namespace LCS.Propositional.Infinite.SignedFormulae

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Systems.G.Search

open LCS.Propositional.Infinite

open LCS.Propositional.Infinite.Compactness

open Classical

helper noncomputable def unneg : PropFormulaNormalized → Option PropFormulaNormalized
  | .neg B => some B
  | _ => none

helper theorem unprovable_finite_subset_satisfiable (seq : InfSequent)
    (hNotProv : ¬ infSeqProvable seq) :
    finiteSubsetSatisfiable (fun C =>
      (∃ n, seq.antecedent n = some C) ∨
      (∃ n B, seq.succedent n = some B ∧ C = .neg B)) := by
  intro S hSsub hSfin ⟨A0, hA0⟩
  obtain ⟨L, hL⟩ := hSfin
  -- Build Gamma_fin: formulas in L that come from the antecedent
  let Gamma_fin := classicalFilter (fun C => ∃ n, seq.antecedent n = some C) L
  -- Build Delta_fin: for each neg X in L from the succedent, extract X
  let succFilter : PropFormulaNormalized → Option PropFormulaNormalized :=
    fun C => match C with
      | .neg X => if ∃ n, seq.succedent n = some X then some X else none
      | _ => none
  let Delta_fin := classicalFilterMap succFilter L
  -- Gamma_fin elements come from the antecedent
  have hGF_ant : ∀ A ∈ Gamma_fin, ∃ n, seq.antecedent n = some A :=
    fun A hA => ((mem_classicalFilter _ L A).mp hA).2
  -- Helper: succFilter C = some B implies ∃ n, suc n = some B
  have succFilter_spec : ∀ C B, succFilter C = some B →
      ∃ n, seq.succedent n = some B := by
    intro C B hfC
    match C with
    | .neg X =>
      simp only [succFilter] at hfC
      split at hfC
      · rename_i hEx; exact Option.some.inj hfC ▸ hEx
      · exact absurd hfC (by simp)
    | .var _ => simp [succFilter] at hfC
    | .conj _ _ => simp [succFilter] at hfC
    | .disj _ _ => simp [succFilter] at hfC
    | .impl _ _ => simp [succFilter] at hfC
  -- Delta_fin elements come from the succedent
  have hDF_suc : ∀ B ∈ Delta_fin, ∃ n, seq.succedent n = some B := by
    intro B hB
    obtain ⟨C, hCL, hfC⟩ := (mem_classicalFilterMap _ L B).mp hB
    exact succFilter_spec C B hfC
  -- The sequent (Gamma_fin, Delta_fin) is not provable
  have hNotProvFin : ¬ sequentProvable (Sequent.mk Gamma_fin Delta_fin) := by
    intro hProv
    exact hNotProv ⟨Gamma_fin, Delta_fin, hGF_ant, hDF_suc, hProv⟩
  -- By completeness contrapositive: not provable → not valid
  have hNotValid : ¬ sequentValid (Sequent.mk Gamma_fin Delta_fin) :=
    fun hv => hNotProvFin (completeness_G _ hv)
  -- Not valid: ∃ v falsifying the sequent
  have hFals : ∃ v : Valuation,
      (∀ A ∈ Gamma_fin, evalExtN v A = BoolVal.T) ∧
      (∀ B ∈ Delta_fin, evalExtN v B ≠ BoolVal.T) := by
    unfold sequentValid at hNotValid
    have ⟨v, hv⟩ := not_forall.mp hNotValid
    rw [not_imp] at hv
    obtain ⟨hAntT, hNoSuc⟩ := hv
    refine ⟨v, hAntT, fun B hB hBT => ?_⟩
    exact hNoSuc ⟨B, hB, hBT⟩
  obtain ⟨v, hvAnt, hvSuc⟩ := hFals
  -- This v satisfies S: for each C in L (hence in S), show evalExtN v C = T
  refine ⟨v, fun C hC => ?_⟩
  have hCL := (hL C).mp hC
  have hCG := hSsub C hC
  -- C ∈ Gamma means either from antecedent or neg B from succedent
  rcases hCG with ⟨n, hn⟩ | ⟨n, B, hn, rfl⟩
  · -- C is from antecedent: C ∈ Gamma_fin, so eval v C = T
    have hCGF : C ∈ Gamma_fin :=
      (mem_classicalFilter _ L C).mpr ⟨hCL, ⟨n, hn⟩⟩
    exact hvAnt C hCGF
  · -- C = neg B where B is from succedent: B ∈ Delta_fin
    have hBDF : B ∈ Delta_fin := by
      apply (mem_classicalFilterMap _ L B).mpr
      refine ⟨.neg B, hCL, ?_⟩
      show succFilter (.neg B) = some B
      simp only [succFilter]
      rw [if_pos ⟨n, hn⟩]
    have hBNotT := hvSuc B hBDF
    -- eval v B ≠ T means eval v B = F, so eval v (neg B) = T
    show evalExtN v (.neg B) = BoolVal.T
    simp only [evalExtN, hNeg]
    cases heq : evalExtN v B with
    | T => exact absurd heq hBNotT
    | F => rfl

helper /-- Theorem 3.5.1 (infrastructure for future proving): If an infinite
    sequent is valid then it is provable (there exists a finite provable
    subsequent). Proved by contradiction using the compactness theorem:
    if not provable, form Gamma = {antecedent formulas} union
    {neg B | B in succedent}, show every finite subset is satisfiable
    (via finite completeness), apply compactness to get a falsifying
    valuation, contradicting validity. This establishes the existence of
    the finite provable subsequent but does NOT extract it from an
    `infSearch`-produced tree — the main textbook statement
    `search_theorem_3_5_1` binds the finite provable subsequent to the
    closed tree produced by `infSearchSteps`. -/
theorem valid_sequent_provable (seq : InfSequent)
    (h : infSeqValid seq)
    : infSeqProvable seq :=
-- BEGIN PROOF
by
  -- Proof by contradiction: assume not provable.
  exact byContradiction fun hNotProv => by
    -- Define Gamma = {A | A in antecedent} ∪ {neg B | B in succedent}
    let Gamma : Set PropFormulaNormalized := fun C =>
      (∃ n, seq.antecedent n = some C) ∨
      (∃ n B, seq.succedent n = some B ∧ C = .neg B)
    have hFSS : finiteSubsetSatisfiable Gamma :=
      unprovable_finite_subset_satisfiable seq hNotProv
    -- Step 2: By compactness, Gamma is satisfiable.
    have hSat := compactness_G Gamma hFSS
    -- Step 3: A satisfying valuation for Gamma falsifies seq.
    obtain ⟨v, hv⟩ := hSat
    have hAntT : ∀ n A, seq.antecedent n = some A → evalExtN v A = BoolVal.T := by
      intro n A hn; exact hv A (Or.inl ⟨n, hn⟩)
    have hSucF : ∀ n B, seq.succedent n = some B → evalExtN v B = BoolVal.F := by
      intro n B hn
      have hNegT := hv (.neg B) (Or.inr ⟨n, B, hn, rfl⟩)
      simp only [evalExtN, hNeg] at hNegT
      cases heq : evalExtN v B with
      | F => rfl
      | T => simp [heq] at hNegT
    -- infSeqValid gives: since all ant are T, some suc is T. Contradiction.
    obtain ⟨n, B, hn, hBT⟩ := h v hAntT
    exact absurd (hSucF n B hn ▸ hBT) (by decide)

helper /-- Theorem 3.5.1 (infrastructure for future proving): Alias of
    `valid_sequent_provable` exposing the finite provable subsequent as a
    triple. Like `valid_sequent_provable`, this is a compactness-based
    existence result that does NOT bind the finite provable subsequent
    to the search tree produced by `infSearchSteps`. The main textbook
    statement `search_theorem_3_5_1` binds the subsequent to the closed
    tree produced by the search procedure. -/
theorem provable_finite_subsequent_exists (seq : InfSequent)
    (h : infSeqValid seq)
    : ∃ (Gamma' : List PropFormulaNormalized) (Delta' : List PropFormulaNormalized),
      (∀ A ∈ Gamma', ∃ n, seq.antecedent n = some A) ∧
      (∀ B ∈ Delta', ∃ n, seq.succedent n = some B) ∧
      sequentProvable (Sequent.mk Gamma' Delta') :=
-- BEGIN PROOF
  valid_sequent_provable seq h

helper /-- Theorem 3.5.1 (infrastructure for future proving): The bundled dichotomy
    "either a falsifying valuation exists or a finite provable subsequent
    exists." This is the semantic dichotomy but DOES NOT bind the falsifying
    valuation or the finite provable subsequent to the search tree produced
    by `infSearchSteps`. The main textbook statement `search_theorem_3_5_1`
    binds both pieces of data to the search procedure. -/
theorem extended_completeness_main (seq : InfSequent)
    : (∃ v : Valuation, infSeqFalsifies v seq) ∨ infSeqProvable seq :=
-- BEGIN PROOF
by
  rcases em (infSeqValid seq) with hValid | hNotValid
  · exact Or.inr (valid_sequent_provable seq hValid)
  · exact Or.inl (LCS.Propositional.Infinite.SignedFormulae.Proofs.falsifying_valuation_from_path seq hNotValid)

helper /-- A falsified sequent cannot be an axiom. -/
theorem falsified_not_axiom (s : Sequent) (v : Valuation)
    (h : sequentFalsifiedBy s v) : ¬ isAxiom s := by
  rintro ⟨A, hA, hB⟩
  have hT := h.1 A hA
  have hF := h.2 A hB
  rw [hT] at hF
  cases hF

helper /-- Extension edges add exactly the truth obligations of their two heads. -/
theorem falsified_extendSeq_iff (s : Sequent) (a b : Option PropFormulaNormalized)
    (v : Valuation) :
    sequentFalsifiedBy (extendSeq s a b) v ↔
      sequentFalsifiedBy s v ∧
      (∀ A, a = some A → evalExtN v A = BoolVal.T) ∧
      (∀ B, b = some B → evalExtN v B = BoolVal.F) := by
  cases a <;> cases b <;>
    simp [extendSeq, sequentFalsifiedBy, List.mem_append, or_imp, forall_and,
      and_assoc, and_left_comm, and_comm]

helper /-- Consuming one more pair of input heads extends precisely the finite
    input support; this is independent of the tree's fixed root label. -/
theorem initialPrefix_succ_extend (seq : InfSequent) (k : Nat) :
    Sequent.mk (initialPrefix seq.antecedent (k + 1))
      (initialPrefix seq.succedent (k + 1)) =
    extendSeq (Sequent.mk (initialPrefix seq.antecedent k)
      (initialPrefix seq.succedent k)) (seq.antecedent k) (seq.succedent k) := by
  cases hA : seq.antecedent k <;> cases hB : seq.succedent k <;>
    simp [initialPrefix, extendSeq, hA, hB]

helper /-- Indexed Gentzen trees carry their own rule-correctness evidence. -/
theorem deductionTree_auto_wf {s : Sequent} (dt : DeductionTree s) : WFTree dt := by
  induction dt with
  | leaf _ => exact WFTree.leaf _
  | onePremise rule _ ih => exact WFTree.step1 rule ih
  | twoPremise rule _ _ ih₁ ih₂ => exact WFTree.step2 rule ih₁ ih₂

helper /-- A single context-introduction step preserves precisely the old label
    and the signed truth requirements of the new heads. -/
theorem appendToLeavesCore_falsification_iff {s : Sequent}
    (t : InfDeductionTree s) (a b : Option PropFormulaNormalized) (v : Valuation) :
    (∃ l ∈ (appendToLeavesCore t a b).leaves, sequentFalsifiedBy l v) ↔
      (∃ l ∈ t.leaves, sequentFalsifiedBy l v) ∧
      (∀ A, a = some A → evalExtN v A = BoolVal.T) ∧
      (∀ B, b = some B → evalExtN v B = BoolVal.F) := by
  have localStep (l : Sequent) :
      (∃ x ∈ (if isAxiomBool l then InfDeductionTree.leaf l
        else .extend a b (.leaf (extendSeq l a b))).leaves,
        sequentFalsifiedBy x v) ↔
      sequentFalsifiedBy l v ∧
        (∀ A, a = some A → evalExtN v A = BoolVal.T) ∧
        (∀ B, b = some B → evalExtN v B = BoolVal.F) := by
    by_cases h : isAxiomBool l = true
    · have hn := fun hf => falsified_not_axiom l v hf ((LCS.Propositional.Infinite.Proofs.isAxiomBool_iff l).mp h)
      simp [h, InfDeductionTree.leaves]
      exact fun hf => False.elim (hn hf)
    · simp [h, InfDeductionTree.leaves, falsified_extendSeq_iff]
  simp only [appendToLeavesCore, InfDeductionTree.leaves_bindLeaves, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨l, hl, hx⟩, hf⟩
    obtain ⟨hfl, ha, hb⟩ := (localStep l).mp ⟨x, hx, hf⟩
    exact ⟨⟨l, hl, hfl⟩, ha, hb⟩
  · rintro ⟨⟨l, hl, hfl⟩, ha, hb⟩
    obtain ⟨x, hx, hf⟩ := (localStep l).mpr ⟨hfl, ha, hb⟩
    exact ⟨x, ⟨l, hl, hx⟩, hf⟩

helper /-- Falsification across one actual search round, including its extension
    edges. Finished open leaves have empty tails, so add no obligations. -/
theorem infExpand_falsification_iff (state : InfSearchState) (v : Valuation) :
    (∃ l ∈ (infExpand state).tree.leaves, sequentFalsifiedBy l v) ↔
      (∃ l ∈ state.tree.leaves, sequentFalsifiedBy l v) ∧
      (∀ A, InfSeq.head state.L = some A → evalExtN v A = BoolVal.T) ∧
      (∀ B, InfSeq.head state.R = some B → evalExtN v B = BoolVal.F) := by
  have localStep (s : Sequent) :
      (∃ l ∈ (if infIsFinishedLeafBool state s then InfDeductionTree.leaf s
        else appendToLeavesCore (InfDeductionTree.ofDeductionTree (searchRound .systematic (.leaf s)))
          (InfSeq.head state.L) (InfSeq.head state.R)).leaves,
        sequentFalsifiedBy l v) ↔
      sequentFalsifiedBy s v ∧
        (∀ A, InfSeq.head state.L = some A → evalExtN v A = BoolVal.T) ∧
        (∀ B, InfSeq.head state.R = some B → evalExtN v B = BoolVal.F) := by
    by_cases hfin : infIsFinishedLeafBool state s = true
    · rcases (LCS.Propositional.Infinite.Proofs.infIsFinishedLeafBool_iff state s).mp hfin with hax | ⟨hl, hr, _⟩
      · have hn := fun hf => falsified_not_axiom s v hf hax
        simp [hfin, InfDeductionTree.leaves]
        exact fun hf => False.elim (hn hf)
      · simp [hfin, InfDeductionTree.leaves, InfSeq.head, hl 0, hr 0]
    · simp only [hfin, Bool.false_eq_true, ↓reduceIte, appendToLeavesCore_falsification_iff,
        LCS.Propositional.Infinite.Proofs.leaves_ofDeductionTree]
      rw [← deductionTree_falsification_iff v (searchRound .systematic (.leaf s))
        (deductionTree_auto_wf _)]
      rfl
  simp only [infExpand, InfDeductionTree.leaves_bindLeaves, List.mem_flatMap]
  constructor
  · rintro ⟨l, ⟨s, hs, hl⟩, hf⟩
    obtain ⟨hfs, ha, hb⟩ := (localStep s).mp ⟨l, hl, hf⟩
    exact ⟨⟨s, hs, hfs⟩, ha, hb⟩
  · rintro ⟨⟨s, hs, hfs⟩, ha, hb⟩
    obtain ⟨l, hl, hf⟩ := (localStep s).mpr ⟨hfs, ha, hb⟩
    exact ⟨l, ⟨s, hs, hl⟩, hf⟩

helper /-- Theorem 3.5.1 (required helper): The "L-sequence" of
    `infSearchSteps seq k` is `k`-shifted relative to the original
    `seq.antecedent`. Specifically, `(infSearchSteps seq k).L n =
    seq.antecedent (n + k + 1)`. This lets us decode "heads consumed during
    round k+1" back into values of the original `seq.antecedent`. -/
theorem infSearchSteps_L_eq (seq : InfSequent) :
    ∀ k n, (infSearchSteps seq k).L n = seq.antecedent (n + k + 1) := by
-- BEGIN PROOF
  intro k
  induction k with
  | zero => intro n; simp [infSearchSteps, infSearchInit, InfSeq.tail]
  | succ k ih =>
    intro n
    simp [infSearchSteps, infExpand, InfSeq.tail, ih n.succ]
    congr 1; omega

helper /-- Theorem 3.5.1 (required helper): The "R-sequence" of
    `infSearchSteps seq k` is `k`-shifted relative to `seq.succedent`:
    `(infSearchSteps seq k).R n = seq.succedent (n + k + 1)`. -/
theorem infSearchSteps_R_eq (seq : InfSequent) :
    ∀ k n, (infSearchSteps seq k).R n = seq.succedent (n + k + 1) := by
-- BEGIN PROOF
  intro k
  induction k with
  | zero => intro n; simp [infSearchSteps, infSearchInit, InfSeq.tail]
  | succ k ih =>
    intro n
    simp [infSearchSteps, infExpand, InfSeq.tail, ih n.succ]
    congr 1; omega

helper /-- Falsified leaves of a search stage are equivalent to falsification of
    the consumed finite input, although the tree's root stays fixed. -/
theorem infSearchSteps_falsification_iff (seq : InfSequent) (v : Valuation) : ∀ k,
    (∃ l ∈ (infSearchSteps seq k).tree.leaves, sequentFalsifiedBy l v) ↔
      sequentFalsifiedBy (Sequent.mk
        (initialPrefix seq.antecedent (k + 1))
        (initialPrefix seq.succedent (k + 1))) v := by
  intro k
  induction k with
  | zero =>
    cases hA : seq.antecedent 0 <;> cases hB : seq.succedent 0 <;>
      simp [infSearchSteps, infSearchInit, InfSeq.head, InfDeductionTree.leaves,
        initialPrefix, hA, hB]
  | succ k ih =>
    rw [infSearchSteps, infExpand_falsification_iff, ih,
      initialPrefix_succ_extend seq (k + 1), falsified_extendSeq_iff]
    simp only [InfSeq.head, infSearchSteps_L_eq, infSearchSteps_R_eq, Nat.zero_add]

helper /-- A falsifier of the input falsifies a leaf at each finite stage. -/
theorem infSearchSteps_leaf_falsifiedBy (seq : InfSequent) (v : Valuation)
    (hv : infSeqFalsifies v seq) :
    ∀ k, ∃ leaf ∈ (infSearchSteps seq k).tree.leaves, sequentFalsifiedBy leaf v := by
  intro k
  apply (infSearchSteps_falsification_iff seq v k).mpr
  have prefixTruth (f : Nat → Option PropFormulaNormalized) (b : BoolVal)
      (hf : ∀ n A, f n = some A → evalExtN v A = b) :
      ∀ n A, A ∈ initialPrefix f n → evalExtN v A = b := by
    intro n
    induction n with
    | zero => simp [initialPrefix]
    | succ n ih =>
      intro A hA
      cases hn : f n with
      | none => exact ih A (by simpa [initialPrefix, hn] using hA)
      | some B =>
        simp only [initialPrefix, hn, List.mem_append, List.mem_singleton] at hA
        rcases hA with hA | rfl
        · exact ih A hA
        · exact hf n A hn
  exact ⟨prefixTruth _ _ hv.1 _, prefixTruth _ _ hv.2 _⟩

helper /-- A closed stage proves its consumed finite support. Extension edges
    contribute assumptions to the support, rather than Gentzen rules. -/
theorem closed_tree_implies_initialPrefix_provable (seq : InfSequent) (k : Nat)
    (hClosed : isClosedTree (infSearchSteps seq k).tree) :
    sequentProvable (Sequent.mk
      (initialPrefix seq.antecedent (k + 1))
      (initialPrefix seq.succedent (k + 1))) := by
  apply completeness_G
  apply Classical.byContradiction
  intro hNotValid
  obtain ⟨v, hf⟩ := search_falsifying_extraction _ hNotValid
  obtain ⟨l, hl, hfl⟩ := (infSearchSteps_falsification_iff seq v k).mpr hf
  exact falsified_not_axiom l v hfl (hClosed l hl)

helper /-- Theorem 3.5.1 (required helper): If `seq` is infinite (not finite)
    and `infSearchSteps seq` halts (with the textbook-faithful
    `infIsFinishedTree` predicate: every leaf is axiom OR (L=R=empty AND
    all-atomic)), then it halts with a closed tree. Textbook: "if
    Γ → Δ is infinite, search terminates if and only if the tree is
    closed … any node that is not an axiom is not finished, since
    otherwise L and R would be empty, contradicting the fact that
    Γ → Δ is infinite."

    Proof: every leaf `s` of the tree satisfies either `isAxiom s` (we're
    done for that leaf) or `∀ n, state.L n = none ∧ state.R n = none ∧
    (...)`. In the latter case, `state.L n = seq.antecedent (n + k + 1)`
    by `infSearchSteps_L_eq`, so `seq.antecedent` is eventually `none`
    (bound `k + 1`). Similarly for R. Together, this says
    `infSeqIsFinite seq`, contradicting `hNotFin`. Hence the second
    disjunct is impossible and every leaf is an axiom, i.e.,
    `isClosedTree`. -/
theorem infinite_seq_halt_implies_closed (seq : InfSequent)
    (hNotFin : ¬ infSeqIsFinite seq) (k : Nat)
    (hFin : infIsFinishedTree (infSearchSteps seq k)) :
    isClosedTree (infSearchSteps seq k).tree := by
-- BEGIN PROOF
  intro s hs
  -- hFin s hs : infIsFinishedLeaf (infSearchSteps seq k) s
  -- = isAxiom s ∨ (∀ n, state.L n = none) ∧ (∀ n, state.R n = none) ∧ all-atomic
  rcases hFin s hs with hAx | ⟨hL, hR, _hAtom⟩
  · exact hAx
  · -- Derive a contradiction with hNotFin from L = R = empty eventually.
    exfalso; apply hNotFin
    refine ⟨⟨k + 1, ?_⟩, ⟨k + 1, ?_⟩⟩
    · -- seq.antecedent is eventually none from k+1 onward.
      intro n hn
      -- Use infSearchSteps_L_eq: (infSearchSteps seq k).L (n - k - 1) = seq.antecedent ((n - k - 1) + k + 1)
      -- Need to express seq.antecedent n in terms of state.L.
      have hLm := hL (n - (k + 1))
      rw [infSearchSteps_L_eq] at hLm
      -- hLm : seq.antecedent ((n - (k+1)) + k + 1) = none
      have hArith : n - (k + 1) + k + 1 = n := by omega
      rw [hArith] at hLm
      exact hLm
    · intro n hn
      have hRm := hR (n - (k + 1))
      rw [infSearchSteps_R_eq] at hRm
      have hArith : n - (k + 1) + k + 1 = n := by omega
      rw [hArith] at hRm
      exact hRm

helper /-- Appending empty heads adds an edge but does not change any leaf label. -/
theorem appendToLeavesCore_none_leaves {s : Sequent} (t : InfDeductionTree s) :
    (appendToLeavesCore t none none).leaves = t.leaves := by
  simp only [appendToLeavesCore, InfDeductionTree.leaves_bindLeaves]
  have hstep (l : Sequent) :
      (if isAxiomBool l then InfDeductionTree.leaf l
        else .extend none none (.leaf (extendSeq l none none))).leaves = [l] := by
    cases h : isAxiomBool l <;>
      simp [InfDeductionTree.leaves, extendSeq]
  simp only [hstep, List.flatMap_singleton']

helper /-- Maximum complexity of the unfinished labels of a finite search stage. -/
def infMaxUnfinishedComplexity (state : InfSearchState) : Nat :=
  ((state.tree.leaves.filter (fun s => !isFinishedLeafBool .systematic s)).map
    sequentComplexity).foldl max 0

helper /-- Once both streams are exhausted, every unfinished new leaf descends
    from an unfinished old leaf with strictly larger complexity. -/
theorem infExpand_unfinished_complexity (state : InfSearchState)
    (hL : InfSeq.head state.L = none) (hR : InfSeq.head state.R = none)
    (l : Sequent) (hl : l ∈ (infExpand state).tree.leaves)
    (hunf : isFinishedLeafBool .systematic l ≠ true) :
    sequentComplexity l < infMaxUnfinishedComplexity state := by
  simp only [infExpand, InfDeductionTree.leaves_bindLeaves, List.mem_flatMap] at hl
  obtain ⟨s, hs, hl⟩ := hl
  by_cases hfin : infIsFinishedLeafBool state s = true
  · simp only [hfin, ↓reduceIte, InfDeductionTree.leaves, List.mem_singleton] at hl
    subst l
    apply False.elim
    apply hunf
    apply (isFinishedLeafBool_iff s).mpr
    rcases (LCS.Propositional.Infinite.Proofs.infIsFinishedLeafBool_iff state s).mp hfin with hax | ⟨_, _, hatom⟩
    · exact Or.inl ⟨rfl, hax⟩
    · exact Or.inr hatom
  · simp only [hfin, Bool.false_eq_true, ↓reduceIte, hL, hR, appendToLeavesCore_none_leaves,
      LCS.Propositional.Infinite.Proofs.leaves_ofDeductionTree] at hl
    have hsUnf : isFinishedLeafBool .systematic s ≠ true := by
      intro hsfin
      apply hfin
      apply (LCS.Propositional.Infinite.Proofs.infIsFinishedLeafBool_iff state s).mpr
      rcases (isFinishedLeafBool_iff s).mp hsfin with ⟨_, hax⟩ | hatom
      · exact Or.inl hax
      · exact Or.inr ⟨(LCS.Propositional.Infinite.Proofs.noHoles_empty_iff state.L state.L_noHoles).mpr hL,
          (LCS.Propositional.Infinite.Proofs.noHoles_empty_iff state.R state.R_noHoles).mpr hR, hatom⟩
    have hsmem : s ∈ state.tree.leaves.filter (fun s => !isFinishedLeafBool .systematic s) := by
      simp only [List.mem_filter, Bool.not_eq_true']
      exact ⟨hs, Bool.eq_false_iff.mpr hsUnf⟩
    have hbound : sequentComplexity s ≤ infMaxUnfinishedComplexity state :=
      LCS.Propositional.Systems.G.Search.Proofs.le_foldl_max_of_mem (List.mem_map.mpr ⟨s, hsmem, rfl⟩)
    have hsmall := LCS.Propositional.Systems.G.Search.Proofs.searchRound_unfinished_lt_max (DeductionTree.leaf s)
      (by simpa [isFinishedTreeBool, DeductionTree.leaves] using hsUnf) l
      (by simp only [unfinishedLeaves, List.mem_filter, Bool.not_eq_true'];
          exact ⟨hl, Bool.eq_false_iff.mpr hunf⟩)
    have hbase : maxUnfinishedLeafComplexity .systematic (DeductionTree.leaf s) =
        sequentComplexity s := by
      simp [maxUnfinishedLeafComplexity, unfinishedLeaves,
        DeductionTree.leaves, Bool.eq_false_iff.mpr hsUnf]
    rw [hbase] at hsmall
    exact Nat.lt_of_lt_of_le hsmall hbound

helper /-- With empty tails, unfinished-stage complexity strictly decreases. -/
theorem infExpand_complexity_decrease (state : InfSearchState)
    (hL : InfSeq.head state.L = none) (hR : InfSeq.head state.R = none)
    (hunf : ¬ ∀ s ∈ state.tree.leaves, isFinishedLeaf .systematic s) :
    infMaxUnfinishedComplexity (infExpand state) < infMaxUnfinishedComplexity state := by
  have hpos : 0 < infMaxUnfinishedComplexity state := by
    obtain ⟨s, hs⟩ := Classical.not_forall.mp hunf
    have hmem : s ∈ state.tree.leaves := by
      exact Classical.byContradiction fun hnot =>
        hs (fun h => False.elim (hnot h))
    have hnot : isFinishedLeafBool .systematic s ≠ true := by
      intro h; exact hs (fun _ => (isFinishedLeafBool_iff s).mp h)
    have hspos := LCS.Propositional.Systems.G.Search.Proofs.unfinished_pos_complexity s hnot
    have hbound : sequentComplexity s ≤ infMaxUnfinishedComplexity state := by
      apply LCS.Propositional.Systems.G.Search.Proofs.le_foldl_max_of_mem
      apply List.mem_map.mpr
      exact ⟨s, by simp [List.mem_filter, hmem, Bool.eq_false_iff.mpr hnot], rfl⟩
    omega
  unfold infMaxUnfinishedComplexity
  by_cases hempty : ((infExpand state).tree.leaves.filter
      (fun s => !isFinishedLeafBool .systematic s)).map sequentComplexity = []
  · rw [hempty]
    exact hpos
  · apply LCS.Propositional.Systems.G.Search.Proofs.foldl_max_lt_of_all_lt hempty
    intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hs, hnot⟩ := List.mem_filter.mp hs
    exact infExpand_unfinished_complexity state hL hR s hs
      (by simpa only [Bool.not_eq_true', Bool.eq_false_iff] using hnot)

helper /-- Exhausted finite input reaches an all-finished stage by strict descent. -/
theorem finite_seq_halts_from_K (seq : InfSequent) :
    ∀ n K, (∀ k, k ≥ K → InfSeq.head (infSearchSteps seq k).L = none ∧
                          InfSeq.head (infSearchSteps seq k).R = none) →
    infMaxUnfinishedComplexity (infSearchSteps seq K) = n →
    ∃ k, k ≥ K ∧ ∀ s ∈ (infSearchSteps seq k).tree.leaves, isFinishedLeaf .systematic s := by
  intro n
  induction n using Nat.strongRecOn with | ind n ih =>
    intro K hhead hn
    by_cases hfin : ∀ s ∈ (infSearchSteps seq K).tree.leaves, isFinishedLeaf .systematic s
    · exact ⟨K, Nat.le_refl K, hfin⟩
    · have hheads := hhead K (Nat.le_refl K)
      have hdec := infExpand_complexity_decrease (infSearchSteps seq K)
        hheads.1 hheads.2 hfin
      have hlt : infMaxUnfinishedComplexity (infSearchSteps seq (K + 1)) < n := by
        change infMaxUnfinishedComplexity (infExpand (infSearchSteps seq K)) < n
        rw [← hn]
        exact hdec
      obtain ⟨k, hk, hf⟩ := ih _ hlt (K + 1) (fun k hk => hhead k (by omega)) rfl
      exact ⟨k, by omega, hf⟩

helper /-- Finite input exhausts its tails and then terminates by complexity descent. -/
theorem finite_seq_search_halts (seq : InfSequent)
    (hFin : infSeqIsFinite seq) :
    ∃ k, infIsFinishedTree (infSearchSteps seq k) := by
  obtain ⟨⟨N, hAnt⟩, ⟨M, hSuc⟩⟩ := hFin
  let K := max N M
  have htails : ∀ k, K ≤ k →
      (∀ n, (infSearchSteps seq k).L n = none) ∧
      (∀ n, (infSearchSteps seq k).R n = none) := by
    intro k hk
    constructor
    · intro n
      rw [infSearchSteps_L_eq]
      apply hAnt
      dsimp [K] at hk
      omega
    · intro n
      rw [infSearchSteps_R_eq]
      apply hSuc
      dsimp [K] at hk
      omega
  obtain ⟨k, hk, hf⟩ := finite_seq_halts_from_K seq _ K
    (fun k hk => ⟨(htails k hk).1 0, (htails k hk).2 0⟩) rfl
  refine ⟨k, fun s hs => ?_⟩
  rcases hf s hs with ⟨_, hax⟩ | hatom
  · exact Or.inl hax
  · exact Or.inr ⟨(htails k hk).1, (htails k hk).2, hatom⟩

helper /-- Theorem 3.5.1 (required helper): A formula appearing at position `n`
    in an `InfSeq` sits inside `initialPrefix s (k + 1)` whenever
    `n ≤ k`. Induction on `k`: the base case handles `n = 0`; the step
    case case-splits on `s (k+1)` — if `n ≤ k`, reuse IH; if `n = k + 1`,
    the match branch appends `A`. -/
theorem mem_initialPrefix_of_le
    (s : Nat → Option PropFormulaNormalized) (n : Nat) (A : PropFormulaNormalized)
    (hn : s n = some A) :
    ∀ k, n ≤ k → A ∈ initialPrefix s (k + 1) := by
-- BEGIN PROOF
  intro k
  induction k with
  | zero =>
    intro hle
    have hn0 : n = 0 := Nat.le_zero.mp hle
    subst hn0
    simp only [initialPrefix, hn, List.nil_append, List.mem_singleton]
  | succ k ih =>
    intro hle
    simp only [initialPrefix]
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hle' : n ≤ k := Nat.lt_succ_iff.mp hlt
      have hmem := ih hle'
      cases hc : s (k + 1) with
      | none => exact hmem
      | some B => exact List.mem_append_left _ hmem
    · have hn_eq : n = k + 1 := Nat.le_antisymm hle hge
      subst hn_eq
      rw [hn]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

helper /-- Theorem 3.5.1 (required helper): If `v` falsifies
    `Sequent.mk (initialPrefix seq.antecedent (k+1))
     (initialPrefix seq.succedent (k+1))` and the tails of
    `seq.antecedent` / `seq.succedent` are `none` from position `k+1`
    onward, then `v` falsifies the whole `seq`. Every formula
    appearing at position `n` in the antecedent must have `n ≤ k`
    (since position `k+1` onward is `none`), so `mem_initialPrefix_of_le`
    places it inside `initialPrefix seq.antecedent (k+1)`, where `v`
    sets it to T. Symmetric argument for the succedent. -/
theorem infSeqFalsifies_of_prefixFalsifiedBy
    (seq : InfSequent) (v : Valuation) (k : Nat)
    (hRootFals : sequentFalsifiedBy (Sequent.mk
      (initialPrefix seq.antecedent (k + 1))
      (initialPrefix seq.succedent (k + 1))) v)
    (hAntTail : ∀ n, n ≥ k + 1 → seq.antecedent n = none)
    (hSucTail : ∀ n, n ≥ k + 1 → seq.succedent n = none) :
    infSeqFalsifies v seq := by
-- BEGIN PROOF
  obtain ⟨hAntT, hSucF⟩ := hRootFals
  refine ⟨fun n A hn => ?_, fun n B hn => ?_⟩
  · have hnlt : n ≤ k := by
      rcases Nat.lt_or_ge k n with hge | hle
      · have hge' : n ≥ k + 1 := hge
        have hnone : seq.antecedent n = none := hAntTail n hge'
        exact absurd (hnone ▸ hn) (by simp)
      · exact hle
    exact hAntT A (mem_initialPrefix_of_le seq.antecedent n A hn k hnlt)
  · have hnlt : n ≤ k := by
      rcases Nat.lt_or_ge k n with hge | hle
      · have hge' : n ≥ k + 1 := hge
        have hnone : seq.succedent n = none := hSucTail n hge'
        exact absurd (hnone ▸ hn) (by simp)
      · exact hle
    exact hSucF B (mem_initialPrefix_of_le seq.succedent n B hn k hnlt)

helper /-- A falsifier of a finished open leaf falsifies the complete input.
    The consumed-prefix invariant accounts for all introduction edges. -/
theorem finished_leaf_falsifies_input (seq : InfSequent) (k : Nat)
    (hfinished : infIsFinishedTree (infSearchSteps seq k))
    (leaf : Sequent) (hmem : leaf ∈ (infSearchSteps seq k).tree.leaves)
    (v : Valuation) (hf : sequentFalsifiedBy leaf v) : infSeqFalsifies v seq := by
  have hprefix := (infSearchSteps_falsification_iff seq v k).mp ⟨leaf, hmem, hf⟩
  obtain ⟨hl, hr, _⟩ := (hfinished leaf hmem).resolve_left (falsified_not_axiom leaf v hf)
  apply infSeqFalsifies_of_prefixFalsifiedBy seq v k hprefix
  · intro n hn
    have h := hl (n - (k + 1))
    rw [infSearchSteps_L_eq] at h
    have heq : n - (k + 1) + k + 1 = n := by omega
    simpa only [heq] using h
  · intro n hn
    have h := hr (n - (k + 1))
    rw [infSearchSteps_R_eq] at h
    have heq : n - (k + 1) + k + 1 = n := by omega
    simpa only [heq] using h

helper /-- A finished nonclosed search stage supplies its actual terminal path,
    its Hintikka union, and the canonical countermodel of the complete input. -/
theorem finished_search_canonical_countermodel (seq : InfSequent) (k : Nat)
    (hfinished : infIsFinishedTree (infSearchSteps seq k))
    (hopen : ¬ isClosedTree (infSearchSteps seq k).tree) :
    ∃ leaf labels, SearchTreePath (infSearchSteps seq k).tree leaf labels ∧
      ¬ isAxiom leaf ∧ IsHintikkaSet (sequentListSignedSet labels) ∧
      infSeqFalsifies (hintikkaCanonicalValuation (sequentListSignedSet labels)) seq := by
  obtain ⟨leaf, labels, hp, hS⟩ :=
    finished_search_hintikka_set_extraction seq k hfinished hopen
  have hf := hp.canonical_falsifies_terminal hS
  exact ⟨leaf, labels, hp, falsified_not_axiom leaf _ hf, hS,
    finished_leaf_falsifies_input seq k hfinished leaf hp.leaf_mem _ hf⟩

helper /-- A valid finite input halts with a closed stage. An open atomic leaf
    would falsify the consumed prefix; exhausted tails then lift its
    valuation to a falsifier of the complete input. -/
theorem valid_implies_search_halts_closed_finite_case
    (seq : InfSequent) (hValid : infSeqValid seq)
    (hFinSeq : infSeqIsFinite seq) :
    ∃ k, infIsFinishedTree (infSearchSteps seq k) ∧
      isClosedTree (infSearchSteps seq k).tree := by
-- BEGIN PROOF
  obtain ⟨k, hFin⟩ := finite_seq_search_halts seq hFinSeq
  refine ⟨k, hFin, ?_⟩
  intro s hs
  exact Classical.byContradiction fun hNotAx => by
    rcases hFin s hs with hAx | ⟨hLall, hRall, hAtom⟩
    · exact hNotAx hAx
    -- Leaf is all-atomic but not an axiom ⇒ falsifiable (contrapositive
    -- of valid_atomic_is_axiom).
    have hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, ∃ n, A = .var n := by
      intro A hA
      have hat := hAtom A hA
      cases A with
      | var n => exact ⟨n, rfl⟩
      | _ => simp [isAtomicFormula] at hat
    have hNotValid : ¬ sequentValid s := fun hv =>
      hNotAx (LCS.Propositional.Systems.G.Search.Proofs.valid_atomic_is_axiom s hv hAllVar)
    obtain ⟨v, hvFalsLeaf⟩ := search_falsifying_extraction s hNotValid
    have hSeqFals := finished_leaf_falsifies_input seq k hFin s hs v hvFalsLeaf
    obtain ⟨hAntT, hSucF⟩ := hSeqFals
    obtain ⟨n, B, hn, hBT⟩ := hValid v hAntT
    have hBF := hSucF n B hn
    rw [hBT] at hBF; exact absurd hBF (by decide)

helper /-- Theorem 3.5.1: A valid infinite input eventually halts. Nontermination
    produces an actual infinite search path; its Hintikka union supplies a
    canonical countermodel, contradicting validity. -/
theorem infinite_valid_seq_search_halts
    (seq : InfSequent) (hValid : infSeqValid seq)
    (_hNotFin : ¬ infSeqIsFinite seq) :
    ∃ k, infIsFinishedTree (infSearchSteps seq k) := by
-- BEGIN PROOF
  apply Classical.byContradiction
  intro hnever
  obtain ⟨address, hp⟩ := infSearch_infinitePath_of_not_halts seq hnever
  obtain ⟨label, _, _, hf⟩ := infinite_search_path_canonical_countermodel seq address hp
  obtain ⟨n, B, hn, htrue⟩ := hValid _ hf.1
  have hfalse := hf.2 n B hn
  rw [htrue] at hfalse
  cases hfalse

helper /-- A valid infinite input halts, and an infinite input can halt only
    with every leaf closed. -/
theorem valid_implies_search_halts_closed_infinite_case
    (seq : InfSequent) (hValid : infSeqValid seq)
    (hNotFin : ¬ infSeqIsFinite seq) :
    ∃ k, infIsFinishedTree (infSearchSteps seq k) ∧
      isClosedTree (infSearchSteps seq k).tree := by
-- BEGIN PROOF
  obtain ⟨k, hFin⟩ := infinite_valid_seq_search_halts seq hValid hNotFin
  exact ⟨k, hFin, infinite_seq_halt_implies_closed seq hNotFin k hFin⟩

helper /-- Every valid input eventually yields a closed search stage. -/
theorem valid_implies_search_halts_closed (seq : InfSequent)
    (hValid : infSeqValid seq) :
    ∃ k, infIsFinishedTree (infSearchSteps seq k) ∧
      isClosedTree (infSearchSteps seq k).tree := by
-- BEGIN PROOF
  rcases Classical.em (infSeqIsFinite seq) with hFin | hNotFin
  · exact valid_implies_search_halts_closed_finite_case seq hValid hFin
  · exact valid_implies_search_halts_closed_infinite_case seq hValid hNotFin

proof_of search_theorem_3_5_1 := by
  -- BEGIN PROOF
    rcases em (infSeqValid seq) with hValid | hNotValid
    · right
      obtain ⟨k, hFin, hClosed⟩ := valid_implies_search_halts_closed seq hValid
      exact ⟨hValid, k, hFin, hClosed,
        closed_tree_implies_initialPrefix_provable seq k hClosed⟩
    · left
      obtain ⟨v, hv⟩ := LCS.Propositional.Infinite.SignedFormulae.Proofs.falsifying_valuation_from_path seq hNotValid
      have hopen (k : Nat) : ¬ isClosedTree (infSearchSteps seq k).tree := by
        intro hclosed
        obtain ⟨leaf, hmem, hf⟩ := infSearchSteps_leaf_falsifiedBy seq v hv k
        exact falsified_not_axiom leaf v hf (hclosed leaf hmem)
      refine ⟨⟨v, hv⟩, ?_, ?_⟩
      · intro hNotFin
        have hnever : ¬ infSearchHalts seq := by
          rintro ⟨k, hfinished⟩
          exact hopen k (infinite_seq_halt_implies_closed seq hNotFin k hfinished)
        obtain ⟨address, hp⟩ := infSearch_infinitePath_of_not_halts seq hnever
        obtain ⟨label, hl, hS, hf⟩ := infinite_search_path_canonical_countermodel seq address hp
        exact ⟨hnever, LCS.Propositional.Infinite.Proofs.infSearch_infinite_of_not_halts seq hnever, address, label, hp, hl, hS, hf⟩
      · intro hFinite
        obtain ⟨k, hfinished⟩ := finite_seq_search_halts seq hFinite
        obtain ⟨leaf, labels, hp, ho, hS, hf⟩ :=
          finished_search_canonical_countermodel seq k hfinished (hopen k)
        exact ⟨k, leaf, labels, hfinished, hp, ho, hS, hf⟩


proof_of extended_completeness_G := ⟨fun h => valid_sequent_provable seq h,
  -- BEGIN PROOF
     infSeqProvable_implies_valid seq⟩


end LCS.Propositional.Infinite.SignedFormulae
