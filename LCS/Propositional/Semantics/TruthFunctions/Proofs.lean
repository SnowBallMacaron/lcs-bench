import LCS.Propositional.Semantics.TruthFunctions

namespace LCS.Propositional.Semantics.TruthFunctions

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

proof_of xorFormula_is_hXor := by
  -- BEGIN PROOF
    cases a <;> cases b <;> rfl


helper /-- Extend an assignment on Fin n to Fin (n+1) by appending a value at position n. -/
def extendAssign {n : Nat} (a : Fin n → BoolVal) (b : BoolVal) :
    Fin (n + 1) → BoolVal :=
  fun i => if h : i.val < n then a ⟨i.val, h⟩ else b

helper theorem extendAssign_init {n : Nat} (a : Fin n → BoolVal) (b : BoolVal)
    (i : Fin n) : extendAssign a b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩ = a i := by
-- BEGIN PROOF
  simp [extendAssign, i.isLt]

helper theorem extendAssign_last {n : Nat} (a : Fin n → BoolVal) (b : BoolVal) :
    extendAssign a b ⟨n, Nat.lt_succ_self _⟩ = b := by
-- BEGIN PROOF
  simp [extendAssign, Nat.lt_irrefl]

helper /-- Shannon expansion witness: build a formula using only var, neg, conj, disj
    that computes the same truth function as f, using variables 0..n-1.
    Uses Shannon decomposition: f(x₀,...,xₙ) = (xₙ ∧ f[xₙ:=T]) ∨ (¬xₙ ∧ f[xₙ:=F]). -/
def shannonFormula : (n : Nat) → (f : TruthFn n) → PropFormula
  | 0, f =>
    match f Fin.elim0 with
    | .T => PropFormula.disj (.var 0) (.neg (.var 0))  -- tautology (propTop)
    | .F => PropFormula.conj (.var 0) (.neg (.var 0))  -- contradiction
  | n + 1, f =>
    let fT : TruthFn n := fun a => f (extendAssign a .T)
    let fF : TruthFn n := fun a => f (extendAssign a .F)
    let AT := shannonFormula n fT
    let AF := shannonFormula n fF
    .disj (.conj (.var n) AT) (.conj (.neg (.var n)) AF)

helper /-- Helper: `eraseDups` always produces a `Nodup` list. -/
theorem eraseDups_nodup (L : List Nat) : L.eraseDups.Nodup := by
-- BEGIN PROOF
  induction hn : L.length using Nat.strongRecOn generalizing L with
  | _ n ih =>
    match L, hn with
    | [], _ => simp [List.eraseDups_nil]
    | hd :: tl, hlen =>
      rw [List.eraseDups_cons]
      simp only [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hcon
        rw [List.mem_eraseDups, List.mem_filter] at hcon
        simp at hcon
      · apply ih _ _ _ rfl
        have : (tl.filter (fun b => !b == hd)).length ≤ tl.length := List.length_filter_le _ _
        simp at hlen; omega

helper /-- Helper: a list that is `Pairwise (· ≤ ·)` and `Nodup` is `Pairwise (· < ·)`. -/
theorem pairwise_le_and_nodup_imp_pairwise_lt (L : List Nat)
    (hle : L.Pairwise (· ≤ ·)) (hnd : L.Nodup) : L.Pairwise (· < ·) := by
-- BEGIN PROOF
  induction L with
  | nil => simp
  | cons a tl ih =>
    rcases hle with _ | ⟨hlehead, hletail⟩
    rcases hnd with _ | ⟨hndhead, hndtail⟩
    constructor
    · intro b hb
      have hle := hlehead b hb
      have hne : a ≠ b := hndhead b hb
      omega
    · exact ih hletail hndtail

helper /-- Helper: a `Pairwise (· < ·)` list whose membership is `x ↔ x < k`
    equals `List.range k`. -/
theorem nodup_sorted_range_eq (L : List Nat) (k : Nat)
    (hmem : ∀ x, x ∈ L ↔ x < k)
    (hpw : L.Pairwise (· < ·)) : L = List.range k := by
-- BEGIN PROOF
  apply List.Perm.eq_of_pairwise (le := (· < ·))
  · intros a b _ _ hab hba; omega
  · exact hpw
  · exact List.pairwise_lt_range
  · apply List.perm_iff_count.mpr
    intro a
    have hLnd : L.Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
    have hRnd : (List.range k).Nodup := List.nodup_range
    rw [List.Nodup.count hLnd, List.Nodup.count hRnd]
    by_cases hmm : a ∈ L
    · rw [if_pos hmm, if_pos ((List.mem_range).mpr ((hmem a).mp hmm))]
    · rw [if_neg hmm, if_neg (fun h => hmm ((hmem a).mpr ((List.mem_range).mp h)))]

helper /-- Helper: `mergeSort` of `eraseDups` produces a `Pairwise (· < ·)` list. -/
theorem pairwise_lt_mergeSort_eraseDups (L : List Nat) :
    (L.eraseDups.mergeSort (· ≤ ·)).Pairwise (· < ·) := by
-- BEGIN PROOF
  apply pairwise_le_and_nodup_imp_pairwise_lt
  · have hpw := @List.pairwise_mergeSort _
      (fun a b => decide ((a : Nat) ≤ b))
      (fun a b c ha hb => by simp at *; omega)
      (fun a b => by simp; omega)
      L.eraseDups
    apply hpw.imp
    intros a b h; simp at h; exact h
  · apply List.Perm.nodup (List.Perm.symm (List.mergeSort_perm L.eraseDups _))
    exact eraseDups_nodup L

helper /-- The Shannon witness at level `n+1` uses exactly variables
    `{0, 1, ..., n}`, so its `varList` is `List.range (n+1)`.
    This is the key identity that feeds both the length statement and
    the transport computation in `functional_completeness`. -/
theorem shannonFormula_varList_eq_range : (n : Nat) → (f : TruthFn (n+1)) →
    varList (shannonFormula (n+1) f) = List.range (n+1)
  | 0, f => by
    simp only [shannonFormula]
    cases (f (extendAssign Fin.elim0 .T)) <;>
    cases (f (extendAssign Fin.elim0 .F)) <;>
      simp [varList, List.eraseDups_cons]
  | n+1, f => by
    have hT := shannonFormula_varList_eq_range n (fun a => f (extendAssign a .T))
    have hF := shannonFormula_varList_eq_range n (fun a => f (extendAssign a .F))
    show varList (shannonFormula (n+2) f) = List.range (n+2)
    rw [show shannonFormula (n+2) f =
        .disj (.conj (.var (n+1)) (shannonFormula (n+1) fun a => f (extendAssign a .T)))
              (.conj (.neg (.var (n+1))) (shannonFormula (n+1) fun a => f (extendAssign a .F)))
        from rfl]
    simp only [varList]
    rw [hT, hF]
    apply nodup_sorted_range_eq
    · intro x
      simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_append,
                 List.mem_singleton, List.mem_range]
      omega
    · exact pairwise_lt_mergeSort_eraseDups _

helper /-- The Shannon witness for an n-ary truth function (for n ≥ 1) uses
    exactly the variables `{0, 1, ..., n-1}`, so its `varList` has
    length `n`. The `n ≥ 1` hypothesis rules out the degenerate n=0
    case where `shannonFormula 0 f` still emits a 1-variable formula.
    Proof: structural induction on n, showing the Shannon recursion at
    level `n+1` introduces `.var n` and recurses into two `shannonFormula n`
    calls that contribute `{0,...,n-1}`. After `.eraseDups` +
    `.mergeSort`, the result is `[0,...,n]`. -/
theorem shannonFormula_varList_length :
    (n : Nat) → (hn : n ≥ 1) → (f : TruthFn n) →
    (varList (shannonFormula n f)).length = n := by
-- BEGIN PROOF
  intros n hn f
  cases n with
  | zero => omega
  | succ m =>
    rw [shannonFormula_varList_eq_range m f]
    exact List.length_range

helper /-- Helper: `findIdx? (· == m)` on `List.range n` returns `some m` when `m < n`. -/
theorem findIdx?_range_some (n m : Nat) (hmlt : m < n) :
    (List.range n).findIdx? (· == m) = some m := by
-- BEGIN PROOF
  apply List.findIdx?_eq_some_iff_findIdx_eq.mpr
  refine ⟨by rw [List.length_range]; exact hmlt, ?_⟩
  rw [List.findIdx_eq (by rw [List.length_range]; exact hmlt)]
  refine ⟨?_, ?_⟩
  · rw [List.getElem_range]; simp
  · intro j hji
    rw [List.getElem_range]
    simp; omega

helper /-- Helper: `findIdx? (· == m)` on `List.range n` returns `none` when `m ≥ n`. -/
theorem findIdx?_range_none (n m : Nat) (hmge : m ≥ n) :
    (List.range n).findIdx? (· == m) = none := by
-- BEGIN PROOF
  apply List.findIdx?_eq_none_iff.mpr
  intro x hx
  rw [List.mem_range] at hx
  simp; omega

helper theorem shannonFormula_usesOnlyAndOrNeg :
    (n : Nat) → (f : TruthFn n) → usesOnlyAndOrNeg (shannonFormula n f)
  | 0, f => by
    simp only [shannonFormula]
    cases f Fin.elim0 <;> simp [usesOnlyAndOrNeg]
  | n + 1, f => by
    simp only [shannonFormula, usesOnlyAndOrNeg]
    exact ⟨⟨trivial, shannonFormula_usesOnlyAndOrNeg n _⟩,
           ⟨trivial, shannonFormula_usesOnlyAndOrNeg n _⟩⟩

helper /-- The shannonFormula for n only uses variables 0..n-1, so its evaluation
    under any valuation depends only on the values at those indices. -/
theorem shannonFormula_vars_lt :
    (n : Nat) → (f : TruthFn n) → (v v' : Valuation) →
    (∀ i, i < n → v i = v' i) →
    evalExt v (shannonFormula n f) = evalExt v' (shannonFormula n f)
  | 0, f, v, v', _ => by
    simp only [shannonFormula]
    cases f Fin.elim0 <;> simp only [evalExt, hOr, hNeg, hAnd] <;>
      (cases v 0 <;> cases v' 0 <;> rfl)
  | n + 1, f, v, v', hagree => by
    simp only [shannonFormula, evalExt]
    have hvn : v n = v' n := hagree n (Nat.lt_succ_self _)
    have hsub : ∀ i, i < n → v i = v' i :=
-- BEGIN PROOF
      fun i hi => hagree i (Nat.lt_of_lt_of_le hi (Nat.le_succ _))
    exact congr (congrArg hOr
      (congr (congrArg hAnd hvn) (shannonFormula_vars_lt n _ v v' hsub)))
      (congr (congrArg hAnd (congrArg hNeg hvn)) (shannonFormula_vars_lt n _ v v' hsub))

helper /-- Key lemma: shannonFormula evaluates correctly. -/
theorem shannonFormula_correct :
    (n : Nat) → (f : TruthFn n) → (assignment : Fin n → BoolVal) →
    f assignment =
      evalExt (fun i => if h : i < n then assignment ⟨i, h⟩ else BoolVal.F)
        (shannonFormula n f)
  | 0, f, assignment => by
    simp only [shannonFormula]
    have : assignment = Fin.elim0 := funext (fun i => Fin.elim0 i)
    subst this
    cases hf : f Fin.elim0 with
    | T =>
      simp only [evalExt, hOr, hNeg]
      cases (if h : (0 : Nat) < 0 then Fin.elim0 ⟨0, h⟩ else BoolVal.F) <;> rfl
    | F =>
      simp only [evalExt, hAnd, hNeg]
      cases (if h : (0 : Nat) < 0 then Fin.elim0 ⟨0, h⟩ else BoolVal.F) <;> rfl
  | n + 1, f, assignment => by
    -- Define shorthands
    let v : Valuation := fun i => if h : i < n + 1 then assignment ⟨i, h⟩ else BoolVal.F
    let lastVal := assignment ⟨n, Nat.lt_succ_self n⟩
    let fT : TruthFn n := fun a => f (extendAssign a .T)
    let fF : TruthFn n := fun a => f (extendAssign a .F)
    let initAssign : Fin n → BoolVal :=
-- BEGIN PROOF
      fun i => assignment ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩
    -- The sub-valuation for n variables
    let vSub : Valuation := fun i => if h : i < n then initAssign ⟨i, h⟩ else BoolVal.F
    -- IH gives us results in terms of vSub
    have ihT : fT initAssign = evalExt vSub (shannonFormula n fT) :=
      shannonFormula_correct n fT initAssign
    have ihF : fF initAssign = evalExt vSub (shannonFormula n fF) :=
      shannonFormula_correct n fF initAssign
    -- vSub and v agree on 0..n-1
    have hv_agree : ∀ i, i < n → vSub i = v i := by
      intro i hi
      simp only [vSub, v, initAssign]
      simp [hi, Nat.lt_of_lt_of_le hi (Nat.le_succ _)]
    -- So shannonFormula n fT/fF evaluates the same under vSub and v
    have ihT' : fT initAssign = evalExt v (shannonFormula n fT) := by
      rw [ihT]; exact shannonFormula_vars_lt n fT vSub v hv_agree
    have ihF' : fF initAssign = evalExt v (shannonFormula n fF) := by
      rw [ihF]; exact shannonFormula_vars_lt n fF vSub v hv_agree
    -- assignment = extendAssign initAssign lastVal
    have hassign : f assignment = f (extendAssign initAssign lastVal) := by
      congr 1; funext ⟨i, hi⟩
      simp only [extendAssign, initAssign, lastVal]
      by_cases heq : i < n
      · simp [heq]
      · simp only [heq, dite_false]
        have : i = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp heq)
        subst this; rfl
    -- v n = lastVal
    have hv_n : v n = lastVal := by
      simp only [v, lastVal]; simp
    -- Unfold evalExt on the Shannon formula
    have heval : evalExt v (shannonFormula (n + 1) f) =
        hOr (hAnd (v n) (evalExt v (shannonFormula n fT)))
            (hAnd (hNeg (v n)) (evalExt v (shannonFormula n fF))) := by
      simp [shannonFormula, evalExt, fT, fF]
    -- Now connect f assignment to evalExt v (shannonFormula (n+1) f)
    rw [hassign, heval, hv_n]
    -- Rewrite IH to get concrete BoolVal equalities
    have ihT_eq : evalExt v (shannonFormula n fT) = fT initAssign := ihT'.symm
    have ihF_eq : evalExt v (shannonFormula n fF) = fF initAssign := ihF'.symm
    cases hlast : lastVal with
    | T =>
      -- Goal: f(extend init T) = hOr(hAnd(T, evalT))(hAnd(hNeg T, evalF))
      --     = hOr(hAnd(T, fT init))(hAnd(F, fF init))
      rw [ihT_eq, ihF_eq]
      simp only [fT]
      -- Now: f(extend init T) = hOr(hAnd(T, f(extend init T)))(hAnd(F, fF init))
      cases f (extendAssign initAssign .T) <;>
        cases fF initAssign <;> rfl
    | F =>
      rw [ihT_eq, ihF_eq]
      simp only [fF]
      cases fT initAssign <;>
        cases f (extendAssign initAssign .F) <;> rfl

proof_of functional_completeness := by
  -- BEGIN PROOF
    by_cases hzero : n = 0
    · subst n
      have hconst (assignment : Fin 0 → BoolVal) : f assignment = f Fin.elim0 := by
        congr 1
        funext i
        exact Fin.elim0 i
      cases hval : f Fin.elim0 with
      | T =>
        refine ⟨.neg .fls, trivial, rfl, ?_⟩
        funext assignment
        exact (hconst assignment).trans hval
      | F =>
        refine ⟨.fls, trivial, rfl, ?_⟩
        funext assignment
        exact (hconst assignment).trans hval
    have hn : n ≥ 1 := by omega
    refine ⟨shannonFormula n f, shannonFormula_usesOnlyAndOrNeg n f, ?_⟩
    have hvl : (varList (shannonFormula n f)).length = n :=
      shannonFormula_varList_length n hn f
    refine ⟨hvl, ?_⟩
    funext assignment
    have hvars : varList (shannonFormula n f) = List.range n := by
      cases n with
      | zero => omega
      | succ m => exact shannonFormula_varList_eq_range m f
    rw [shannonFormula_correct n f assignment]
    symm
    generalize hB : shannonFormula n f = B at *
    have trans_eq : (hvl ▸ H_A B) assignment =
        H_A B (hvl.symm ▸ assignment) := by
      subst hvl
      rfl
    rw [trans_eq]
    clear trans_eq
    unfold H_A truthFunction
    revert hvl
    rw [hvars]
    intro hvl
    apply evalExt_depends_on_vars
    intro mm hmm
    by_cases hmmlt : mm < n
    · rw [findIdx?_range_some n mm hmmlt]
      simp only [hmmlt, dite_true]
      split
      · rename_i hmmlen
        have : (hvl.symm ▸ assignment) ⟨mm, hmmlen⟩ = assignment ⟨mm, hmmlt⟩ := by
          generalize hk : (List.range n).length = k at hvl hmmlen
          subst hvl
          rfl
        exact this
      · rename_i h_imp
        exfalso
        rw [List.length_range] at h_imp
        exact h_imp hmmlt
    · rw [findIdx?_range_none n mm (Nat.not_lt.mp hmmlt)]
      simp only [hmmlt, dite_false]


helper /-- Lemma 3.3.3 (required helper): Every propositional symbol occurring in A
    (in the `formulaVars` sense) appears in `varList A` (the sorted-with-dups-
    removed list of symbol indices). Bridges the `Set`-based `formulaVars`
    used by Lemma 3.3.1 with the `List`-based `varList` used by Definition 3.3.5. -/
theorem formulaVars_mem_varList (A : PropFormula) (n : Nat)
    (h : formulaVars A n) : n ∈ varList A := by
-- BEGIN PROOF
  induction A with
  | var m =>
    simp only [formulaVars] at h
    subst h; simp [varList]
  | fls => exact absurd h id
  | neg A ih =>
    simp only [formulaVars] at h
    simp only [varList]; exact ih h
  | conj A B ihA ihB =>
    simp only [formulaVars] at h
    simp only [varList, List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
    cases h with
    | inl hA => exact Or.inl (ihA hA)
    | inr hB => exact Or.inr (ihB hB)
  | disj A B ihA ihB =>
    simp only [formulaVars] at h
    simp only [varList, List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
    cases h with
    | inl hA => exact Or.inl (ihA hA)
    | inr hB => exact Or.inr (ihB hB)
  | impl A B ihA ihB =>
    simp only [formulaVars] at h
    simp only [varList, List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
    cases h with
    | inl hA => exact Or.inl (ihA hA)
    | inr hB => exact Or.inr (ihB hB)
  | equiv_ A B ihA ihB =>
    simp only [formulaVars] at h
    simp only [varList, List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
    cases h with
    | inl hA => exact Or.inl (ihA hA)
    | inr hB => exact Or.inr (ihB hB)

helper /-- Lemma 3.3.3 (required helper): Applying the truth function
    `truthFunction vars A` at the canonical assignment `i ↦ v (vars[i])`
    reproduces the direct evaluation `evalExt v A`, provided every variable
    occurring in A is present in `vars`. This is the key bridge between
    the "pointwise equal evaluations" statement and the "equal truth functions"
    statement in Lemma 3.3.3. -/
theorem truthFunction_apply_valuation (vars : List Nat) (A : PropFormula)
    (v : Valuation) (hA : ∀ n, formulaVars A n → n ∈ vars) :
    truthFunction vars A (fun i => v (vars.get i)) = evalExt v A := by
-- BEGIN PROOF
  unfold truthFunction
  apply evalExt_depends_on_vars
  intro n hn
  have hmem : n ∈ vars := hA n hn
  have hxp : ∃ x, x ∈ vars ∧ (x == n) = true := ⟨n, hmem, by simp⟩
  have hlt : vars.findIdx (· == n) < vars.length :=
    List.findIdx_lt_length.mpr hxp
  have hfi : vars.findIdx? (· == n) = some (vars.findIdx (· == n)) :=
    List.findIdx?_eq_some_iff_findIdx_eq.mpr ⟨hlt, rfl⟩
  rw [hfi]
  simp only [hlt, dite_true]
  congr 1
  rw [List.get_eq_getElem]
  have h1 : ((vars[vars.findIdx (· == n)]'hlt) == n) = true :=
    List.findIdx_getElem (w := hlt)
  exact (beq_iff_eq ..).mp h1

proof_of tautological_equiv_iff_equal_eval := by
  -- BEGIN PROOF
    have part1 : isValid (.equiv_ A B) ↔
        ∀ v : Valuation, evalExt v A = evalExt v B := by
      constructor
      · intro h v
        have hv := h v
        simp only [evalExt, hEquiv] at hv
        cases heqA : evalExt v A <;> cases heqB : evalExt v B <;> simp_all
      · intro h v
        simp only [evalExt, hEquiv]
        rw [h v]
        cases evalExt v B <;> rfl
    refine ⟨part1, ?_⟩
    constructor
    · intro hValid
      have hp := part1.mp hValid
      funext assignment
      unfold truthFunction
      exact hp _
    · intro hFn
      rw [part1]
      intro v
      have hA_sub : ∀ n, formulaVars A n → n ∈ varList (.equiv_ A B) := by
        intro n hn
        apply formulaVars_mem_varList
        simp only [formulaVars]; exact Or.inl hn
      have hB_sub : ∀ n, formulaVars B n → n ∈ varList (.equiv_ A B) := by
        intro n hn
        apply formulaVars_mem_varList
        simp only [formulaVars]; exact Or.inr hn
      have eqA := truthFunction_apply_valuation (varList (.equiv_ A B)) A v hA_sub
      have eqB := truthFunction_apply_valuation (varList (.equiv_ A B)) B v hB_sub
      rw [← eqA, ← eqB, hFn]


proof_of equiv_impl_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hImplies]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of impl_disj_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hImplies, hOr, hNeg]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of disj_impl_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, hImplies, hNeg]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of disj_demorgan_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, hNeg, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of conj_demorgan_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hNeg, hOr]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of neg_falsum_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hNeg, hImplies]
    cases evalExt v A <;> rfl


proof_of falsum_contradiction_tautology := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hNeg]
    cases evalExt v A <;> rfl


proof_of lemma_3_3_4 := ⟨equiv_impl_tautology A B, impl_disj_tautology A B,
  -- BEGIN PROOF
     disj_impl_tautology A B, disj_demorgan_tautology A B,
     conj_demorgan_tautology A B, neg_falsum_tautology A,
     falsum_contradiction_tautology A⟩


proof_of logEquiv_congruence_neg := by
  -- BEGIN PROOF
    have hA' := (tautological_equiv_iff_equal_eval A A').1.mp hA
    intro v; simp only [evalExt, hEquiv, hNeg]; rw [hA' v]
    cases evalExt v A' <;> rfl


proof_of logEquiv_congruence_conj := by
  -- BEGIN PROOF
    have hA' := (tautological_equiv_iff_equal_eval A A').1.mp hA
    have hB' := (tautological_equiv_iff_equal_eval B B').1.mp hB
    intro v; simp only [evalExt, hEquiv, hAnd]; rw [hA' v, hB' v]
    cases evalExt v A' <;> cases evalExt v B' <;> rfl


proof_of logEquiv_congruence_disj := by
  -- BEGIN PROOF
    have hA' := (tautological_equiv_iff_equal_eval A A').1.mp hA
    have hB' := (tautological_equiv_iff_equal_eval B B').1.mp hB
    intro v; simp only [evalExt, hEquiv, hOr]; rw [hA' v, hB' v]
    cases evalExt v A' <;> cases evalExt v B' <;> rfl


proof_of logEquiv_congruence_impl := by
  -- BEGIN PROOF
    have hA' := (tautological_equiv_iff_equal_eval A A').1.mp hA
    have hB' := (tautological_equiv_iff_equal_eval B B').1.mp hB
    intro v; simp only [evalExt, hEquiv, hImplies]; rw [hA' v, hB' v]
    cases evalExt v A' <;> cases evalExt v B' <;> rfl


proof_of logEquiv_congruence_equiv := by
  -- BEGIN PROOF
    have hA' := (tautological_equiv_iff_equal_eval A A').1.mp hA
    have hB' := (tautological_equiv_iff_equal_eval B B').1.mp hB
    intro v; simp only [evalExt, hEquiv]; rw [hA' v, hB' v]
    cases evalExt v A' <;> cases evalExt v B' <;> rfl


proof_of logEquiv_disj_assoc := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr]
    cases evalExt v A <;> cases evalExt v B <;> cases evalExt v C <;> rfl


proof_of logEquiv_conj_assoc := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> cases evalExt v C <;> rfl


proof_of logEquiv_disj_comm := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_conj_comm := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_disj_conj_distrib := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> cases evalExt v C <;> rfl


proof_of logEquiv_conj_disj_distrib := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hOr]
    cases evalExt v A <;> cases evalExt v B <;> cases evalExt v C <;> rfl


proof_of logEquiv_demorgan_disj := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hNeg, hOr, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_demorgan_conj := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hNeg, hAnd, hOr]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_disj_idempotent := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr]
    cases evalExt v A <;> rfl


proof_of logEquiv_conj_idempotent := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd]
    cases evalExt v A <;> rfl


proof_of logEquiv_double_neg := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hNeg]
    cases evalExt v A <;> rfl


proof_of logEquiv_disj_absorption := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, hAnd]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_conj_absorption := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hOr]
    cases evalExt v A <;> cases evalExt v B <;> rfl


proof_of logEquiv_disj_identity := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr]
    cases evalExt v A <;> rfl


proof_of logEquiv_conj_annihilation := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd]
    cases evalExt v A <;> rfl


proof_of logEquiv_disj_top := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, propTop, hNeg]
    cases evalExt v A <;> cases v 0 <;> rfl


proof_of logEquiv_conj_identity_top := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, propTop, hOr, hNeg]
    cases evalExt v A <;> cases v 0 <;> rfl


proof_of logEquiv_excluded_middle := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hOr, hNeg, propTop]
    cases evalExt v A <;> cases v 0 <;> rfl


proof_of logEquiv_contradiction := by
  -- BEGIN PROOF
    intro v; simp only [evalExt, hEquiv, hAnd, hNeg]
    cases evalExt v A <;> rfl


namespace PropFormulaExtended

proof_of logEquivIffEqualEval := by
  rw [logEquivIffTranslated]
  unfold LCS.Propositional.Semantics.TruthFunctions.logEquiv
  rw [(tautological_equiv_iff_equal_eval A.toFormula B.toFormula).1]
  simp only [evalEqToFormula]


proof_of congruenceNeg := by
  apply (logEquivIffEqualEval _ _).mpr
  have hA := (logEquivIffEqualEval A A').mp hA
  intro v
  exact congrArg hNeg (hA v)


proof_of congruenceConj := by
  apply (logEquivIffEqualEval _ _).mpr
  have hA := (logEquivIffEqualEval A A').mp hA
  have hB := (logEquivIffEqualEval B B').mp hB
  intro v
  simp only [eval, hA v, hB v]


proof_of congruenceDisj := by
  apply (logEquivIffEqualEval _ _).mpr
  have hA := (logEquivIffEqualEval A A').mp hA
  have hB := (logEquivIffEqualEval B B').mp hB
  intro v
  simp only [eval, hA v, hB v]


proof_of logEquiv_disj_assoc := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_assoc A.toFormula B.toFormula C.toFormula)


proof_of logEquiv_conj_assoc := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_assoc A.toFormula B.toFormula C.toFormula)


proof_of logEquiv_disj_comm := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_comm A.toFormula B.toFormula)


proof_of logEquiv_conj_comm := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_comm A.toFormula B.toFormula)


proof_of logEquiv_disj_conj_distrib := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_conj_distrib A.toFormula B.toFormula C.toFormula)


proof_of logEquiv_conj_disj_distrib := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_disj_distrib A.toFormula B.toFormula C.toFormula)


proof_of logEquiv_demorgan_disj := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_demorgan_disj A.toFormula B.toFormula)


proof_of logEquiv_demorgan_conj := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_demorgan_conj A.toFormula B.toFormula)


proof_of logEquiv_disj_idempotent := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_idempotent A.toFormula)


proof_of logEquiv_conj_idempotent := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_idempotent A.toFormula)


proof_of logEquiv_double_neg := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_double_neg A.toFormula)


proof_of logEquiv_disj_absorption := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_absorption A.toFormula B.toFormula)


proof_of logEquiv_conj_absorption := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_absorption A.toFormula B.toFormula)


proof_of logEquiv_disj_identity := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_identity A.toFormula)


proof_of logEquiv_conj_annihilation := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_annihilation A.toFormula)


proof_of logEquiv_disj_top := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_disj_top A.toFormula)


proof_of logEquiv_conj_identity_top := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_conj_identity_top A.toFormula)


proof_of logEquiv_excluded_middle := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_excluded_middle A.toFormula)


proof_of logEquiv_contradiction := (logEquivIffTranslated _ _).mpr
    (LCS.Propositional.Semantics.TruthFunctions.logEquiv_contradiction A.toFormula)


end PropFormulaExtended

namespace BProp

proof_of ofFormulaEqIff := ⟨Quotient.exact, fun h => @Quotient.sound _ logEquivSetoid A B h⟩


proof_of addOfFormula := rfl


proof_of mulOfFormula := rfl


proof_of negOfFormula := rfl


proof_of addAssoc := Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (PropFormulaExtended.logEquiv_disj_assoc A B C))


proof_of mulAssoc := Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (PropFormulaExtended.logEquiv_conj_assoc A B C))


proof_of addComm := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_disj_comm A B))


proof_of mulComm := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_conj_comm A B))


proof_of addMulDistrib := Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (PropFormulaExtended.logEquiv_disj_conj_distrib A B C))


proof_of mulAddDistrib := Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (PropFormulaExtended.logEquiv_conj_disj_distrib A B C))


proof_of negAdd := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_demorgan_disj A B))


proof_of negMul := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_demorgan_conj A B))


proof_of addIdempotent := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_disj_idempotent A))


proof_of mulIdempotent := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_conj_idempotent A))


proof_of negNeg := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_double_neg A))


proof_of addAbsorption := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_disj_absorption A B))


proof_of mulAbsorption := Quotient.inductionOn₂ a b (fun A B => Quotient.sound (PropFormulaExtended.logEquiv_conj_absorption A B))


proof_of addZero := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_disj_identity A))


proof_of mulZero := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_conj_annihilation A))


proof_of addOne := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_disj_top A))


proof_of mulOne := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_conj_identity_top A))


proof_of addNeg := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_excluded_middle A))


proof_of mulNeg := Quotient.inductionOn a (fun A => Quotient.sound (PropFormulaExtended.logEquiv_contradiction A))


proof_of zeroNeOne := by
  intro h
  have hEquiv := (ofFormulaEqIff .fls .top).mp h
  have hEval := (PropFormulaExtended.logEquivIffEqualEval .fls .top).mp hEquiv
    (fun _ => BoolVal.F)
  cases hEval


end BProp

end LCS.Propositional.Semantics.TruthFunctions
