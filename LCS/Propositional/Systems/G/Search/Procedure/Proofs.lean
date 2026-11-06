import LCS.Propositional.Systems.G.Search.Procedure
open LCS.Propositional.Systems.G.Search.Expansion.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_add_ge (n : Nat) (L : List Nat) :
    L.foldl (· + ·) n ≥ n := by
-- BEGIN PROOF
  induction L generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons]
    exact Nat.le_trans (Nat.le_add_right n x) (ih _)

helper theorem foldl_add_zero_of_member {f : PropFormulaNormalized → Nat}
    {L : List PropFormulaNormalized}
    (hzero : (L.map f).foldl (· + ·) 0 = 0)
    {a : PropFormulaNormalized} (ha : a ∈ L) : f a = 0 := by
-- BEGIN PROOF
  induction L with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add] at hzero
    rcases List.mem_cons.mp ha with rfl | hxs
    · have h1 := foldl_add_ge (f a) (xs.map f); omega
    · have hfx : f x = 0 := by
        have h1 := foldl_add_ge (f x) (xs.map f); omega
      simp only [hfx] at hzero
      exact ih hzero hxs

helper theorem sequentComplexity_zero_all_zero (s : Sequent)
    (hzero : sequentComplexity s = 0) :
    (∀ A ∈ s.antecedent, formulaComplexity A = 0) ∧
    (∀ B ∈ s.succedent, formulaComplexity B = 0) := by
-- BEGIN PROOF
  simp [sequentComplexity] at hzero
  have hAnt : (s.antecedent.map formulaComplexity).foldl (· + ·) 0 = 0 := by
    have h1 := foldl_add_ge 0 (s.antecedent.map formulaComplexity); omega
  have hSucc : (s.succedent.map formulaComplexity).foldl (· + ·) 0 = 0 := by
    have h1 := foldl_add_ge 0 (s.succedent.map formulaComplexity); omega
  exact ⟨fun A hA => foldl_add_zero_of_member hAnt hA,
         fun B hB => foldl_add_zero_of_member hSucc hB⟩

helper theorem complexity_zero_is_var (A : PropFormulaNormalized)
    (hc : formulaComplexity A = 0) :
    ∃ n, A = .var n := by
-- BEGIN PROOF
  cases A with
  | var n => exact ⟨n, rfl⟩
  | neg _ => simp [formulaComplexity] at hc
  | conj _ _ => simp [formulaComplexity] at hc
  | disj _ _ => simp [formulaComplexity] at hc
  | impl _ _ => simp [formulaComplexity] at hc

helper theorem foldl_add_eq_add_foldl (n : Nat) (L : List Nat) :
    L.foldl (· + ·) n = n + L.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction L generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih, ih x]; omega

helper theorem foldl_add_eq_sum (L : List Nat) :
    L.foldl (· + ·) 0 = L.sum := by
-- BEGIN PROOF
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.sum_cons]
    rw [foldl_add_eq_add_foldl]; omega

helper theorem sequentComplexity_as_sum (s : Sequent) :
    sequentComplexity s =
      (s.antecedent.map formulaComplexity).sum +
      (s.succedent.map formulaComplexity).sum := by
-- BEGIN PROOF
  simp only [sequentComplexity, foldl_add_eq_sum]

helper theorem step1_complexity_decrease {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) :
    sequentComplexity prem < sequentComplexity conc := by
-- BEGIN PROOF
  cases rule <;>
    simp only [sequentComplexity_as_sum, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      formulaComplexity] <;>
    omega

helper theorem step2_complexity_decrease {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) :
    sequentComplexity p1 < sequentComplexity conc ∧
    sequentComplexity p2 < sequentComplexity conc := by
-- BEGIN PROOF
  cases rule <;> (constructor <;>
    simp only [sequentComplexity_as_sum, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      formulaComplexity] <;>
    omega)

helper theorem foldl_max_shift (L : List Nat) (a : Nat) :
    L.foldl max a = max a (L.foldl max 0) := by
-- BEGIN PROOF
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (max a x), ih (max 0 x)]
    omega

helper theorem le_foldl_max_of_mem {L : List Nat} {x : Nat}
    (hx : x ∈ L) : x ≤ L.foldl max 0 := by
  induction L with
  | nil => simp_all
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [foldl_max_shift]
    cases List.mem_cons.mp hx with
    | inl h => subst h; omega
    | inr h => have := ih h; omega

helper theorem foldl_max_lt_of_all_lt {L : List Nat} {bound : Nat}
    (hne : L ≠ [])
    (hall : ∀ x ∈ L, x < bound) :
    L.foldl max 0 < bound := by
-- BEGIN PROOF
  induction L with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [foldl_max_shift]
    have hx := hall x (List.Mem.head _)
    cases xs with
    | nil => simp; omega
    | cons y ys =>
      have hxs := ih (List.cons_ne_nil y ys)
        (fun z hz => hall z (List.Mem.tail _ hz))
      omega

helper theorem unfinished_pos_complexity (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    sequentComplexity s > 0 :=
-- BEGIN PROOF
  Classical.byContradiction fun hle => by
    have hzero : sequentComplexity s = 0 := by omega
    have ⟨hAnt0, hSucc0⟩ := sequentComplexity_zero_all_zero s hzero
    have hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, isAtomicFormula A := by
      intro A hA
      cases List.mem_append.mp hA with
      | inl hAntA =>
        obtain ⟨n, rfl⟩ := complexity_zero_is_var A (hAnt0 A hAntA)
        exact trivial
      | inr hSuccA =>
        obtain ⟨n, rfl⟩ := complexity_zero_is_var A (hSucc0 A hSuccA)
        exact trivial
    exact hunf ((isFinishedLeafBool_iff s).mpr (Or.inr hAllVar))

helper theorem sequent_ant_eq (s : Sequent) (i : Nat) (A : PropFormulaNormalized)
    (hi : i < s.antecedent.length) (hA : s.antecedent[i] = A) :
    s = Sequent.mk (s.antecedent.take i ++ [A] ++ s.antecedent.drop (i + 1)) s.succedent := by
-- BEGIN PROOF
  rcases s with ⟨ant, succ⟩; subst hA
  exact congrArg (Sequent.mk · succ) (take_elem_drop ant i hi).symm

helper theorem sequent_succ_eq (s : Sequent) (j : Nat) (B : PropFormulaNormalized)
    (hj : j < s.succedent.length) (hB : s.succedent[j] = B) :
    s = Sequent.mk s.antecedent (s.succedent.take j ++ [B] ++ s.succedent.drop (j + 1)) := by
-- BEGIN PROOF
  rcases s with ⟨ant, succ⟩; subst hB
  exact congrArg (Sequent.mk ant) (take_elem_drop succ j hj).symm

helper /-- Every leaf of expandLeaf s has strictly smaller sequent complexity than s,
    provided s is not a finished leaf. -/
theorem expandFirstFormula_leaves_complexity_lt (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    ∀ leaf ∈ (expandFirstFormula s).leaves,
      sequentComplexity leaf < sequentComplexity s := by
-- BEGIN PROOF
  unfold expandFirstFormula expandSelected
  split
  · case h_1 A i hfind =>
    have ⟨hi, hget, hna⟩ := findFirstNonatomic_spec s.antecedent A i hfind
    have hA : s.antecedent[i] = A := by
      rw [List.getElem?_eq_getElem hi] at hget; exact Option.some.inj hget
    have hs := sequent_ant_eq s i A hi hA
    cases A with
    | neg C =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
      rw [congrArg sequentComplexity hs]
      exact step1_complexity_decrease (GentzenStep1.negLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C)
    | conj C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
      rw [congrArg sequentComplexity hs]
      exact step1_complexity_decrease (GentzenStep1.andLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)
    | disj C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.orLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).1
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.orLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).2
    | impl C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.implLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).1
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.implLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).2
    | var n => simp [isNonatomicBool] at hna
  · case h_2 hno_ant =>
    split
    · case h_1 B j hfind =>
      have ⟨hj, hget, hna⟩ := findFirstNonatomic_spec s.succedent B j hfind
      have hB : s.succedent[j] = B := by
        rw [List.getElem?_eq_getElem hj] at hget; exact Option.some.inj hget
      have hs := sequent_succ_eq s j B hj hB
      cases B with
      | neg C =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.negRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C)
      | conj C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · rw [congrArg sequentComplexity hs]
          exact (step2_complexity_decrease (GentzenStep2.andRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)).1
        · rw [congrArg sequentComplexity hs]
          exact (step2_complexity_decrease (GentzenStep2.andRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)).2
      | disj C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.orRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)
      | impl C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.implRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)
      | var n => simp [isNonatomicBool] at hna
    · case h_2 hno_succ =>
      -- Both findFirstNonatomic return none: all formulas are atomic
      -- But hunf says s is not finished, contradiction
      exfalso; apply hunf
      rw [isFinishedLeafBool_iff s]
      right
      intro A hA
      cases List.mem_append.mp hA with
      | inl hAnt => exact findFirstNonatomic_none_all_atomic _ _ hno_ant A hAnt
      | inr hSucc => exact findFirstNonatomic_none_all_atomic _ _ hno_succ A hSucc

helper /-- The leaves produced by structural substitution descend from one
    particular leaf of the input tree. -/
theorem mapLeaves_leaves {c : Sequent} (dt : DeductionTree c)
    (expand : (s : Sequent) → DeductionTree s) :
    ∀ leaf ∈ (mapLeaves expand dt).leaves,
      ∃ original ∈ dt.leaves, leaf ∈ (expand original).leaves := by
  induction dt with
  | leaf s =>
    intro leaf h
    exact ⟨s, by simp [DeductionTree.leaves], h⟩
  | onePremise rule child ih => exact ih
  | twoPremise rule left right ihL ihR =>
    intro leaf h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨s, hs, hleaf⟩ := ihL leaf h
      exact ⟨s, List.mem_append_left _ hs, hleaf⟩
    · obtain ⟨s, hs, hleaf⟩ := ihR leaf h
      exact ⟨s, List.mem_append_right _ hs, hleaf⟩

helper /-- Every rule decreases complexity, so every leaf is bounded by its
    tree's root, independently of the schedule used to construct it. -/
theorem deductionTree_leaf_complexity_le {c : Sequent} (dt : DeductionTree c) :
    ∀ leaf ∈ dt.leaves, sequentComplexity leaf ≤ sequentComplexity c := by
  induction dt with
  | leaf s =>
    intro leaf h
    simp only [DeductionTree.leaves, List.mem_singleton] at h
    subst leaf
    exact Nat.le_refl _
  | onePremise rule child ih =>
    intro leaf h
    exact Nat.le_trans (ih leaf h) (Nat.le_of_lt (step1_complexity_decrease rule))
  | twoPremise rule left right ihL ihR =>
    intro leaf h
    rcases List.mem_append.mp h with h | h
    · exact Nat.le_trans (ihL leaf h) (Nat.le_of_lt (step2_complexity_decrease rule).1)
    · exact Nat.le_trans (ihR leaf h) (Nat.le_of_lt (step2_complexity_decrease rule).2)

helper theorem expandSchedule_leaves_bound {c : Sequent}
    (schedule : List (Bool × Nat)) (dt : DeductionTree c) :
    ∀ leaf ∈ (expandSchedule mode schedule dt).leaves,
      ∃ original ∈ dt.leaves, sequentComplexity leaf ≤ sequentComplexity original := by
  induction schedule generalizing dt with
  | nil =>
    intro leaf h
    exact ⟨leaf, h, Nat.le_refl _⟩
  | cons entry rest ih =>
    intro leaf h
    obtain ⟨mid, hmid, hle⟩ := ih (mapLeaves (expandScheduled mode entry.1 entry.2) dt) leaf h
    obtain ⟨original, horiginal, hdesc⟩ := mapLeaves_leaves dt _ mid hmid
    exact ⟨original, horiginal,
      Nat.le_trans hle (deductionTree_leaf_complexity_le _ mid hdesc)⟩

helper /-- A round strictly reduces the complexity of every descendant of an
    unfinished leaf. Its first effective rule decreases complexity; all
    remaining scheduled rules preserve that strict upper bound. -/
theorem expandLeaf_leaves_complexity_lt (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    ∀ leaf ∈ (expandLeaf mode s).leaves,
      sequentComplexity leaf < sequentComplexity s := by
  simp only [expandLeaf, hunf, Bool.false_eq_true, ↓reduceIte]
  intro leaf h
  obtain ⟨original, horiginal, hle⟩ := expandSchedule_leaves_bound _ _ leaf h
  exact Nat.lt_of_le_of_lt hle
    (expandFirstFormula_leaves_complexity_lt s hunf original horiginal)

helper theorem unfinished_le_max {c : Sequent} (dt : DeductionTree c) (s : Sequent)
    (hs : s ∈ unfinishedLeaves mode dt) :
    sequentComplexity s ≤ maxUnfinishedLeafComplexity mode dt := by
  simp only [maxUnfinishedLeafComplexity]
  apply le_foldl_max_of_mem
  exact List.mem_map_of_mem (f := sequentComplexity) hs

helper theorem not_finished_of_mem_unfinished {c : Sequent} {s : Sequent}
    {dt : DeductionTree c}
    (h : s ∈ unfinishedLeaves mode dt) : ¬isFinishedLeafBool mode s = true := by
-- BEGIN PROOF
  simp only [unfinishedLeaves, List.mem_filter] at h
  obtain ⟨_, hfilt⟩ := h
  intro htrue; rw [htrue] at hfilt; simp at hfilt

helper theorem unfinishedLeaves_ne_nil {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    unfinishedLeaves mode dt ≠ [] := by
-- BEGIN PROOF
  intro hempty; apply hunf
  simp only [isFinishedTreeBool, List.all_eq_true]
  intro s hs
  simp only [unfinishedLeaves] at hempty
  have := List.filter_eq_nil_iff.mp hempty s hs
  simp at this; exact this

helper theorem searchRound_unfinished_lt_max {c : Sequent} (dt : DeductionTree c)
    (_hunf : ¬isFinishedTreeBool mode dt = true) :
    ∀ s ∈ unfinishedLeaves mode (searchRound mode dt),
      sequentComplexity s < maxUnfinishedLeafComplexity mode dt := by
-- BEGIN PROOF
  intro s hs
  have hs_leaf : s ∈ (searchRound mode dt).leaves := by
    simp only [unfinishedLeaves, List.mem_filter] at hs; exact hs.1
  have hs_unf : ¬isFinishedLeafBool mode s = true := not_finished_of_mem_unfinished hs
  obtain ⟨original, horiginal, hdesc⟩ := mapLeaves_leaves dt (expandLeaf mode) s hs_leaf
  by_cases hfin : isFinishedLeafBool mode original = true
  · rw [expandLeaf_of_finished original hfin] at hdesc
    simp only [DeductionTree.leaves, List.mem_singleton] at hdesc
    subst original
    exact False.elim (hs_unf hfin)
  · have hmem : original ∈ unfinishedLeaves mode dt := by
      simp [unfinishedLeaves, horiginal, hfin]
    exact Nat.lt_of_lt_of_le
      (expandLeaf_leaves_complexity_lt original hfin s hdesc)
      (unfinished_le_max dt original hmem)

helper theorem max_pos_of_unfinished {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    maxUnfinishedLeafComplexity mode dt > 0 := by
-- BEGIN PROOF
  have hne := unfinishedLeaves_ne_nil dt hunf
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
  exact Nat.lt_of_lt_of_le
    (unfinished_pos_complexity s (not_finished_of_mem_unfinished hs))
    (unfinished_le_max dt s hs)

proof_of searchRound_complexity_decrease := by
  -- BEGIN PROOF
    have hmax_pos := max_pos_of_unfinished dt hunf
    simp only [maxUnfinishedLeafComplexity]
    by_cases hne :
      (unfinishedLeaves mode (searchRound mode dt)).map sequentComplexity = []
    · simp [hne]; exact hmax_pos
    · exact foldl_max_lt_of_all_lt hne (fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact searchRound_unfinished_lt_max dt hunf s hs)

helper theorem search_of_finished {c : Sequent} (dt : DeductionTree c)
    (h : isFinishedTreeBool mode dt = true) :
    search mode dt = dt := by
-- BEGIN PROOF
  simp [search, h]

end LCS.Propositional.Systems.G.Search
end
