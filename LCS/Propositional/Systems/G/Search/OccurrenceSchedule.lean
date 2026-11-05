import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.OccurrenceSchedule.ProofsStamp
import LCS.Propositional.Systems.G.Search.LeafExpansion
import LCS.Propositional.Systems.G.Search.SearchRounds
import LCS.Propositional.Systems.G.Search.Validity
import LCS.Propositional.Systems.G.Search.Falsification
import LCS.Propositional.Systems.G.Search.Termination
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

/-- The frozen schedule visits the leftmost remaining occurrence first. -/
theorem suffixSchedule_succ (side : Bool) (n : Nat) :
    suffixSchedule side (n + 1) = (side, n) :: suffixSchedule side n := by
  simp [suffixSchedule, List.range_succ, List.reverse_append]

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search.Fairness
/-- A suffix offset identifies its occurrence regardless of the prefix. -/
theorem selectOffset_suffix (pre tail : List PropFormulaNormalized)
    (A : PropFormulaNormalized) :
    selectOffset tail.length (pre ++ A :: tail) = some (A, pre.length) := by
  simp [selectOffset, List.length_append]

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search.Fairness
/-- A scheduled variable contributes no inference step. -/
theorem expandScheduled_var {s : Sequent} (side : Bool) (offset i n : Nat)
    (h : selectOffset offset (if side then s.succedent else s.antecedent) =
      some (.var n, i)) :
    expandScheduled mode side offset s = .leaf s := by
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals
    unfold expandScheduled
    split
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold expandSelected
      dsimp only []
      split
      · next A j hj =>
        have he := Option.some.inj (h.symm.trans hj)
        cases he
        rfl
      · rfl

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search.Fairness
/-- A block of original variables is skipped without changing the tree.
    The already visited prefix remains in the current sequent. -/
theorem expandSchedule_skip_atomic_prefix (s : Sequent) (side : Bool)
    (done pre tail : List PropFormulaNormalized) (rest : List (Bool × Nat))
    (hs : (if side then s.succedent else s.antecedent) = done ++ pre ++ tail)
    (hat : ∀ A ∈ pre, isAtomicFormula A) :
    expandSchedule mode (suffixSchedule side (pre.length + tail.length) ++ rest) (.leaf s) =
      expandSchedule mode (suffixSchedule side tail.length ++ rest) (.leaf s) := by
  induction pre generalizing done with
  | nil => simp
  | cons A pre ih =>
    have hA := hat A (by simp)
    cases A with
    | var n =>
      have hselect : selectOffset (pre.length + tail.length)
          (if side then s.succedent else s.antecedent) = some (.var n, done.length) := by
        rw [hs]
        simpa [List.append_assoc] using selectOffset_suffix done (pre ++ tail) (.var n)
      have hstep := expandScheduled_var (mode := mode) side _ _ _ hselect
      rw [show (PropFormulaNormalized.var n :: pre).length + tail.length =
        (pre.length + tail.length) + 1 from by simp; omega, suffixSchedule_succ]
      simp only [List.cons_append, expandSchedule, List.foldl_cons, mapLeaves, hstep]
      exact ih (done ++ [.var n]) (by simpa [List.append_assoc] using hs)
        (fun B hB => hat B (by simp [hB]))
    | neg _ => simp [isAtomicFormula] at hA
    | conj _ _ => simp [isAtomicFormula] at hA
    | disj _ _ => simp [isAtomicFormula] at hA
    | impl _ _ => simp [isAtomicFormula] at hA

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
/-- The first nonatomic selector's preceding occurrences are variables. -/
theorem findFirstNonatomic_atomic_prefix (L : List PropFormulaNormalized) (k : Nat)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L k = some (A, i)) :
    ∀ B ∈ L.take (i - k), isAtomicFormula B := by
  induction L generalizing k with
  | nil => simp [findFirstNonatomic] at h
  | cons C cs ih =>
    simp only [findFirstNonatomic] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Option.some.inj h
      simp
    · next hc =>
      have hbound := (findFirstNonatomic_spec_aux cs (k + 1) A i h).1
      have hi : i - k = (i - (k + 1)) + 1 := by omega
      rw [hi, List.take_succ_cons]
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · cases B <;> simp_all [isNonatomicBool, isAtomicFormula]
      · exact ih (k + 1) h B hB

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
/-- Finished leaves remain unchanged for any frozen schedule. -/
theorem expandSchedule_finished (s : Sequent) (schedule : List (Bool × Nat))
    (h : isFinishedLeafBool mode s = true) :
    expandSchedule mode schedule (.leaf s) = .leaf s := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [expandSchedule, List.foldl_cons, mapLeaves, expandScheduled, h,
      ↓reduceIte] using ih

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
/-- The first antecedent occurrence is the first effective scheduled rule. -/
theorem expandFirstFormula_eq_scheduled_ante (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic s.antecedent = some (A, i)) :
    expandFirstFormula s = expandScheduled mode false
      (s.antecedent.length - (i + 1)) s := by
  have ⟨hi, hget, _⟩ := findFirstNonatomic_spec _ _ _ h
  have hsel : selectOffset (s.antecedent.length - (i + 1)) s.antecedent = some (A, i) := by
    simp only [selectOffset]
    rw [show s.antecedent.length - (s.antecedent.length - (i + 1) + 1) = i by omega, hget]
    rfl
  unfold expandFirstFormula expandScheduled
  simp only [hunf, Bool.false_eq_true, ↓reduceIte]
  unfold expandSelected
  split
  · next B j hB =>
    obtain ⟨hAB, hij⟩ := Prod.mk.inj (Option.some.inj (h.symm.trans hB))
    subst B; subst j
    cases A <;> dsimp only [] <;> split
    all_goals first
      | next C k hC =>
        obtain ⟨hAC, hik⟩ := Prod.mk.inj (Option.some.inj (hsel.symm.trans hC))
        subst C; subst k
        rfl
      | next hnone => simp [hnone] at hsel
  · next hnone => simp [hnone] at h

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
/-- The first succedent occurrence is the first effective scheduled rule
    when every original antecedent occurrence is atomic. -/
theorem expandFirstFormula_eq_scheduled_succ (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true)
    (hant : findFirstNonatomic s.antecedent = none)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic s.succedent = some (A, i)) :
    expandFirstFormula s = expandScheduled mode true
      (s.succedent.length - (i + 1)) s := by
  have ⟨hi, hget, _⟩ := findFirstNonatomic_spec _ _ _ h
  have hsel : selectOffset (s.succedent.length - (i + 1)) s.succedent = some (A, i) := by
    simp only [selectOffset]
    rw [show s.succedent.length - (s.succedent.length - (i + 1) + 1) = i by omega, hget]
    rfl
  unfold expandFirstFormula expandScheduled
  simp only [hunf, Bool.false_eq_true, ↓reduceIte]
  unfold expandSelected
  split
  · next B j hB => simp [hant] at hB
  · dsimp only []
    split
    · next B j hB =>
      obtain ⟨hAB, hij⟩ := Prod.mk.inj (Option.some.inj (h.symm.trans hB))
      subst B; subst j
      cases A <;> dsimp only [] <;> split
      all_goals first
        | next C k hC =>
          obtain ⟨hAC, hik⟩ := Prod.mk.inj (Option.some.inj (hsel.symm.trans hC))
          subst C; subst k
          rfl
        | next hnone => simp [hnone] at hsel
    · next hnone => simp [hnone] at h

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search.Fairness
/-- The implementation is exactly the two frozen occurrence loops in
    Definition 3.4.6. Skipping an initial block of variables only removes
    iterations that leave the tree unchanged. -/
theorem expandLeaf_eq_full_schedule (s : Sequent) :
    expandLeaf mode s =
      expandSchedule mode (suffixSchedule false s.antecedent.length ++
        suffixSchedule true s.succedent.length) (.leaf s) := by
  by_cases hfin : isFinishedLeafBool mode s = true
  · rw [expandLeaf_of_finished s hfin, expandSchedule_finished s _ hfin]
  · unfold expandLeaf
    simp only [hfin, Bool.false_eq_true, ↓reduceIte]
    cases hant : findFirstNonatomic s.antecedent with
    | some pair =>
      obtain ⟨A, i⟩ := pair
      have hsplit := findFirstNonatomic_split _ _ _ hant
      have hat : ∀ B ∈ s.antecedent.take i, isAtomicFormula B := by
        simpa using findFirstNonatomic_atomic_prefix s.antecedent 0 A i hant
      have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s false []
        (s.antecedent.take i) (A :: s.antecedent.drop (i + 1))
        (suffixSchedule true s.succedent.length)
        (by simpa [List.append_assoc] using hsplit) hat
      have hlen : (s.antecedent.take i).length +
          (A :: s.antecedent.drop (i + 1)).length = s.antecedent.length := by
        have := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
      rw [hlen] at hskip
      rw [hskip]
      simp only [List.length_cons, List.length_drop, suffixSchedule_succ,
        List.cons_append, expandSchedule, List.foldl_cons, mapLeaves]
      rw [← expandFirstFormula_eq_scheduled_ante s hfin A i hant]
    | none =>
      have hat := findFirstNonatomic_none_all_atomic _ _ hant
      have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s false []
        s.antecedent [] (suffixSchedule true s.succedent.length) (by simp) hat
      have hskipAnt : expandSchedule mode
          (suffixSchedule false s.antecedent.length ++ suffixSchedule true s.succedent.length)
          (.leaf s) = expandSchedule mode (suffixSchedule true s.succedent.length) (.leaf s) := by
        simpa [suffixSchedule] using hskip
      rw [hskipAnt]
      cases hsucc : findFirstNonatomic s.succedent with
      | none =>
        exfalso
        apply hfin
        apply (isFinishedLeafBool_iff s).mpr
        right
        intro A hA
        rcases List.mem_append.mp hA with hA | hA
        · exact hat A hA
        · exact findFirstNonatomic_none_all_atomic _ _ hsucc A hA
      | some pair =>
        obtain ⟨A, i⟩ := pair
        have hsplit := findFirstNonatomic_split _ _ _ hsucc
        have hpre : ∀ B ∈ s.succedent.take i, isAtomicFormula B := by
          simpa using findFirstNonatomic_atomic_prefix s.succedent 0 A i hsucc
        have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s true []
          (s.succedent.take i) (A :: s.succedent.drop (i + 1)) []
          (by simpa [List.append_assoc] using hsplit) hpre
        have hlen : (s.succedent.take i).length +
            (A :: s.succedent.drop (i + 1)).length = s.succedent.length := by
          have := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
          omega
        rw [hlen] at hskip
        simp only [List.append_nil] at hskip
        rw [hskip]
        simp only [List.length_cons, List.length_drop, suffixSchedule_succ,
          expandSchedule, List.foldl_cons, mapLeaves]
        rw [← expandFirstFormula_eq_scheduled_succ s hfin hant A i hsucc]

end LCS.Propositional.Systems.G.Search
end

