import LCS.Propositional.Systems.G.Search.Expansion

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Definition 3.4.6 (required helper): Auxiliary lemma with an accumulator
    offset `k` — if `findFirstNonatomic L k = some (A, i)`, then `k ≤ i` and
    `L` splits around position `i - k` yielding prefix, `[A]`, suffix. -/
theorem findFirstNonatomic_split_aux (ante : List PropFormulaNormalized)
    (k : Nat) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic ante k = some (A, i)) :
    k ≤ i ∧ ante = ante.take (i - k) ++ [A] ++ ante.drop (i - k + 1) := by
-- BEGIN PROOF
  induction ante generalizing k with
  | nil => simp [findFirstNonatomic] at h
  | cons x xs ih =>
    simp [findFirstNonatomic] at h
    split at h
    · next _ =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.le.refl, ?_⟩
      simp
    · next _ =>
      obtain ⟨hle, heq⟩ := ih _ h
      refine ⟨Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hle), ?_⟩
      have hksub : i - k = (i - (k + 1)) + 1 := by omega
      show x :: xs = (x :: xs).take (i - k) ++ [A] ++ (x :: xs).drop (i - k + 1)
      rw [hksub, List.take_succ_cons, List.drop_succ_cons, List.cons_append,
          List.cons_append]
      rw [← heq]

proof_of findFirstNonatomic_split := by
  -- BEGIN PROOF
    have := findFirstNonatomic_split_aux ante 0 A i h
    simpa using this.2

helper theorem take_elem_drop (L : List α) (i : Nat) (hi : i < L.length) :
    L.take i ++ [L[i]] ++ L.drop (i + 1) = L := by
-- BEGIN PROOF
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
                  List.cons_append]
      congr 1; exact ih j (by simp at hi; exact hi)

proof_of selectOffset_split := by
  simp only [selectOffset, Option.map_eq_some_iff] at h
  obtain ⟨B, hB, heq⟩ := h
  cases heq
  have hi := List.getElem?_eq_some_iff.mp hB
  obtain ⟨hi, hval⟩ := hi
  rw [← hval]
  exact (take_elem_drop L _ hi).symm

end LCS.Propositional.Systems.G.Search
end
