import LCS.Propositional.Systems.G.Search.SearchRounds

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTraceRound1_eq_displayed := by
  rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTraceRound2_eq_displayed := by
  rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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
