import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

namespace SearchTree



end SearchTree

end LCS.FirstOrder.Gentzen.Search.NoFunction

end

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

namespace SearchState

helper /-- Definition 5.4.9 (companion, invariant): `NoVarAbove` is monotone
    in the bound — if every var index is `< b`, then every var index
    is `< b'` for any `b' ≥ b`. -/
theorem SearchState.NoVarAbove_mono {L : Language} {seq : Sequent L} {b b' : Nat}
    (h : NoVarAbove seq b) (hle : b ≤ b') : NoVarAbove seq b' := by
-- BEGIN PROOF
  intro F hF
  obtain ⟨hFV, hBV⟩ := h F hF
  exact ⟨fun j hj => Nat.lt_of_lt_of_le (hFV j hj) hle,
         fun j hj => Nat.lt_of_lt_of_le (hBV j hj) hle⟩











end SearchState

end LCS.FirstOrder.Gentzen.Search.NoFunction

end

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

helper theorem list_eraseDups_nodup {α : Type} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  induction hn : xs.length using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    match xs, hn with
    | [], _ => simp [List.eraseDups_nil]
    | hd :: tl, hlen =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hcon
        rw [List.mem_eraseDups, List.mem_filter] at hcon
        simp at hcon
      · apply ih _ _ _ rfl
        have := List.length_filter_le (fun b => !b == hd) tl
        simp at hlen
        omega

helper /-- Definition 5.4.9 (companion, discharge): An index `i ≥ bound`
    cannot occur bound in any formula of `seq` when
    `NoVarAbove seq bound` holds (every bound-variable index is
    strictly less than `bound`). Captures the freshness of activated
    eigenvariables: `y = availNext` at activation has `y ≥ bound` by
    `Inv.avail_above_bound`, and so `y ∉ BV(G)` for every `G ∈ seq`. -/
theorem notBV_of_geBound {L : Language} {seq : Sequent L} {bound : Nat}
    (hNVA : NoVarAbove seq bound) {i : Nat} (hi : bound ≤ i)
    (G : FormulaN L) (hG : G ∈ seq.antecedent ++ seq.succedent) :
    i ∉ formulaBVN G := by
-- BEGIN PROOF
  intro hiBV
  have hlt : i < bound := (hNVA G hG).2 i hiBV
  exact Nat.not_lt_of_le hi hlt



end LCS.FirstOrder.Gentzen.Search.NoFunction

end
