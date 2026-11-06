import LCS.Resolution.Method.Resolvents

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper theorem removePairFirst (L M : Literal) (h : L ≠ M) :
    GCNF.Clause.remove (GCNF.Clause.ofList [L, M]) L = GCNF.Clause.single M := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
    LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro ⟨hx, hne⟩
    exact hx.elim (fun he => False.elim (hne he)) id
  · intro hx
    subst x
    exact ⟨Or.inr rfl, Ne.symm h⟩

helper theorem removePairSecond (L M : Literal) (h : L ≠ M) :
    GCNF.Clause.remove (GCNF.Clause.ofList [L, M]) M = GCNF.Clause.single L := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
    LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro ⟨hx, hne⟩
    exact hx.elim id (fun he => False.elim (hne he))
  · intro hx
    subst x
    exact ⟨Or.inl rfl, h⟩

helper theorem unionSingles (L M : Literal) :
    GCNF.Clause.union (GCNF.Clause.single L) (GCNF.Clause.single M) =
      GCNF.Clause.ofList [L, M] := by
  apply LCS.Finset.ext
  intro x
  simp [GCNF.Clause.union, GCNF.Clause.single, GCNF.Clause.ofList,
    LCS.Finset.mem_union_exp, LCS.Finset.mem_singleton]

proof_of exampleTwoResolvents := by
  have hPos : Literal.pos A ≠ Literal.pos B := fun h => hAB (Literal.pos.inj h)
  have hNeg : Literal.neg A ≠ Literal.neg B := fun h => hAB (Literal.neg.inj h)
  constructor
  · rintro ⟨L, hL, _, hC⟩
    simp only [GCNF.Clause.ofList, LCS.Finset.mem_ofList, List.mem_cons,
      List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · right
      simpa only [Clause.remove, Literal.conjugate, removePairFirst _ _ hPos,
        removePairFirst _ _ hNeg, unionSingles] using hC
    · left
      simpa only [Clause.remove, Literal.conjugate, removePairSecond _ _ hPos,
        removePairSecond _ _ hNeg, unionSingles] using hC
  · rintro (rfl | rfl)
    · refine ⟨.pos B, ?_, ?_, ?_⟩
      · simp [GCNF.Clause.ofList]
      · simp [GCNF.Clause.ofList, Literal.conjugate]
      · simp only [Clause.remove, Literal.conjugate, removePairSecond _ _ hPos,
          removePairSecond _ _ hNeg, unionSingles]
    · refine ⟨.pos A, ?_, ?_, ?_⟩
      · simp [GCNF.Clause.ofList]
      · simp [GCNF.Clause.ofList, Literal.conjugate]
      · simp only [Clause.remove, Literal.conjugate, removePairFirst _ _ hPos,
          removePairFirst _ _ hNeg, unionSingles]

helper /-- A literal and its conjugate cannot both be satisfied by the same
    valuation. -/
theorem literal_conjugate_not_both_sat (L : Literal) (v : Nat → Bool) :
    Literal.satisfiedBy L v → Literal.satisfiedBy (Literal.conjugate L) v → False := by
-- BEGIN PROOF
  cases L with
  | pos n => simp [Literal.satisfiedBy, Literal.conjugate]
  | neg n => simp [Literal.satisfiedBy, Literal.conjugate]

helper /-- If a valuation satisfies both C1 and C2, then it satisfies
    union (remove C1 L) (remove C2 (conjugate L)), for any L. -/
theorem resolvent_sat (C1 C2 : Clause) (L : Literal) (v : Nat → Bool)
    (h1 : Clause.satisfies v C1) (h2 : Clause.satisfies v C2) :
    Clause.satisfies v (GCNF.Clause.union (GCNF.Clause.remove C1 L) (GCNF.Clause.remove C2 (Literal.conjugate L))) := by
-- BEGIN PROOF
  obtain ⟨M, hMmem, hMsat⟩ := h1
  obtain ⟨N, hNmem, hNsat⟩ := h2
  by_cases hML : M = L
  · -- M = L, so v ⊨ L
    by_cases hNcL : N = Literal.conjugate L
    · -- N = conjugate L, so v ⊨ conjugate L — contradiction with v ⊨ L
      rw [hML] at hMsat; rw [hNcL] at hNsat
      exact absurd hNsat (literal_conjugate_not_both_sat L v hMsat)
    · -- N ≠ conjugate L, so N ∈ remove C2 (conjugate L)
      refine ⟨N, ?_, hNsat⟩
      rw [GCNF.Clause.union, LCS.Finset.mem_union_exp]
      exact Or.inr (by rw [GCNF.Clause.remove, LCS.Finset.mem_erase]; exact ⟨hNmem, hNcL⟩)
  · -- M ≠ L, so M ∈ remove C1 L
    refine ⟨M, ?_, hMsat⟩
    rw [GCNF.Clause.union, LCS.Finset.mem_union_exp]
    exact Or.inl (by rw [GCNF.Clause.remove, LCS.Finset.mem_erase]; exact ⟨hMmem, hML⟩)

open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolutionFormulaTautology := by
  intro v
  simp only [evalExt]
  cases evalExt v A <;> cases evalExt v B <;> cases v P <;> rfl

proof_of emptyDisjunctionReductions := by
  simp only [evalExt]
  cases evalExt v A <;> cases v P <;> decide

proof_of complementaryUnitsResolve := by
  refine ⟨L, (LCS.Finset.mem_singleton _ _).mpr rfl,
    (LCS.Finset.mem_singleton _ _).mpr rfl, ?_⟩
  apply LCS.Finset.ext
  intro x
  simp [GCNF.Clause.empty, GCNF.Clause.union, Clause.remove,
    GCNF.Clause.remove, GCNF.Clause.single, LCS.Finset.mem_union_exp,
    LCS.Finset.mem_singleton, LCS.Finset.mem_erase]
  exact LCS.Finset.not_mem_empty

end LCS.Resolution.Method
end
