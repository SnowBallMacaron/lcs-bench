import LCS.Propositional.Systems.G.Search.Validity

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_add_eq_add_foldl (n : Nat) (L : List Nat) :
    L.foldl (· + ·) n = n + L.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction L generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih, ih x]; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_add_eq_sum (L : List Nat) :
    L.foldl (· + ·) 0 = L.sum := by
-- BEGIN PROOF
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.sum_cons]
    rw [foldl_add_eq_add_foldl]; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sequentComplexity_as_sum (s : Sequent) :
    sequentComplexity s =
      (s.antecedent.map formulaComplexity).sum +
      (s.succedent.map formulaComplexity).sum := by
-- BEGIN PROOF
  simp only [sequentComplexity, foldl_add_eq_sum]

end LCS.Propositional.Systems.G.Search
end

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem valid_atomic_provable (s : Sequent)
    (hv : sequentValid s)
    (hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, ∃ n, A = .var n) :
    sequentProvable s := by
-- BEGIN PROOF
  have hax := valid_atomic_is_axiom s hv hAllVar
  exact ⟨ProofTree.axiom_ s hax⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem mc_s {x y : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    (h : y ∈ Γ ++ [x] ++ Δ) : y ∈ Γ ∨ y = x ∨ y ∈ Δ := by
-- BEGIN PROOF
  rcases List.mem_append.mp h with h1 | h2
  · rcases List.mem_append.mp h1 with hΓ | hx
    · exact Or.inl hΓ
    · rcases List.mem_cons.mp hx with rfl | hn; exact Or.inr (Or.inl rfl); simp at hn
  · exact Or.inr (Or.inr h2)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem ml_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Γ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem mr_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Δ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem mm_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    x ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.Mem.head _))))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem tc_s {A B y : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    (h : y ∈ Γ ++ [A, B] ++ Δ) : y ∈ Γ ∨ y = A ∨ y = B ∨ y ∈ Δ := by
-- BEGIN PROOF
  rcases List.mem_append.mp h with h1 | h2
  · rcases List.mem_append.mp h1 with hΓ | hAB
    · exact Or.inl hΓ
    · rcases List.mem_cons.mp hAB with rfl | hB
      · exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.mp hB with rfl | hn
        exact Or.inr (Or.inr (Or.inl rfl)); simp at hn
  · exact Or.inr (Or.inr (Or.inr h2))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem tl_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Γ) : y ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem tr_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Δ) : y ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem tf_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    A ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.Mem.head _))))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem ts_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    B ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.Mem.tail _ (List.Mem.head _)))))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem list_split_s {a : PropFormulaNormalized} {L : List PropFormulaNormalized}
    (h : a ∈ L) : ∃ before after, L = before ++ [a] ++ after := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hxs
    · exact ⟨[], xs, rfl⟩
    · obtain ⟨b, a2, rfl⟩ := ih hxs; exact ⟨x :: b, a2, by simp⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_shift_s (n : Nat) (L : List Nat) :
    L.foldl (· + ·) n = n + L.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction L generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih x]; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_eq_sum_s (L : List Nat) : L.foldl (· + ·) 0 = L.sum := by
-- BEGIN PROOF
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.sum_cons]
    rw [foldl_shift_s]; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sc_sum_s (s : Sequent) :
    sequentComplexity s = (s.antecedent.map formulaComplexity).sum +
                          (s.succedent.map formulaComplexity).sum := by
-- BEGIN PROOF
  simp only [sequentComplexity, foldl_eq_sum_s]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sum_zero_s {f : α → Nat} {L : List α}
    (h : ∀ x ∈ L, f x = 0) : (L.map f).sum = 0 := by
-- BEGIN PROOF
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp [List.sum_cons, h x (List.Mem.head _),
          ih (fun y hy => h y (List.Mem.tail _ hy))]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem step1_complexity_decrease {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) :
    sequentComplexity prem < sequentComplexity conc := by
-- BEGIN PROOF
  cases rule <;>
    simp only [sequentComplexity_as_sum, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      formulaComplexity] <;>
    omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem boolval_T_or_F (b : BoolVal) : b = BoolVal.T ∨ b = BoolVal.F := by
-- BEGIN PROOF
  cases b <;> simp

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem conj_T_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.conj A B) = BoolVal.T) :
    evalExtN v A = BoolVal.T ∧ evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hAnd]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem disj_F_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.disj A B) = BoolVal.F) :
    evalExtN v A = BoolVal.F ∧ evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hOr]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem impl_F_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.impl A B) = BoolVal.F) :
    evalExtN v A = BoolVal.T ∧ evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hImplies]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem neg_T_part {v : Valuation} {A : PropFormulaNormalized}
    (h : evalExtN v (.neg A) = BoolVal.T) :
    evalExtN v A = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> simp_all [hNeg]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem neg_F_part {v : Valuation} {A : PropFormulaNormalized}
    (h : evalExtN v (.neg A) = BoolVal.F) :
    evalExtN v A = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> simp_all [hNeg]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem conj_T_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.conj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hAnd]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem conj_F_of_left {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.conj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hAnd]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem conj_F_of_right {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.conj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hAnd]; cases evalExtN v A <;> rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem disj_T_of_left {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) :
    evalExtN v (.disj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hOr]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem disj_T_of_right {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.disj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hOr]; cases evalExtN v A <;> rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem disj_F_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.disj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hOr]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem impl_T_of_left_F {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.impl A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hImplies]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem impl_T_of_right_T {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.impl A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hImplies]; cases evalExtN v A <;> rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem impl_F_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.impl A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hImplies]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem neg_T_of_F {v : Valuation} {A : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.neg A) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hNeg]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem neg_F_of_T {v : Valuation} {A : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) :
    evalExtN v (.neg A) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hNeg]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem impl_T_right_of_left_T {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.impl A B) = BoolVal.T) (hA : evalExtN v A = BoolVal.T) :
    evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hImplies] at h
  cases hb : evalExtN v B <;> simp_all

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem disj_T_right_of_left_F {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.disj A B) = BoolVal.T) (hA : evalExtN v A = BoolVal.F) :
    evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hOr]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem conj_F_right_of_left_T {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.conj A B) = BoolVal.F) (hA : evalExtN v A = BoolVal.T) :
    evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hAnd]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem step1_falsification_forward {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (v : Valuation)
    (hf : sequentFalsifiedBy conc v) :
    sequentFalsifiedBy prem v := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hf
  cases rule with
  | andLeft Γ Δ Λ A B =>
    have ⟨hA, hB⟩ := conj_T_parts (hAnt _ mm_s)
    refine ⟨fun X hX => ?_, hSucc⟩
    rcases tc_s hX with hΓ | rfl | rfl | hΔ
    · exact hAnt X (ml_s hΓ)
    · exact hA
    · exact hB
    · exact hAnt X (mr_s hΔ)
  | orRight Γ Δ Λ A B =>
    have ⟨hA, hB⟩ := disj_F_parts (hSucc _ mm_s)
    refine ⟨hAnt, fun X hX => ?_⟩
    rcases tc_s hX with hΔ | rfl | rfl | hΛ
    · exact hSucc X (ml_s hΔ)
    · exact hA
    · exact hB
    · exact hSucc X (mr_s hΛ)
  | implRight Γ Δ Λ A B =>
    have ⟨hA, hB⟩ := impl_F_parts (hSucc _ mm_s)
    constructor
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hΓ
      · exact hA
      · exact hAnt X hΓ
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hCtx
      · exact hB
      · rcases List.mem_append.mp hCtx with hΔ | hΛ
        · exact hSucc X (ml_s hΔ)
        · exact hSucc X (mr_s hΛ)
  | negLeft Γ Δ Λ A =>
    have hA := neg_T_part (hAnt _ mm_s)
    constructor
    · intro X hX
      rcases List.mem_append.mp hX with hΓ | hΔ
      · exact hAnt X (ml_s hΓ)
      · exact hAnt X (mr_s hΔ)
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hΛ
      · exact hA
      · exact hSucc X hΛ
  | negRight Γ Δ Λ A =>
    have hA := neg_F_part (hSucc _ mm_s)
    constructor
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hΓ
      · exact hA
      · exact hAnt X hΓ
    · intro X hX
      rcases List.mem_append.mp hX with hΔ | hΛ
      · exact hSucc X (ml_s hΔ)
      · exact hSucc X (mr_s hΛ)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem step2_falsification_forward {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) (v : Valuation)
    (hf : sequentFalsifiedBy conc v) :
    sequentFalsifiedBy p1 v ∨ sequentFalsifiedBy p2 v := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hf
  cases rule with
  | andRight Γ Δ Λ A B =>
    have hAB := hSucc _ mm_s  -- evalExtN v (conj A B) = F
    rcases boolval_T_or_F (evalExtN v A) with hA | hA
    · have hB := conj_F_right_of_left_T hAB hA
      right; exact ⟨hAnt, fun X hX => match mc_s hX with
        | Or.inl hΔ => hSucc X (ml_s hΔ)
        | Or.inr (Or.inl h) => h ▸ hB
        | Or.inr (Or.inr hΛ) => hSucc X (mr_s hΛ)⟩
    · left; exact ⟨hAnt, fun X hX => match mc_s hX with
        | Or.inl hΔ => hSucc X (ml_s hΔ)
        | Or.inr (Or.inl h) => h ▸ hA
        | Or.inr (Or.inr hΛ) => hSucc X (mr_s hΛ)⟩
  | orLeft Γ Δ Λ A B =>
    have hAB := hAnt _ mm_s  -- evalExtN v (disj A B) = T
    rcases boolval_T_or_F (evalExtN v A) with hA | hA
    · left; exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸ hA
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ), hSucc⟩
    · have hB := disj_T_right_of_left_F hAB hA
      right; exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸ hB
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ), hSucc⟩
  | implLeft Γ Δ Λ A B =>
    have hAB := hAnt _ mm_s  -- evalExtN v (impl A B) = T
    rcases boolval_T_or_F (evalExtN v A) with hA | hA
    · have hB := impl_T_right_of_left_T hAB hA
      right
      constructor
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hΓΔ
        · exact hB
        · rcases List.mem_append.mp hΓΔ with hΓ | hΔ
          · exact hAnt X (ml_s hΓ)
          · exact hAnt X (mr_s hΔ)
      · exact hSucc
    · left
      constructor
      · intro X hX
        rcases List.mem_append.mp hX with hΓ | hΔ
        · exact hAnt X (ml_s hΓ)
        · exact hAnt X (mr_s hΔ)
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hΛ
        · exact hA
        · exact hSucc X hΛ

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem step1_falsification_backward {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (v : Valuation)
    (hf : sequentFalsifiedBy prem v) :
    sequentFalsifiedBy conc v := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hf
  cases rule with
  | andLeft Γ Δ Λ A B =>
    refine ⟨fun X hX => ?_, hSucc⟩
    rcases mc_s hX with hΓ | rfl | hΔ
    · exact hAnt X (tl_s hΓ)
    · exact conj_T_of_parts (hAnt A tf_s) (hAnt B ts_s)
    · exact hAnt X (tr_s hΔ)
  | orRight Γ Δ Λ A B =>
    refine ⟨hAnt, fun X hX => ?_⟩
    rcases mc_s hX with hΔ | rfl | hΛ
    · exact hSucc X (tl_s hΔ)
    · exact disj_F_of_parts (hSucc A tf_s) (hSucc B ts_s)
    · exact hSucc X (tr_s hΛ)
  | implRight Γ Δ Λ A B =>
    constructor
    · intro X hX; exact hAnt X (List.Mem.tail _ hX)
    · intro X hX
      rcases mc_s hX with hΔ | rfl | hΛ
      · exact hSucc X (List.Mem.tail _ (List.mem_append.mpr (Or.inl hΔ)))
      · exact impl_F_of_parts (hAnt A (List.Mem.head _)) (hSucc B (List.Mem.head _))
      · exact hSucc X (List.Mem.tail _ (List.mem_append.mpr (Or.inr hΛ)))
  | negLeft Γ Δ Λ A =>
    constructor
    · intro X hX
      rcases mc_s hX with hΓ | rfl | hΔ
      · exact hAnt X (List.mem_append.mpr (Or.inl hΓ))
      · exact neg_T_of_F (hSucc A (List.Mem.head _))
      · exact hAnt X (List.mem_append.mpr (Or.inr hΔ))
    · intro X hX; exact hSucc X (List.Mem.tail _ hX)
  | negRight Γ Δ Λ A =>
    constructor
    · intro X hX; exact hAnt X (List.Mem.tail _ hX)
    · intro X hX
      rcases mc_s hX with hΔ | rfl | hΛ
      · exact hSucc X (List.mem_append.mpr (Or.inl hΔ))
      · exact neg_F_of_T (hAnt A (List.Mem.head _))
      · exact hSucc X (List.mem_append.mpr (Or.inr hΛ))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem step2_falsification_backward {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) (v : Valuation)
    (hf : sequentFalsifiedBy p1 v ∨ sequentFalsifiedBy p2 v) :
    sequentFalsifiedBy conc v := by
-- BEGIN PROOF
  cases rule with
  | andRight Γ Δ Λ A B =>
    rcases hf with ⟨hAnt, hSucc⟩ | ⟨hAnt, hSucc⟩
    · exact ⟨hAnt, fun X hX => match mc_s hX with
        | Or.inl hΔ => hSucc X (ml_s hΔ)
        | Or.inr (Or.inl h) => h ▸ conj_F_of_left (hSucc A mm_s)
        | Or.inr (Or.inr hΛ) => hSucc X (mr_s hΛ)⟩
    · exact ⟨hAnt, fun X hX => match mc_s hX with
        | Or.inl hΔ => hSucc X (ml_s hΔ)
        | Or.inr (Or.inl h) => h ▸ conj_F_of_right (hSucc B mm_s)
        | Or.inr (Or.inr hΛ) => hSucc X (mr_s hΛ)⟩
  | orLeft Γ Δ Λ A B =>
    rcases hf with ⟨hAnt, hSucc⟩ | ⟨hAnt, hSucc⟩
    · exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸ disj_T_of_left (hAnt A mm_s)
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ), hSucc⟩
    · exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (ml_s hΓ)
        | Or.inr (Or.inl h) => h ▸ disj_T_of_right (hAnt B mm_s)
        | Or.inr (Or.inr hΔ) => hAnt X (mr_s hΔ), hSucc⟩
  | implLeft Γ Δ Λ A B =>
    rcases hf with ⟨hAnt, hSucc⟩ | ⟨hAnt, hSucc⟩
    · -- premise1: Γ++Δ → A, Λ falsified, so A is false → impl A B is T
      exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (List.mem_append.mpr (Or.inl hΓ))
        | Or.inr (Or.inl h) => h ▸ impl_T_of_left_F (hSucc A (List.Mem.head _))
        | Or.inr (Or.inr hΔ) => hAnt X (List.mem_append.mpr (Or.inr hΔ)),
      fun X hX => hSucc X (List.Mem.tail _ hX)⟩
    · -- premise2: B,Γ,Δ → Λ falsified, so B is true → impl A B is T
      exact ⟨fun X hX => match mc_s hX with
        | Or.inl hΓ => hAnt X (List.Mem.tail _ (List.mem_append.mpr (Or.inl hΓ)))
        | Or.inr (Or.inl h) => h ▸ impl_T_of_right_T (hAnt B (List.Mem.head _))
        | Or.inr (Or.inr hΔ) => hAnt X (List.Mem.tail _ (List.mem_append.mpr (Or.inr hΔ))),
      hSucc⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of deductionTree_falsification_iff := by
  -- BEGIN PROOF
    induction hwf with
    | leaf s =>
      simp [DeductionTree.conclusion, DeductionTree.leaves]
    | step1 rule hchild ih =>
      simp only [DeductionTree.conclusion, DeductionTree.leaves]
      constructor
      · intro hf
        have hfp := step1_falsification_forward rule v hf
        exact ih.mp hfp
      · intro ⟨s, hs, hfs⟩
        have hfp := ih.mpr ⟨s, hs, hfs⟩
        exact step1_falsification_backward rule v hfp
    | step2 rule hw1 hw2 ih1 ih2 =>
      simp only [DeductionTree.conclusion, DeductionTree.leaves]
      constructor
      · intro hf
        rcases step2_falsification_forward rule v hf with hf1 | hf2
        · obtain ⟨s, hs, hfs⟩ := ih1.mp hf1
          exact ⟨s, List.mem_append.mpr (Or.inl hs), hfs⟩
        · obtain ⟨s, hs, hfs⟩ := ih2.mp hf2
          exact ⟨s, List.mem_append.mpr (Or.inr hs), hfs⟩
      · intro ⟨s, hs, hfs⟩
        rcases List.mem_append.mp hs with h1 | h2
        · have hfp := ih1.mpr ⟨s, h1, hfs⟩
          exact step2_falsification_backward rule v (Or.inl hfp)
        · have hfp := ih2.mpr ⟨s, h2, hfs⟩
          exact step2_falsification_backward rule v (Or.inr hfp)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

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

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of completeness_G := completeness_by_complexity (sequentComplexity s) s rfl hv

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of search_valid_iff_proofTree := by
  -- BEGIN PROOF
    constructor
    · exact completeness_G s
    · exact soundness_G s

end LCS.Propositional.Systems.G.Search
end
