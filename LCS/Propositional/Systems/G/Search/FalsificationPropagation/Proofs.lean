import LCS.Propositional.Systems.G.Search.FalsificationPropagation

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

helper theorem ml_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Γ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

helper theorem mr_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Δ) : y ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

helper theorem mm_s {x : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    x ∈ Γ ++ [x] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.Mem.head _))))

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

helper theorem tl_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Γ) : y ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

helper theorem tr_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized}
    {y : PropFormulaNormalized} (h : y ∈ Δ) : y ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

helper theorem tf_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    A ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.Mem.head _))))

helper theorem ts_s {A B : PropFormulaNormalized} {Γ Δ : List PropFormulaNormalized} :
    B ∈ Γ ++ [A, B] ++ Δ :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.Mem.tail _ (List.Mem.head _)))))

helper theorem boolval_T_or_F (b : BoolVal) : b = BoolVal.T ∨ b = BoolVal.F := by
-- BEGIN PROOF
  cases b <;> simp

helper theorem conj_T_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.conj A B) = BoolVal.T) :
    evalExtN v A = BoolVal.T ∧ evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hAnd]

helper theorem disj_F_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.disj A B) = BoolVal.F) :
    evalExtN v A = BoolVal.F ∧ evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hOr]

helper theorem impl_F_parts {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.impl A B) = BoolVal.F) :
    evalExtN v A = BoolVal.T ∧ evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hImplies]

helper theorem neg_T_part {v : Valuation} {A : PropFormulaNormalized}
    (h : evalExtN v (.neg A) = BoolVal.T) :
    evalExtN v A = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> simp_all [hNeg]

helper theorem neg_F_part {v : Valuation} {A : PropFormulaNormalized}
    (h : evalExtN v (.neg A) = BoolVal.F) :
    evalExtN v A = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> simp_all [hNeg]

helper theorem conj_T_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.conj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hAnd]

helper theorem conj_F_of_left {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.conj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hAnd]

helper theorem conj_F_of_right {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.conj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hAnd]; cases evalExtN v A <;> rfl

helper theorem disj_T_of_left {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) :
    evalExtN v (.disj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hOr]

helper theorem disj_T_of_right {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.disj A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hOr]; cases evalExtN v A <;> rfl

helper theorem disj_F_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.disj A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hOr]

helper theorem impl_T_of_left_F {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.impl A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hImplies]

helper theorem impl_T_of_right_T {v : Valuation} {A B : PropFormulaNormalized}
    (hB : evalExtN v B = BoolVal.T) :
    evalExtN v (.impl A B) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hB, hImplies]; cases evalExtN v A <;> rfl

helper theorem impl_F_of_parts {v : Valuation} {A B : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) (hB : evalExtN v B = BoolVal.F) :
    evalExtN v (.impl A B) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hB, hImplies]

helper theorem neg_T_of_F {v : Valuation} {A : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.F) :
    evalExtN v (.neg A) = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hNeg]

helper theorem neg_F_of_T {v : Valuation} {A : PropFormulaNormalized}
    (hA : evalExtN v A = BoolVal.T) :
    evalExtN v (.neg A) = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hNeg]

helper theorem impl_T_right_of_left_T {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.impl A B) = BoolVal.T) (hA : evalExtN v A = BoolVal.T) :
    evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN, hA, hImplies] at h
  cases hb : evalExtN v B <;> simp_all

helper theorem disj_T_right_of_left_F {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.disj A B) = BoolVal.T) (hA : evalExtN v A = BoolVal.F) :
    evalExtN v B = BoolVal.T := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hOr]

helper theorem conj_F_right_of_left_T {v : Valuation} {A B : PropFormulaNormalized}
    (h : evalExtN v (.conj A B) = BoolVal.F) (hA : evalExtN v A = BoolVal.T) :
    evalExtN v B = BoolVal.F := by
-- BEGIN PROOF
  simp only [evalExtN] at h
  cases ha : evalExtN v A <;> cases hb : evalExtN v B <;> simp_all [hAnd]

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

proof_of rule_falsification_step1_iff := by
  -- BEGIN PROOF
    exact ⟨step1_falsification_forward rule v, step1_falsification_backward rule v⟩

proof_of rule_falsification_step2_iff := by
  -- BEGIN PROOF
    exact ⟨step2_falsification_forward rule v, step2_falsification_backward rule v⟩

end LCS.Propositional.Systems.G.Search
end
