import LCS.Resolution.GCNF

namespace LCS.Resolution.GCNF

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Systems.G.NormalForms

proof_of Clause.single_eq_ofList_singleton := by
  -- BEGIN PROOF
    unfold Clause.single Clause.ofList
    apply LCS.Finset.ext; intro x
    simp [LCS.Finset.mem_singleton, LCS.Finset.mem_ofList, List.mem_cons]


proof_of Clause.ofList_singleton_eq_single := (Clause.single_eq_ofList_singleton L).symm
  -- BEGIN PROOF


proof_of Clause.single_ordinary := Clause.ordinary_of_mem ((LCS.Finset.mem_singleton _ _).mpr rfl)


proof_of Clause.ofList_cons_ordinary := Clause.ordinary_of_mem (LCS.Finset.mem_ofList.mpr (List.mem_cons.mpr (Or.inl rfl)))


proof_of ClauseSequent.ordinary_subset := fun C hC => h C (hSub C hC)


proof_of ClauseSequent.ordinary_union := by
  intro C hC
  exact ((LCS.Finset.mem_union_exp _ _ _).mp hC).elim (hS C) (hT C)


proof_of ClauseSequent.ordinary_single := by
  intro D hD
  exact (LCS.Finset.mem_singleton D C).mp hD ▸ h


proof_of ClauseSequent.ordinary_ofList := fun C hC => h C (LCS.Finset.mem_ofList.mp hC)


proof_of clauseWithLiteral_single := by
  apply LCS.Finset.ext
  intro L
  simp [clauseWithLiteral, Clause.single, Clause.ofList, LCS.Finset.mem_insert,
    LCS.Finset.mem_ofList, or_comm]


proof_of clauseWithLiteral_ofList := by
  apply LCS.Finset.ext
  intro M
  simp [clauseWithLiteral, Clause.ofList, or_comm]


proof_of clauseOfList_swap := by
  apply LCS.Finset.ext
  intro N
  simp [Clause.ofList, or_comm]


proof_of GCNFProofTree.ordinary := @fun
  | _, .axiom_ _ h _ => h
  | _, .rule Gamma As B _ _ _ hGamma _ _ _ _ _ _ _ => by
    apply ClauseSequent.ordinary_union hGamma
    intro C hC
    obtain ⟨A, _, rfl⟩ := LCS.Finset.mem_image.mp hC
    exact Clause.ordinary_of_mem (LCS.Finset.mem_insert.mpr (Or.inl rfl))

namespace GCNFProofTree

proof_of leafCount_cast := open LCS.Resolution.GCNF.Proofs.GCNFProofTree in
  by
    cases h
    rfl

helper @[simp] theorem GCNFProofTree.weaken_leafCount {S : ClauseSequent} (t : GCNFProofTree S)
    (Extra : ClauseSequent) (hExtra : Extra.isOrdinary) :
    (t.weaken Extra hExtra).leafCount = t.leafCount := by
  cases t <;> simp [weaken, leafCount, cast_eq]

helper theorem GCNFProofTree.nodeCount_eq_two_leafCount_sub_one {S : ClauseSequent} (t : GCNFProofTree S) :
    t.nodeCount + 1 = 2 * t.leafCount := by
  induction t with
  | axiom_ => rfl
  | rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
    simp only [nodeCount, leafCount]
    omega

end GCNFProofTree

proof_of gcnf_axiom_valid := by
  -- BEGIN PROOF
    constructor
    · -- Axiom validity: trivial sequents are valid (unsatisfiable)
      intro S ⟨P, hPos, hNeg⟩ ⟨v, hSat⟩
      have hSatPos := hSat (Clause.single (Literal.pos P)) hPos
      have hSatNeg := hSat (Clause.single (Literal.neg P)) hNeg
      obtain ⟨L1, hL1mem, hL1sat⟩ := hSatPos
      have hL1eq : L1 = Literal.pos P := by
        show L1 = Literal.pos P
        exact (LCS.Finset.mem_singleton L1 (Literal.pos P)).mp hL1mem
      subst hL1eq
      obtain ⟨L2, hL2mem, hL2sat⟩ := hSatNeg
      have hL2eq : L2 = Literal.neg P := by
        show L2 = Literal.neg P
        exact (LCS.Finset.mem_singleton L2 (Literal.neg P)).mp hL2mem
      subst hL2eq
      simp [Literal.satisfiedBy] at hL1sat hL2sat
      rw [hL1sat] at hL2sat; exact absurd hL2sat (by decide)
    · intro Gamma As B Cs Gamma1 Gamma2 v _hCsNe hCsSub hG1Sub hG2Sub hLeft hRight hSat
      by_cases hB : Literal.satisfiedBy B v
      · apply hRight
        intro C hC
        rcases (LCS.Finset.mem_union_exp _ _ _).mp hC with hC | hC
        · exact hSat C (hG2Sub C hC)
        · have hEq := (LCS.Finset.mem_singleton _ _).mp hC
          subst C
          exact ⟨B, (LCS.Finset.mem_singleton _ _).mpr rfl, hB⟩
      · apply hLeft
        intro C hC
        rcases (LCS.Finset.mem_union_exp _ _ _).mp hC with hC | hC
        · exact hSat C (hG1Sub C hC)
        · have hAug : clauseWithLiteral C B ∈ LCS.Finset.union Gamma
              (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
            (LCS.Finset.mem_union_exp _ _ _).mpr
              (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCsSub C hC, rfl⟩))
          obtain ⟨L, hL, hTrue⟩ := hSat _ hAug
          rcases (LCS.Finset.mem_insert_exp B L C).mp hL with hEq | hMem
          · subst L; exact False.elim (hB hTrue)
          · exact ⟨L, hMem, hTrue⟩


proof_of gcnf_soundness := by
  -- BEGIN PROOF
    obtain ⟨t⟩ := h
    induction t with
    | axiom_ S _hOrd hTriv =>
      exact gcnf_axiom_valid.1 S hTriv
    | rule Gamma As B Cs Gamma1 Gamma2 _hGamma _hAs _leftTree _rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
      intro ⟨v, hSat⟩
      -- The conclusion is Gamma ∪ {clauseWithLiteral A B | A ∈ As}
      -- Case split on whether B is satisfied by v
      by_cases hBv : Literal.satisfiedBy B v
      · -- B is satisfied: right premise Gamma2 ∪ {{B}} is satisfied
        apply ihR; exact ⟨v, fun C hC => by
          cases (LCS.Finset.mem_union_exp C Gamma2 (ClauseSequent.single (Clause.single B))).mp hC with
          | inl hG2 => exact hSat C (hG2Sub C hG2)
          | inr hSing =>
            have : C = Clause.single B := (LCS.Finset.mem_singleton C (Clause.single B)).mp hSing
            subst this
            exact ⟨B, (LCS.Finset.mem_singleton B B).mpr rfl, hBv⟩⟩
      · -- B is not satisfied: left premise Gamma1 ∪ Cs is satisfied
        apply ihL; exact ⟨v, fun C hC => by
          cases (LCS.Finset.mem_union_exp C Gamma1 Cs).mp hC with
          | inl hG1 => exact hSat C (hG1Sub C hG1)
          | inr hCs =>
            -- C ∈ Cs ⊆ As, so clauseWithLiteral C B ∈ conclusion
            have hCinAs := hCsSub C hCs
            have hCWBinConc : clauseWithLiteral C B ∈
                LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
              (LCS.Finset.mem_union_exp _ Gamma _).mpr
                (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCinAs, rfl⟩))
            -- v satisfies clauseWithLiteral C B = insert B C
            obtain ⟨L, hLmem, hLsat⟩ := hSat _ hCWBinConc
            cases (LCS.Finset.mem_insert_exp B L C).mp hLmem with
            | inl hLeqB =>
              -- L = B, but B is not satisfied — contradiction
              subst hLeqB; exact absurd hLsat hBv
            | inr hLC => exact ⟨L, hLC, hLsat⟩⟩


helper theorem clauseSeq_compatible (s : Sequent) (h : ProofTree.isClauseSequent s) :
    isClauseCompatible s := by
-- BEGIN PROOF
  obtain ⟨hSucc, hAnt⟩ := h
  constructor
  · intro A hA; exact Or.inl (hAnt A hA)
  · intro B hB; rw [hSucc] at hB; exact absurd hB (by simp)

helper def fmlaSize : PropFormulaNormalized → Nat
  | .var _ => 0
  | .neg A => 1 + fmlaSize A
  | .conj A B => 1 + fmlaSize A + fmlaSize B
  | .disj A B => 1 + fmlaSize A + fmlaSize B
  | .impl A B => 1 + fmlaSize A + fmlaSize B

helper def listSize : List PropFormulaNormalized → Nat
  | [] => 0
  | A :: L => fmlaSize A + listSize L

helper def seqSize (s : Sequent) : Nat :=
  listSize s.antecedent + listSize s.succedent

helper theorem listSize_cons (A : PropFormulaNormalized) (L : List PropFormulaNormalized) :
    listSize (A :: L) = fmlaSize A + listSize L := rfl

helper theorem listSize_append (L1 L2 : List PropFormulaNormalized) :
    listSize (L1 ++ L2) = listSize L1 + listSize L2 := by
-- BEGIN PROOF
  induction L1 with
  | nil => simp [listSize]
  | cons hd tl ih => simp [listSize, ih]; omega

helper theorem negLeft_backward_valid
    (Γ Δ Λ : List PropFormulaNormalized) (A : PropFormulaNormalized)
    (hValid : sequentValid (Sequent.mk (Γ ++ [.neg A] ++ Δ) Λ)) :
    sequentValid (Sequent.mk (Γ ++ Δ) ([A] ++ Λ)) := by
-- BEGIN PROOF
  intro v hAnt
  by_cases ha : evalExtN v A = BoolVal.T
  · exact ⟨A, List.mem_cons.mpr (Or.inl rfl), ha⟩
  · have hAF : evalExtN v A = BoolVal.F := by
      cases h : evalExtN v A with | T => exact absurd h ha | F => rfl
    have hNegAT : evalExtN v (.neg A) = BoolVal.T := by
      simp only [evalExtN, hNeg, hAF]
    have hAntConc : ∀ X ∈ (Γ ++ [.neg A] ++ Δ), evalExtN v X = BoolVal.T := by
      intro X hX
      rcases List.mem_append.mp hX with h1 | h2
      · rcases List.mem_append.mp h1 with hΓ | hNA
        · exact hAnt X (List.mem_append.mpr (Or.inl hΓ))
        · simp at hNA; exact hNA ▸ hNegAT
      · exact hAnt X (List.mem_append.mpr (Or.inr h2))
    obtain ⟨B, hBmem, hBT⟩ := hValid v hAntConc
    exact ⟨B, List.mem_cons.mpr (Or.inr hBmem), hBT⟩

helper theorem orLeft_backward_valid_left
    (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized)
    (hValid : sequentValid (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ)) :
    sequentValid (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  intro v hAnt
  have hAntConc : ∀ X ∈ (Γ ++ [.disj A B] ++ Δ), evalExtN v X = BoolVal.T := by
    intro X hX
    rcases List.mem_append.mp hX with h1 | h2
    · rcases List.mem_append.mp h1 with hΓ | hAB
      · exact hAnt X (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hΓ))))
      · simp at hAB; subst hAB
        have hAT := hAnt A (List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
        simp only [evalExtN, hOr, hAT]
    · exact hAnt X (List.mem_append.mpr (Or.inr h2))
  exact hValid v hAntConc

helper theorem orLeft_backward_valid_right
    (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized)
    (hValid : sequentValid (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ)) :
    sequentValid (Sequent.mk (Γ ++ [B] ++ Δ) Λ) := by
-- BEGIN PROOF
  intro v hAnt
  have hAntConc : ∀ X ∈ (Γ ++ [.disj A B] ++ Δ), evalExtN v X = BoolVal.T := by
    intro X hX
    rcases List.mem_append.mp hX with h1 | h2
    · rcases List.mem_append.mp h1 with hΓ | hAB
      · exact hAnt X (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hΓ))))
      · simp at hAB; subst hAB
        have hBT := hAnt B (List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
        simp only [evalExtN, hOr, hBT]
        cases evalExtN v A <;> rfl
    · exact hAnt X (List.mem_append.mpr (Or.inr h2))
  exact hValid v hAntConc

helper theorem allVar_valid_isAxiom (s : Sequent)
    (hAntVar : ∀ A ∈ s.antecedent, ∃ n, A = .var n)
    (hSuccVar : ∀ B ∈ s.succedent, ∃ n, B = .var n)
    (hValid : sequentValid s) :
    isAxiom s := by
-- BEGIN PROOF
  -- By contradiction: if no common formula, construct a falsifying valuation
  suffices h : ¬isAxiom s → False from Classical.byContradiction fun hNA => h hNA
  intro hNotAxiom
  -- Build valuation: antecedent vars true, everything else false
  have hDisjoint : ∀ A, A ∈ s.antecedent → A ∉ s.succedent :=
    fun A hA hS => hNotAxiom ⟨A, hA, hS⟩
  let v : Valuation := fun n =>
    if (PropFormulaNormalized.var n) ∈ s.antecedent then BoolVal.T else BoolVal.F
  have hAntTrue : ∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T := by
    intro A hA; obtain ⟨n, rfl⟩ := hAntVar A hA
    simp only [evalExtN, v, hA, ite_true]
  obtain ⟨B, hBmem, hBT⟩ := hValid v hAntTrue
  obtain ⟨m, rfl⟩ := hSuccVar B hBmem
  -- .var m is in succedent but not in antecedent (by disjointness)
  have hNot : (PropFormulaNormalized.var m) ∉ s.antecedent :=
    fun hContra => hDisjoint _ hContra hBmem
  -- So v m = BoolVal.F, but hBT says evalExtN v (.var m) = BoolVal.T
  have : evalExtN v (.var m) = BoolVal.F := by
    simp only [evalExtN, v, hNot, ite_false]
  exact absurd hBT (by rw [this]; decide)

helper theorem find_nonvar_in_list (L : List PropFormulaNormalized)
    (hSz : listSize L > 0) :
    ∃ Γ Δ A, L = Γ ++ [A] ++ Δ ∧ fmlaSize A > 0 := by
-- BEGIN PROOF
  induction L with
  | nil => exact absurd hSz (by simp [listSize])
  | cons hd tl ih =>
    by_cases hhd : fmlaSize hd > 0
    · exact ⟨[], tl, hd, by simp, hhd⟩
    · have hhd0 : fmlaSize hd = 0 := by omega
      rw [listSize_cons] at hSz
      have htlSz : listSize tl > 0 := by omega
      obtain ⟨Γ, Δ, A, hEq, hA⟩ := ih htlSz
      exact ⟨hd :: Γ, Δ, A, by rw [hEq]; simp [List.cons_append], hA⟩

helper theorem clauseCompat_pos_cases (A : PropFormulaNormalized)
    (hCC : isClauseN A ∨ ∃ n, A = .var n)
    (hPos : fmlaSize A > 0) :
    (∃ n, A = .neg (.var n)) ∨
    (∃ B C, A = .disj B C ∧ (isClauseN B ∨ ∃ m, B = .var m) ∧
                               (isClauseN C ∨ ∃ m, C = .var m)) := by
-- BEGIN PROOF
  rcases hCC with hCl | ⟨n, rfl⟩
  · cases A with
    | var _ => simp [fmlaSize] at hPos
    | neg A' =>
      cases A' with
      | var n => exact Or.inl ⟨n, rfl⟩
      | _ => simp [isClauseN] at hCl
    | disj B C =>
      simp [isClauseN] at hCl
      exact Or.inr ⟨B, C, rfl, Or.inl hCl.1, Or.inl hCl.2⟩
    | _ => simp [isClauseN] at hCl
  · simp [fmlaSize] at hPos

helper theorem negLeft_size_decrease (Γ Δ Λ : List PropFormulaNormalized) (n : Nat) :
    seqSize (Sequent.mk (Γ ++ Δ) ([.var n] ++ Λ)) <
    seqSize (Sequent.mk (Γ ++ [.neg (.var n)] ++ Δ) Λ) := by
-- BEGIN PROOF
  simp only [seqSize, listSize_append, listSize, fmlaSize]
  omega

helper theorem orLeft_size_decrease_left (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
    seqSize (Sequent.mk (Γ ++ [A] ++ Δ) Λ) <
    seqSize (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ) := by
-- BEGIN PROOF
  simp only [seqSize, listSize_append, listSize, fmlaSize]
  omega

helper theorem orLeft_size_decrease_right (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
    seqSize (Sequent.mk (Γ ++ [B] ++ Δ) Λ) <
    seqSize (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ) := by
-- BEGIN PROOF
  simp only [seqSize, listSize_append, listSize, fmlaSize]
  omega

helper theorem negLeft_preserves_compat (Γ Δ Λ : List PropFormulaNormalized) (n : Nat)
    (hCC : isClauseCompatible (Sequent.mk (Γ ++ [.neg (.var n)] ++ Δ) Λ)) :
    isClauseCompatible (Sequent.mk (Γ ++ Δ) ([.var n] ++ Λ)) := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hCC
  constructor
  · intro A hA
    rcases List.mem_append.mp hA with hΓ | hΔ
    · exact hAnt A (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hΓ))))
    · exact hAnt A (List.mem_append.mpr (Or.inr hΔ))
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hΛ
    · exact ⟨n, rfl⟩
    · exact hSucc B hΛ

helper theorem orLeft_preserves_compat_left (Γ Δ Λ : List PropFormulaNormalized)
    (A B : PropFormulaNormalized)
    (hCC : isClauseCompatible (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ))
    (hA : isClauseN A ∨ ∃ m, A = .var m) :
    isClauseCompatible (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hCC
  constructor
  · intro X hX
    rcases List.mem_append.mp hX with h1 | h2
    · rcases List.mem_append.mp h1 with hΓ | hAs
      · exact hAnt X (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hΓ))))
      · simp at hAs; subst hAs; exact hA
    · exact hAnt X (List.mem_append.mpr (Or.inr h2))
  · exact hSucc

helper theorem orLeft_preserves_compat_right (Γ Δ Λ : List PropFormulaNormalized)
    (A B : PropFormulaNormalized)
    (hCC : isClauseCompatible (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ))
    (hB : isClauseN B ∨ ∃ m, B = .var m) :
    isClauseCompatible (Sequent.mk (Γ ++ [B] ++ Δ) Λ) := by
-- BEGIN PROOF
  obtain ⟨hAnt, hSucc⟩ := hCC
  constructor
  · intro X hX
    rcases List.mem_append.mp hX with h1 | h2
    · rcases List.mem_append.mp h1 with hΓ | hBs
      · exact hAnt X (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hΓ))))
      · simp at hBs; subst hBs; exact hB
    · exact hAnt X (List.mem_append.mpr (Or.inr h2))
  · exact hSucc

helper theorem listSize_zero_all_zero (L : List PropFormulaNormalized)
    (h : listSize L = 0) : ∀ A ∈ L, fmlaSize A = 0 := by
-- BEGIN PROOF
  induction L with
  | nil => intro A hA; exact absurd hA (by simp)
  | cons hd tl ih =>
    rw [listSize_cons] at h
    have hhd : fmlaSize hd = 0 := by omega
    have htl : listSize tl = 0 := by omega
    intro A hA
    rcases List.mem_cons.mp hA with rfl | htlA
    · exact hhd
    · exact ih htl A htlA

helper /-- Locate a displayed formula occurrence, retaining both ordered contexts. -/
theorem formula_mem_split {A : PropFormulaNormalized} {L : List PropFormulaNormalized}
    (h : A ∈ L) : ∃ Γ Δ, L = Γ ++ [A] ++ Δ := by
  induction L with
  | nil => simp at h
  | cons B L ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], L, rfl⟩
    · obtain ⟨Γ, Δ, hEq⟩ := ih h
      exact ⟨B :: Γ, Δ, by simp [hEq]⟩

helper /-- Backward proof search gives priority to every available disjunction.
    Once only literals remain, the constructed subtree has no disjunction rule. -/
theorem build_normal_form_proof (bound : Nat) :
    ∀ (s : Sequent), seqSize s ≤ bound → isClauseCompatible s → sequentValid s →
    ∃ pt : ProofTree s, ProofTree.negLeftPrecedesOrLeft pt ∧
      ((∀ A B, PropFormulaNormalized.disj A B ∉ s.antecedent) → ProofTree.noOrLeft pt) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro s hBound hCC hValid
    by_cases hSplit : ∃ Γ Δ B C, s.antecedent = Γ ++ [.disj B C] ++ Δ
    · obtain ⟨Γ, Δ, B, C, hAntEq⟩ := hSplit
      have hSeqEq : s = Sequent.mk (Γ ++ [.disj B C] ++ Δ) s.succedent := by
        cases s; simp at hAntEq ⊢; exact hAntEq
      have hParts : isClauseN B ∧ isClauseN C := by
        have h := hCC.1 (.disj B C) (by simp [hAntEq])
        rcases h with h | ⟨n, h⟩
        · exact h
        · cases h
      have hCCr := hSeqEq ▸ hCC
      have hValidr := hSeqEq ▸ hValid
      let premL := Sequent.mk (Γ ++ [B] ++ Δ) s.succedent
      let premR := Sequent.mk (Γ ++ [C] ++ Δ) s.succedent
      have hLSz : seqSize premL < seqSize s := by
        rw [hSeqEq]; exact orLeft_size_decrease_left Γ Δ s.succedent B C
      have hRSz : seqSize premR < seqSize s := by
        rw [hSeqEq]; exact orLeft_size_decrease_right Γ Δ s.succedent B C
      obtain ⟨ptL, hLP, _⟩ := ih (seqSize premL) (by omega) premL (Nat.le_refl _)
        (orLeft_preserves_compat_left Γ Δ s.succedent B C hCCr (Or.inl hParts.1))
        (orLeft_backward_valid_left Γ Δ s.succedent B C hValidr)
      obtain ⟨ptR, hRP, _⟩ := ih (seqSize premR) (by omega) premR (Nat.le_refl _)
        (orLeft_preserves_compat_right Γ Δ s.succedent B C hCCr (Or.inl hParts.2))
        (orLeft_backward_valid_right Γ Δ s.succedent B C hValidr)
      rw [hSeqEq]
      refine ⟨.twoPremise (.orLeft Γ Δ s.succedent B C) ptL ptR, ⟨hLP, hRP⟩, ?_⟩
      intro hNo
      exact False.elim (hNo B C (by simp))
    · have hNo : ∀ B C, PropFormulaNormalized.disj B C ∉ s.antecedent := by
        intro B C hMem
        obtain ⟨Γ, Δ, hEq⟩ := formula_mem_split hMem
        exact hSplit ⟨Γ, Δ, B, C, hEq⟩
      by_cases hAllVar : listSize s.antecedent = 0
      · have hAntVar : ∀ A ∈ s.antecedent, ∃ n, A = .var n := by
          intro A hA
          have hSz := listSize_zero_all_zero s.antecedent hAllVar A hA
          rcases hCC.1 A hA with hCl | ⟨n, rfl⟩
          · cases A with
            | var n => exact ⟨n, rfl⟩
            | neg _ => simp [fmlaSize] at hSz
            | disj _ _ => simp [fmlaSize] at hSz
            | _ => simp [isClauseN] at hCl
          · exact ⟨n, rfl⟩
        exact ⟨.axiom_ s (allVar_valid_isAxiom s hAntVar hCC.2 hValid), trivial,
          fun _ => trivial⟩
      · obtain ⟨Γ, Δ, A, hAntEq, hASz⟩ := find_nonvar_in_list s.antecedent (by omega)
        have hMem : A ∈ s.antecedent := by simp [hAntEq]
        rcases clauseCompat_pos_cases A (hCC.1 A hMem) hASz with
          ⟨n, rfl⟩ | ⟨B, C, rfl, _, _⟩
        · have hSeqEq : s = Sequent.mk (Γ ++ [.neg (.var n)] ++ Δ) s.succedent := by
            cases s; simp at hAntEq ⊢; exact hAntEq
          let prem := Sequent.mk (Γ ++ Δ) ([.var n] ++ s.succedent)
          have hSz : seqSize prem < seqSize s := by
            rw [hSeqEq]; exact negLeft_size_decrease Γ Δ s.succedent n
          obtain ⟨pt, hP, hNoPt⟩ := ih (seqSize prem) (by omega) prem (Nat.le_refl _)
            (negLeft_preserves_compat Γ Δ s.succedent n (hSeqEq ▸ hCC))
            (negLeft_backward_valid Γ Δ s.succedent (.var n) (hSeqEq ▸ hValid))
          have hNoPrem : ∀ B C, PropFormulaNormalized.disj B C ∉ prem.antecedent := by
            intro B C h
            apply hNo B C
            simpa [hAntEq, prem] using h
          have hNoTree := hNoPt hNoPrem
          rw [hSeqEq]
          exact ⟨.onePremise (.negLeft Γ Δ s.succedent (.var n)) pt,
            ⟨hP, hNoTree⟩, fun _ => hNoTree⟩
        · exact False.elim (hNo B C hMem)

helper theorem commute_to_normal_form
    (S : Sequent)
    (pt : ProofTree S)
    (hClause : ProofTree.isClauseSequent S) :
    ∃ pt' : ProofTree S, ProofTree.negLeftPrecedesOrLeft pt' := by
-- BEGIN PROOF
  -- Step 1: Get validity from soundness
  have hValid : sequentValid S := soundness_G S ⟨pt⟩
  -- Step 2: Clause sequent is clause-compatible
  have hCC := clauseSeq_compatible S hClause
  -- Step 3: Build a proof tree satisfying both properties
  obtain ⟨pt', hPrec, _⟩ := build_normal_form_proof (seqSize S) S (Nat.le_refl _) hCC hValid
  exact ⟨pt', hPrec⟩

proof_of gPrime_proof_normal_form := commute_to_normal_form S pt hClause
  -- BEGIN PROOF

open Classical

helper /-- A witness for the complete restricted-context variant. -/
def GCNFRestrictedProvable (S : ClauseSequent) : Prop :=
  ∃ t : GCNFProofTree S, t.restrictedContexts

helper /-- Helper: construct a GCNF' proof tree for Gamma ∪ {clauseWithLiteral A B}. -/
theorem gcnf_provable_step
    (Gamma : ClauseSequent) (A : Clause) (B : Literal)
    (ihLeft : GCNFRestrictedProvable (LCS.Finset.union Gamma (ClauseSequent.single A)))
    (ihRight : GCNFRestrictedProvable (LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B)))) :
    GCNFRestrictedProvable (LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B))) := by
-- BEGIN PROOF
  obtain ⟨leftTree, hLeft⟩ := ihLeft
  obtain ⟨rightTree, hRight⟩ := ihRight
  have heq : LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      LCS.Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply LCS.Finset.ext; intro C
    constructor
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'
        rw [mem_csingle]; exact hCA'.symm
  rw [heq]
  exact ⟨GCNFProofTree.rule Gamma (ClauseSequent.single A) B (ClauseSequent.single A)
    Gamma Gamma
    (ClauseSequent.ordinary_subset leftTree.ordinary (fun C hC => LCS.Finset.mem_union.mpr (Or.inl hC)))
    (ClauseSequent.ordinary_subset leftTree.ordinary (fun C hC => LCS.Finset.mem_union.mpr (Or.inr hC)))
    leftTree rightTree
    ⟨A, (LCS.Finset.mem_singleton A A).mpr rfl⟩
    (fun C hC => hC)
    (fun _ h => (LCS.Finset.mem_union_exp _ Gamma _).mpr (Or.inl h))
    (fun _ h => (LCS.Finset.mem_union_exp _ Gamma _).mpr (Or.inl h)),
    ⟨fun _ h => h, fun _ h => h, hLeft, hRight⟩⟩

proof_of ofList_replace_eq_union := by
  -- BEGIN PROOF
    apply LCS.Finset.ext; intro D
    constructor
    · intro hD
      rw [LCS.Finset.mem_ofList] at hD
      rw [LCS.Finset.mem_union]
      rw [List.mem_append, List.mem_cons] at hD
      rcases hD with hPre | (rfl | hSuf)
      · exact Or.inl ((LCS.Finset.mem_ofList_exp D (pre ++ suf)).mpr (List.mem_append.mpr (Or.inl hPre)))
      · exact Or.inr ((LCS.Finset.mem_singleton D D).mpr rfl)
      · exact Or.inl ((LCS.Finset.mem_ofList_exp D (pre ++ suf)).mpr (List.mem_append.mpr (Or.inr hSuf)))
    · intro hD
      rw [LCS.Finset.mem_union] at hD
      rw [LCS.Finset.mem_ofList]
      rcases hD with hPS | hSing
      · rw [LCS.Finset.mem_ofList] at hPS
        rw [List.mem_append] at hPS
        rcases hPS with hPre | hSuf
        · exact List.mem_append.mpr (Or.inl hPre)
        · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf)))
      · rw [mem_csingle] at hSing
        rw [hSing]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))


helper /-- Helper: combine provability of left and right branches. -/
theorem ofList_provable_step
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (ihLeft : GCNFRestrictedProvable (LCS.Finset.ofList (pre ++ A :: suf)))
    (ihRight : GCNFRestrictedProvable (LCS.Finset.ofList (pre ++ Clause.single B :: suf))) :
    GCNFRestrictedProvable (LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf)) := by
-- BEGIN PROOF
  let Gamma := LCS.Finset.ofList (pre ++ suf)
  have heqL : LCS.Finset.ofList (pre ++ A :: suf) = LCS.Finset.union Gamma (ClauseSequent.single A) :=
    ofList_replace_eq_union pre suf A
  have heqR : LCS.Finset.ofList (pre ++ Clause.single B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B)) :=
    ofList_replace_eq_union pre suf (Clause.single B)
  have heqC : LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) :=
    ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  rw [heqC]
  rw [heqL] at ihLeft
  rw [heqR] at ihRight
  exact gcnf_provable_step Gamma A B ihLeft ihRight

helper /-- Core completeness lemma: well-founded induction on total literal count. -/
theorem gcnf_provable_of_lit_lists :
    ∀ (ll : List (List Literal)),
    (∀ ls ∈ ll, ls ≠ []) →
    ClauseSequent.isValid (litListsToClauseSeq ll) →
    GCNFRestrictedProvable (litListsToClauseSeq ll) := by
-- BEGIN PROOF
  suffices hwf : ∀ (n : Nat) (ll : List (List Literal)),
      totalLitCount ll ≤ n →
      (∀ ls ∈ ll, ls ≠ []) →
      ClauseSequent.isValid (litListsToClauseSeq ll) →
      GCNFRestrictedProvable (litListsToClauseSeq ll) from
    fun ll hNe hValid => hwf (totalLitCount ll) ll (Nat.le_refl _) hNe hValid
  intro n
  induction n with
  | zero =>
    intro ll hBound hNe hValid
    have hEmpty : ll = [] := by
      cases ll with
      | nil => rfl
      | cons hd tl =>
        have hhdNe := hNe hd (List.mem_cons.mpr (Or.inl rfl))
        rw [totalLitCount_cons] at hBound
        have : hd.length ≥ 1 := by
          cases hd with
          | nil => exact absurd rfl hhdNe
          | cons _ _ => simp
        omega
    subst hEmpty
    exfalso; apply hValid
    exact ⟨fun _ => true, fun C hC => absurd ((LCS.Finset.mem_ofList_exp C []).mp hC) List.not_mem_nil⟩
  | succ n ih =>
    intro ll hBound hNe hValid
    by_cases hAllSingle : ∀ ls ∈ ll, ∃ L, ls = [L]
    · have hSingle : ∀ C ∈ litListsToClauseSeq ll, ∃ L : Literal, C = Clause.single L := by
        intro C hC
        change C ∈ LCS.Finset.ofList (List.map Clause.ofList ll) at hC
        rw [LCS.Finset.mem_ofList] at hC
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hC
        obtain ⟨L, rfl⟩ := hAllSingle ls hls
        exact ⟨L, ofList_singleton_eq L⟩
      have hTriv := singletons_valid_imp_trivial (litListsToClauseSeq ll) hSingle hValid
      obtain ⟨P, hPos, hNeg⟩ := hTriv
      exact ⟨GCNFProofTree.axiom_ _ (by
        intro C hC
        obtain ⟨L, rfl⟩ := hSingle C hC
        exact Clause.single_ordinary L) ⟨P, hPos, hNeg⟩, by trivial⟩
    · have ⟨ls, hls_mem, hls_not_single⟩ : ∃ ls ∈ ll, ∀ L, ls ≠ [L] :=
        Classical.byContradiction fun hAll => hAllSingle fun ls hls =>
          Classical.byContradiction fun hNo =>
            hAll ⟨ls, hls, fun L hEq => hNo ⟨L, hEq⟩⟩
      have hls_ne := hNe ls hls_mem
      obtain ⟨L, rest, rfl⟩ : ∃ L rest, ls = L :: rest := by
        cases ls with
        | nil => exact absurd rfl hls_ne
        | cons hd tl => exact ⟨hd, tl, rfl⟩
      have hrest_ne : rest ≠ [] := by
        intro h; subst h; exact hls_not_single L rfl
      have mem_split : ∀ (xs : List (List Literal)) (x : List Literal),
          x ∈ xs → ∃ pre suf, xs = pre ++ x :: suf := by
        intro xs x hx
        induction xs with
        | nil => exact absurd hx List.not_mem_nil
        | cons hd tl ih_s =>
          rw [List.mem_cons] at hx
          rcases hx with rfl | htl
          · exact ⟨[], tl, by simp⟩
          · obtain ⟨pre', suf', heq'⟩ := ih_s htl
            exact ⟨hd :: pre', suf', by rw [heq', List.cons_append]⟩
      obtain ⟨pre, suf, hll_eq⟩ := mem_split ll (L :: rest) hls_mem
      have hclause_eq : Clause.ofList (L :: rest) = clauseWithLiteral (Clause.ofList rest) L :=
        (clauseWithLiteral_ofList_cons L rest).symm
      have hll_map2 : ll.map Clause.ofList =
          pre.map Clause.ofList ++ clauseWithLiteral (Clause.ofList rest) L :: suf.map Clause.ofList := by
        rw [hll_eq, List.map_append, List.map_cons, hclause_eq]
      have hseq_eq : litListsToClauseSeq ll =
          LCS.Finset.ofList (pre.map Clause.ofList ++ clauseWithLiteral (Clause.ofList rest) L :: suf.map Clause.ofList) := by
        show LCS.Finset.ofList (ll.map Clause.ofList) = _
        rw [hll_map2]
      rw [hseq_eq]; rw [hseq_eq] at hValid
      have hLeftValid : ClauseSequent.isValid
          (LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.ofList rest :: suf.map Clause.ofList)) :=
        ofList_left_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hRightValid : ClauseSequent.isValid
          (LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.single L :: suf.map Clause.ofList)) :=
        ofList_right_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hLeftEq : LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.ofList rest :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ rest :: suf) := by
        simp only [litListsToClauseSeq, List.map_append, List.map_cons]
      have hRightEq : LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.single L :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ [L] :: suf) := by
        unfold litListsToClauseSeq
        simp only [List.map_append, List.map_cons]
        rw [ofList_singleton_eq]
      have hLeftSize : totalLitCount (pre ++ rest :: suf) < totalLitCount ll := by
        rw [hll_eq]
        exact totalLitCount_replace_lt pre (L :: rest) suf rest (by simp)
      have hRightSize : totalLitCount (pre ++ [L] :: suf) < totalLitCount ll := by
        rw [hll_eq]
        apply totalLitCount_replace_lt pre (L :: rest) suf [L]
        cases rest with
        | nil => exact absurd rfl hrest_ne
        | cons _ _ => simp
      have hNe' : ∀ ls ∈ pre ++ (L :: rest) :: suf, ls ≠ [] := hll_eq ▸ hNe
      have hLeftNe : ∀ ls ∈ pre ++ rest :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact hrest_ne
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have hRightNe : ∀ ls ∈ pre ++ [L] :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact List.cons_ne_nil L []
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have ihL : GCNFRestrictedProvable (litListsToClauseSeq (pre ++ rest :: suf)) :=
        ih (pre ++ rest :: suf) (by omega) hLeftNe (hLeftEq ▸ hLeftValid)
      have ihR : GCNFRestrictedProvable (litListsToClauseSeq (pre ++ [L] :: suf)) :=
        ih (pre ++ [L] :: suf) (by omega) hRightNe (hRightEq ▸ hRightValid)
      rw [← hLeftEq] at ihL; rw [← hRightEq] at ihR
      exact ofList_provable_step (pre.map Clause.ofList) (suf.map Clause.ofList)
        (Clause.ofList rest) L ihL ihR

helper /-- Helper: mapping ofList over toList-extraction recovers the original list
    (extensionally via LCS.Finset.ofList). -/
theorem map_ofList_map_toList (l : List Clause) :
    (l.map (fun C : Clause => C.toList)).map Clause.ofList = l := by
-- BEGIN PROOF
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons]
    rw [ofList_toList_eq hd, ih]

helper /-- Helper: well-founded completeness on a list witness.
    Each clause C : LCS.Finset Literal has C.toList : List Literal (via
    Classical.choose) which is non-empty iff C ≠ Clause.empty. -/
theorem gcnf_provable_of_list (l : List Clause)
    (hNe : ∀ C ∈ l, C ≠ Clause.empty)
    (hValid : ClauseSequent.isValid (LCS.Finset.ofList l)) :
    GCNFRestrictedProvable (LCS.Finset.ofList l) := by
-- BEGIN PROOF
  let toLitList : Clause → List Literal := fun C => C.toList
  let ll := l.map toLitList
  have hMapEq : ll.map Clause.ofList = l := map_ofList_map_toList l
  have hSeqEq : litListsToClauseSeq ll = LCS.Finset.ofList l := by
    unfold litListsToClauseSeq; rw [hMapEq]
  have hllNe : ∀ ls ∈ ll, ls ≠ [] := by
    intro ls hls
    change ls ∈ List.map toLitList l at hls
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hls
    intro hempty
    -- hempty : toLitList C = []. Unfold to C.toList = [].
    have hempty' : C.toList = [] := hempty
    have hCne := hNe C hC
    apply hCne
    apply LCS.Finset.ext; intro a
    rw [show (Clause.empty : Clause) = LCS.Finset.empty from rfl]
    constructor
    · intro (ha : a ∈ C)
      -- From ha : a ∈ C, and hempty' : C.toList = [], show a ∈ empty (false).
      have : a ∈ C.toList := (LCS.Finset.mem_toList C a).mpr ha
      rw [hempty'] at this
      exact absurd this List.not_mem_nil
    · intro ha
      exact absurd ha (LCS.Finset.not_mem_empty)
  have := gcnf_provable_of_lit_lists ll hllNe (hSeqEq ▸ hValid)
  rwa [hSeqEq] at this

helper /-- The exact-pair axiom satisfies axiomsMinimal. -/
theorem pairAxiom_minimal (P : Nat) :
    (pairAxiom P).axiomsMinimal :=
-- BEGIN PROOF
  ⟨P, rfl⟩

helper /-- The pair set is a subset of any clause sequent containing the pair. -/
theorem pairSet_sub_of_trivial (S : ClauseSequent) (P : Nat)
    (hPos : Clause.single (Literal.pos P) ∈ S)
    (hNeg : Clause.single (Literal.neg P) ∈ S) :
    LCS.Finset.Subset (pairSet P) S := by
-- BEGIN PROOF
  intro C hC
  unfold pairSet at hC
  rw [LCS.Finset.mem_ofList] at hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact hPos
  · rcases List.mem_cons.mp hC with rfl | hC
    · exact hNeg
    · exact absurd hC List.not_mem_nil

helper /-- Key construction: for an all-singletons valid clause sequent S,
    build a GCNF' proof tree where every axiom is an exact complementary
    pair. -/
theorem all_singletons_exact_pair_proof (S : ClauseSequent)
    (hSingle : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L)
    (hValid : ClauseSequent.isValid S) :
    ∃ t : GCNFProofTree S, t.axiomsMinimal := by
-- BEGIN PROOF
  have hTriv := singletons_valid_imp_trivial S hSingle hValid
  obtain ⟨P, hPos, hNeg⟩ := hTriv
  by_cases hExact : S = pairSet P
  · rw [hExact]
    exact ⟨pairAxiom P, pairAxiom_minimal P⟩
  · have hCwlId : clauseWithLiteral (Clause.single (Literal.pos P)) (Literal.pos P) =
        Clause.single (Literal.pos P) :=
      clauseWithLiteral_single_self (Literal.pos P)
    -- Define Gamma as everything in S except single (pos P)
    let Gamma : ClauseSequent := LCS.Finset.erase S (Clause.single (Literal.pos P))
    have hSdecomp : S = LCS.Finset.union Gamma (ClauseSequent.mapSet
        (ClauseSequent.single (Clause.single (Literal.pos P)))
        (fun A => clauseWithLiteral A (Literal.pos P))) := by
      apply LCS.Finset.ext; intro C
      constructor
      · intro hC
        rw [LCS.Finset.mem_union]
        by_cases heq : C = Clause.single (Literal.pos P)
        · right
          show C ∈ LCS.Finset.image (fun A => clauseWithLiteral A (Literal.pos P))
            (LCS.Finset.singleton (Clause.single (Literal.pos P)))
          rw [heq]
          exact (mem_image_iff _ _ _).mpr
            ⟨Clause.single (Literal.pos P),
             (LCS.Finset.mem_singleton _ _).mpr rfl,
             hCwlId⟩
        · left
          rw [LCS.Finset.mem_erase]
          exact ⟨hC, heq⟩
      · intro hC
        rw [LCS.Finset.mem_union] at hC
        rcases hC with hG | hMap
        · rw [LCS.Finset.mem_erase] at hG; exact hG.1
        · obtain ⟨A, hA, hCA⟩ := (mem_image_iff _ _ _).mp hMap
          rw [(LCS.Finset.mem_singleton A (Clause.single (Literal.pos P))).mp hA] at hCA
          rw [hCwlId] at hCA; rw [← hCA]; exact hPos
    rw [hSdecomp]
    have hPairSub : LCS.Finset.Subset (pairSet P)
        (LCS.Finset.union Gamma (ClauseSequent.mapSet
          (ClauseSequent.single (Clause.single (Literal.pos P)))
          (fun A => clauseWithLiteral A (Literal.pos P)))) := by
      rw [← hSdecomp]; exact pairSet_sub_of_trivial S P hPos hNeg
    -- pairSet P ∪ {single (pos P)} = pairSet P
    have hPairAbsorb : LCS.Finset.union (pairSet P)
        (ClauseSequent.single (Clause.single (Literal.pos P))) = pairSet P := by
      apply LCS.Finset.ext; intro C
      constructor
      · intro hC
        rw [LCS.Finset.mem_union] at hC
        rcases hC with hP | hSing
        · exact hP
        · rw [mem_csingle] at hSing; rw [hSing]
          exact (LCS.Finset.mem_ofList_exp _ _).mpr (List.mem_cons.mpr (Or.inl rfl))
      · intro hC
        rw [LCS.Finset.mem_union]
        exact Or.inl hC
    let premTree : GCNFProofTree
        (LCS.Finset.union (pairSet P) (ClauseSequent.single (Clause.single (Literal.pos P)))) :=
      Eq.mpr (congrArg GCNFProofTree hPairAbsorb) (pairAxiom P)
    have hPremMin : premTree.axiomsMinimal := by
      suffices ∀ (T : ClauseSequent) (heq : T = pairSet P),
          (Eq.mpr (congrArg GCNFProofTree heq) (pairAxiom P)).axiomsMinimal from
        this _ hPairAbsorb
      intro T heq; subst heq; exact pairAxiom_minimal P
    refine ⟨GCNFProofTree.rule Gamma
      (ClauseSequent.single (Clause.single (Literal.pos P)))
      (Literal.pos P)
      (ClauseSequent.single (Clause.single (Literal.pos P)))
      (pairSet P) (pairSet P)
      (by
        intro C hC
        obtain ⟨L, rfl⟩ := hSingle C ((LCS.Finset.mem_erase _ _ _).mp hC).1
        exact Clause.single_ordinary L)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      premTree premTree
      ⟨Clause.single (Literal.pos P), (LCS.Finset.mem_singleton _ _).mpr rfl⟩
      (fun C hC => hC)
      hPairSub hPairSub, ?_⟩
    exact And.intro hPremMin hPremMin

helper /-- Helper: construct a GCNF' proof tree with minimal axioms for
    Gamma ∪ {clauseWithLiteral A B} by applying the GCNF' rule. -/
theorem gcnf_minimal_step
    (Gamma : ClauseSequent) (A : Clause) (B : Literal)
    (ihLeft : ∃ t : GCNFProofTree (LCS.Finset.union Gamma (ClauseSequent.single A)), t.axiomsMinimal)
    (ihRight : ∃ t : GCNFProofTree (LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B))),
      t.axiomsMinimal) :
    ∃ t : GCNFProofTree (LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B))),
      t.axiomsMinimal := by
-- BEGIN PROOF
  obtain ⟨leftTree, hLeftMin⟩ := ihLeft
  obtain ⟨rightTree, hRightMin⟩ := ihRight
  have heq : LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      LCS.Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply LCS.Finset.ext; intro C
    constructor
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'
        rw [mem_csingle]; exact hCA'.symm
  rw [heq]
  exact ⟨GCNFProofTree.rule Gamma (ClauseSequent.single A) B (ClauseSequent.single A)
    Gamma Gamma
    (ClauseSequent.ordinary_subset leftTree.ordinary (fun C hC => LCS.Finset.mem_union.mpr (Or.inl hC)))
    (ClauseSequent.ordinary_subset leftTree.ordinary (fun C hC => LCS.Finset.mem_union.mpr (Or.inr hC)))
    leftTree rightTree
    ⟨A, (LCS.Finset.mem_singleton A A).mpr rfl⟩
    (fun C hC => hC)
    (fun _ h => (LCS.Finset.mem_union_exp _ Gamma _).mpr (Or.inl h))
    (fun _ h => (LCS.Finset.mem_union_exp _ Gamma _).mpr (Or.inl h)),
    ⟨hLeftMin, hRightMin⟩⟩

helper /-- Helper: combine minimal proof trees for left and right branches
    in the list-based representation. -/
theorem ofList_minimal_step
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (ihLeft : ∃ t : GCNFProofTree (LCS.Finset.ofList (pre ++ A :: suf)), t.axiomsMinimal)
    (ihRight : ∃ t : GCNFProofTree (LCS.Finset.ofList (pre ++ Clause.single B :: suf)),
      t.axiomsMinimal) :
    ∃ t : GCNFProofTree (LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf)),
      t.axiomsMinimal := by
-- BEGIN PROOF
  let Gamma := LCS.Finset.ofList (pre ++ suf)
  have heqL : LCS.Finset.ofList (pre ++ A :: suf) = LCS.Finset.union Gamma (ClauseSequent.single A) :=
    ofList_replace_eq_union pre suf A
  have heqR : LCS.Finset.ofList (pre ++ Clause.single B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B)) :=
    ofList_replace_eq_union pre suf (Clause.single B)
  have heqC : LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) :=
    ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  rw [heqC]
  rw [heqL] at ihLeft
  rw [heqR] at ihRight
  exact gcnf_minimal_step Gamma A B ihLeft ihRight

helper /-- Core axiom-minimization lemma on literal-lists. -/
theorem gcnf_minimal_of_lit_lists :
    ∀ (ll : List (List Literal)),
    (∀ ls ∈ ll, ls ≠ []) →
    ClauseSequent.isValid (litListsToClauseSeq ll) →
    ∃ t : GCNFProofTree (litListsToClauseSeq ll), t.axiomsMinimal := by
-- BEGIN PROOF
  suffices hwf : ∀ (n : Nat) (ll : List (List Literal)),
      totalLitCount ll ≤ n →
      (∀ ls ∈ ll, ls ≠ []) →
      ClauseSequent.isValid (litListsToClauseSeq ll) →
      ∃ t : GCNFProofTree (litListsToClauseSeq ll), t.axiomsMinimal from
    fun ll hNe hValid => hwf (totalLitCount ll) ll (Nat.le_refl _) hNe hValid
  intro n
  induction n with
  | zero =>
    intro ll hBound hNe hValid
    have hEmpty : ll = [] := by
      cases ll with
      | nil => rfl
      | cons hd tl =>
        have hhdNe := hNe hd (List.mem_cons.mpr (Or.inl rfl))
        rw [totalLitCount_cons] at hBound
        have : hd.length ≥ 1 := by
          cases hd with
          | nil => exact absurd rfl hhdNe
          | cons _ _ => simp
        omega
    subst hEmpty
    exfalso; apply hValid
    exact ⟨fun _ => true, fun C hC => absurd ((LCS.Finset.mem_ofList_exp C []).mp hC) List.not_mem_nil⟩
  | succ n ih =>
    intro ll hBound hNe hValid
    by_cases hAllSingle : ∀ ls ∈ ll, ∃ L, ls = [L]
    · have hSingle : ∀ C ∈ litListsToClauseSeq ll, ∃ L : Literal, C = Clause.single L := by
        intro C hC
        change C ∈ LCS.Finset.ofList (List.map Clause.ofList ll) at hC
        rw [LCS.Finset.mem_ofList] at hC
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hC
        obtain ⟨L, rfl⟩ := hAllSingle ls hls
        exact ⟨L, ofList_singleton_eq L⟩
      exact all_singletons_exact_pair_proof (litListsToClauseSeq ll) hSingle hValid
    · have ⟨ls, hls_mem, hls_not_single⟩ : ∃ ls ∈ ll, ∀ L, ls ≠ [L] :=
        Classical.byContradiction fun hAll => hAllSingle fun ls hls =>
          Classical.byContradiction fun hNo =>
            hAll ⟨ls, hls, fun L hEq => hNo ⟨L, hEq⟩⟩
      have hls_ne := hNe ls hls_mem
      obtain ⟨L, rest, rfl⟩ : ∃ L rest, ls = L :: rest := by
        cases ls with
        | nil => exact absurd rfl hls_ne
        | cons hd tl => exact ⟨hd, tl, rfl⟩
      have hrest_ne : rest ≠ [] := by
        intro h; subst h; exact hls_not_single L rfl
      have mem_split : ∀ (xs : List (List Literal)) (x : List Literal),
          x ∈ xs → ∃ pre suf, xs = pre ++ x :: suf := by
        intro xs x hx
        induction xs with
        | nil => exact absurd hx List.not_mem_nil
        | cons hd tl ih_s =>
          rw [List.mem_cons] at hx
          rcases hx with rfl | htl
          · exact ⟨[], tl, by simp⟩
          · obtain ⟨pre', suf', heq'⟩ := ih_s htl
            exact ⟨hd :: pre', suf', by rw [heq', List.cons_append]⟩
      obtain ⟨pre, suf, hll_eq⟩ := mem_split ll (L :: rest) hls_mem
      have hclause_eq : Clause.ofList (L :: rest) = clauseWithLiteral (Clause.ofList rest) L :=
        (clauseWithLiteral_ofList_cons L rest).symm
      have hll_map2 : ll.map Clause.ofList =
          pre.map Clause.ofList ++ clauseWithLiteral (Clause.ofList rest) L :: suf.map Clause.ofList := by
        rw [hll_eq, List.map_append, List.map_cons, hclause_eq]
      have hseq_eq : litListsToClauseSeq ll =
          LCS.Finset.ofList (pre.map Clause.ofList ++ clauseWithLiteral (Clause.ofList rest) L :: suf.map Clause.ofList) := by
        show LCS.Finset.ofList (ll.map Clause.ofList) = _
        rw [hll_map2]
      rw [hseq_eq]; rw [hseq_eq] at hValid
      have hLeftValid : ClauseSequent.isValid
          (LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.ofList rest :: suf.map Clause.ofList)) :=
        ofList_left_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hRightValid : ClauseSequent.isValid
          (LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.single L :: suf.map Clause.ofList)) :=
        ofList_right_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hLeftEq : LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.ofList rest :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ rest :: suf) := by
        simp only [litListsToClauseSeq, List.map_append, List.map_cons]
      have hRightEq : LCS.Finset.ofList (pre.map Clause.ofList ++ Clause.single L :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ [L] :: suf) := by
        unfold litListsToClauseSeq
        simp only [List.map_append, List.map_cons]
        rw [ofList_singleton_eq]
      have hLeftSize : totalLitCount (pre ++ rest :: suf) < totalLitCount ll := by
        rw [hll_eq]
        exact totalLitCount_replace_lt pre (L :: rest) suf rest (by simp)
      have hRightSize : totalLitCount (pre ++ [L] :: suf) < totalLitCount ll := by
        rw [hll_eq]
        apply totalLitCount_replace_lt pre (L :: rest) suf [L]
        cases rest with
        | nil => exact absurd rfl hrest_ne
        | cons _ _ => simp
      have hNe' : ∀ ls ∈ pre ++ (L :: rest) :: suf, ls ≠ [] := hll_eq ▸ hNe
      have hLeftNe : ∀ ls ∈ pre ++ rest :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact hrest_ne
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have hRightNe : ∀ ls ∈ pre ++ [L] :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact List.cons_ne_nil L []
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have ihL := ih (pre ++ rest :: suf) (by omega) hLeftNe (hLeftEq ▸ hLeftValid)
      have ihR := ih (pre ++ [L] :: suf) (by omega) hRightNe (hRightEq ▸ hRightValid)
      rw [← hLeftEq] at ihL; rw [← hRightEq] at ihR
      exact ofList_minimal_step (pre.map Clause.ofList) (suf.map Clause.ofList)
        (Clause.ofList rest) L ihL ihR

helper /-- Helper: well-founded axiom-minimization on a list witness. -/
theorem gcnf_minimal_of_list (l : List Clause)
    (hNe : ∀ C ∈ l, C ≠ Clause.empty)
    (hValid : ClauseSequent.isValid (LCS.Finset.ofList l)) :
    ∃ t : GCNFProofTree (LCS.Finset.ofList l), t.axiomsMinimal := by
-- BEGIN PROOF
  let toLitList : Clause → List Literal := fun C => C.toList
  let ll := l.map toLitList
  have hMapEq : ll.map Clause.ofList = l := map_ofList_map_toList l
  have hSeqEq : litListsToClauseSeq ll = LCS.Finset.ofList l := by
    unfold litListsToClauseSeq; rw [hMapEq]
  have hllNe : ∀ ls ∈ ll, ls ≠ [] := by
    intro ls hls
    change ls ∈ List.map toLitList l at hls
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hls
    intro hempty
    have hempty' : C.toList = [] := hempty
    have hCne := hNe C hC
    apply hCne
    apply LCS.Finset.ext; intro a
    rw [show (Clause.empty : Clause) = LCS.Finset.empty from rfl]
    constructor
    · intro (ha : a ∈ C)
      have : a ∈ C.toList := (LCS.Finset.mem_toList C a).mpr ha
      rw [hempty'] at this
      exact absurd this List.not_mem_nil
    · intro ha
      exact absurd ha (LCS.Finset.not_mem_empty)
  have := gcnf_minimal_of_lit_lists ll hllNe (hSeqEq ▸ hValid)
  rwa [hSeqEq] at this

helper /-- The completeness of GCNF' with exact-pair axioms (Theorem 4.2.1 Part 2). -/
theorem gcnf_minimal_from_normal_form
    (S : ClauseSequent)
    (hValid : ClauseSequent.isValid S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    ∃ t : GCNFProofTree S, t.axiomsMinimal := by
-- BEGIN PROOF
  -- Extract a list representation via Classical.choose.
  have hSeq : S = LCS.Finset.ofList S.toList := by
    apply LCS.Finset.ext; intro C
    rw [LCS.Finset.mem_ofList, LCS.Finset.mem_toList]
  rw [hSeq]
  apply gcnf_minimal_of_list S.toList
  · intro C hC; exact hNe C ((LCS.Finset.mem_toList S C).mp hC)
  · rw [hSeq] at hValid; exact hValid

proof_of gcnf_completeness := by
  -- BEGIN PROOF
    constructor
    · -- Part 1: GCNFProvable S
      have hSeq : S = LCS.Finset.ofList S.toList := by
        apply LCS.Finset.ext; intro C
        rw [LCS.Finset.mem_ofList, LCS.Finset.mem_toList]
      rw [hSeq]
      obtain ⟨t, _⟩ := gcnf_provable_of_list S.toList
        (fun C hC => hNe C ((LCS.Finset.mem_toList S C).mp hC))
        (by rw [hSeq] at hValid; exact hValid)
      exact ⟨t⟩
    · -- Part 2: Nontrivial valid sequents have proofs with minimal axioms
      intro _
      exact gcnf_minimal_from_normal_form S hValid hNe

proof_of Clause.union_ordinary_left := by
  intro h
  apply hA
  apply LCS.Finset.ext
  intro L
  constructor
  · intro hL
    have hU := LCS.Finset.mem_union.mpr (Or.inl hL : L ∈ A ∨ L ∈ B)
    rw [h] at hU
    exact hU
  · intro hL; exact False.elim (LCS.Finset.not_mem_empty hL)


proof_of exProof_leaf_comparison := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    · simp [exGCNFProofTree, GCNFProofTree.leafCount, cast_eq]
    · simp only [exOrdinaryProofTree, OrdinaryClauseProof.orLeftOfList,
        OrdinaryClauseProof.leafCount_cast, OrdinaryClauseProof.leafCount]


proof_of exProof_node_comparison := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    · simp [exGCNFProofTree, GCNFProofTree.nodeCount, cast_eq]
    · simp only [exOrdinaryProofTree, OrdinaryClauseProof.orLeftOfList,
        OrdinaryClauseProof.nodeCount_cast, OrdinaryClauseProof.nodeCount]

end LCS.Resolution.GCNF
