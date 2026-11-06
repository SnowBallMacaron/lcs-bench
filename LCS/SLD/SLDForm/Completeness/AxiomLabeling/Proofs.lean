import LCS.SLD.SLDForm.Completeness.AxiomLabeling

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

helper /-- An exact selection description including the unit root clauses. -/
theorem axiomLeaves_selection {S : ClauseSequent} (T : GCNFProofTree S)
    (hWk : IsStrictIWW T) (hGen : GenuineDecompositions T)
    (hMin : T.axiomsAllSingleLiteral) :
    ∀ leaf, leaf ∈ axiomLeaves T →
      ∃ select : Clause → Literal,
        (∀ C ∈ S, select C ∈ C) ∧
        leaf = ClauseSequent.mapSet S (fun C => Clause.single (select C)) := by
  classical
  induction T with
  | axiom_ S hOrd hTriv =>
    intro leaf hLeaf
    have hEq : leaf = S := by simpa only [axiomLeaves, List.mem_singleton] using hLeaf
    subst leaf
    let select : Clause → Literal := fun C =>
      if h : C ∈ S then Classical.choose (hMin C h) else Literal.pos 0
    have hs : ∀ C ∈ S, C = Clause.single (select C) := by
      intro C hC
      simpa only [select, dite_eq_left hC] using Classical.choose_spec (hMin C hC)
    refine ⟨select, ?_, ?_⟩
    · intro C hC
      have hm : select C ∈ Clause.single (select C) := (Finset.mem_singleton _ _).mpr rfl
      exact (congrArg (fun D => select C ∈ D) (hs C hC)).mpr hm
    · apply Finset.ext; intro C
      constructor
      · intro hC
        exact (mem_image_iff _ _ _).mpr ⟨C, hC, (hs C hC).symm⟩
      · intro hC
        obtain ⟨D, hD, rfl⟩ := (mem_image_iff _ _ _).mp hC
        rw [← hs D hD]; exact hD
  | rule Gamma As B Cs Gamma1 Gamma2 hGammaOrd hAsOrd left right hNe hSub hG1 hG2 ihL ihR =>
    rcases hWk with ⟨hCs, hGamma1, hGamma2, hWL, hWR⟩
    subst Cs; subst Gamma1; subst Gamma2
    rcases hGen with ⟨hFresh, hDisj, hGL, hGR⟩
    intro leaf hLeaf
    rcases List.mem_append.mp hLeaf with hLeaf | hLeaf
    · obtain ⟨f, hf, heq⟩ := ihL hWL hGL hMin.1 leaf hLeaf
      let select : Clause → Literal := fun C => if C ∈ Gamma then f C else f (C.erase B)
      have hErase : ∀ A ∈ As, (clauseWithLiteral A B).erase B = A := by
        intro A hA
        apply Finset.ext; intro L
        rw [Finset.mem_erase, clauseWithLiteral, Finset.mem_insert_exp]
        constructor
        · rintro ⟨h | h, hne⟩
          · exact False.elim (hne h)
          · exact h
        · intro h
          exact ⟨Or.inr h, fun he => hFresh A hA (he ▸ h)⟩
      have hContext : ∀ C ∈ Gamma, select C = f C := by
        intro C hC; exact ite_eq_left hC
      have hPrincipal : ∀ A ∈ As, select (clauseWithLiteral A B) = f A := by
        intro A hA
        dsimp [select]
        rw [ite_eq_right (hDisj A hA), hErase A hA]
      refine ⟨select, ?_, ?_⟩
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · rw [hContext C hC]
          exact hf C (Finset.mem_union.mpr (Or.inl hC))
        · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hC
          rw [hPrincipal A hA]
          exact (Finset.mem_insert_exp _ _ _).mpr
            (Or.inr (hf A (Finset.mem_union.mpr (Or.inr hA))))
      · rw [heq]
        apply Finset.ext; intro D
        constructor
        · intro hD
          obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
          rcases Finset.mem_union.mp hC with hC | hC
          · exact (mem_image_iff _ _ _).mpr
              ⟨C, Finset.mem_union.mpr (Or.inl hC), congrArg Clause.single (hContext C hC)⟩
          · refine (mem_image_iff _ _ _).mpr
              ⟨clauseWithLiteral C B, Finset.mem_union.mpr (Or.inr ?_),
                congrArg Clause.single (hPrincipal C hC)⟩
            exact (mem_image_iff _ _ _).mpr ⟨C, hC, rfl⟩
        · intro hD
          obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
          rcases Finset.mem_union.mp hC with hC | hC
          · exact (mem_image_iff _ _ _).mpr
              ⟨C, Finset.mem_union.mpr (Or.inl hC), congrArg Clause.single (hContext C hC).symm⟩
          · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hC
            exact (mem_image_iff _ _ _).mpr
              ⟨A, Finset.mem_union.mpr (Or.inr hA), congrArg Clause.single (hPrincipal A hA).symm⟩
    · obtain ⟨f, hf, heq⟩ := ihR hWR hGR hMin.2 leaf hLeaf
      let select : Clause → Literal := fun C => if C ∈ Gamma then f C else B
      have hContext : ∀ C ∈ Gamma, select C = f C := by
        intro C hC; exact ite_eq_left hC
      have hPrincipal : ∀ A ∈ As, select (clauseWithLiteral A B) = B := by
        intro A hA; exact ite_eq_right (hDisj A hA)
      have hB : f (Clause.single B) = B :=
        (Finset.mem_singleton _ _).mp (hf _ (Finset.mem_union.mpr
          (Or.inr ((mem_csingle _ _).mpr rfl))))
      refine ⟨select, ?_, ?_⟩
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · rw [hContext C hC]
          exact hf C (Finset.mem_union.mpr (Or.inl hC))
        · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hC
          rw [hPrincipal A hA]
          exact (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
      · rw [heq]
        apply Finset.ext; intro D
        constructor
        · intro hD
          obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
          rcases Finset.mem_union.mp hC with hC | hC
          · exact (mem_image_iff _ _ _).mpr
              ⟨C, Finset.mem_union.mpr (Or.inl hC), congrArg Clause.single (hContext C hC)⟩
          · have hCeq := (mem_csingle _ _).mp hC
            subst C
            obtain ⟨A, hA⟩ := hNe
            refine (mem_image_iff _ _ _).mpr
              ⟨clauseWithLiteral A B, Finset.mem_union.mpr (Or.inr ?_), ?_⟩
            · exact (mem_image_iff _ _ _).mpr ⟨A, hA, rfl⟩
            · rw [hPrincipal A hA, hB]
        · intro hD
          obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
          rcases Finset.mem_union.mp hC with hC | hC
          · exact (mem_image_iff _ _ _).mpr
              ⟨C, Finset.mem_union.mpr (Or.inl hC), congrArg Clause.single (hContext C hC).symm⟩
          · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hC
            refine (mem_image_iff _ _ _).mpr
              ⟨Clause.single B, Finset.mem_union.mpr (Or.inr ((mem_csingle _ _).mpr rfl)), ?_⟩
            rw [hPrincipal A hA, hB]

proof_of axiom_labeling_structure := by
  dsimp only
  intro leaf hLeaf
  obtain ⟨f, hf, heq⟩ := axiomLeaves_selection T hWk hGen hMin leaf hLeaf
  have hUnit : ∀ C ∈ oneLiteralClauses S, Clause.single (f C) = C := by
    intro C hC
    obtain ⟨hCS, hCard⟩ := Finset.mem_filter.mp hC
    have hOne : C.card = 1 := of_decide_eq_true hCard
    apply Finset.ext; intro L
    change L ∈ Finset.singleton (f C) ↔ L ∈ C
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl; exact hf C hCS
    · intro hL; exact finset_card_one_eq hOne L (f C) hL (hf C hCS)
  refine ⟨f, fun C hC => hf C (Finset.mem_filter.mp hC).1, ?_⟩
  rw [heq]
  apply Finset.ext; intro D
  constructor
  · intro hD
    obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
    by_cases hm : 1 < C.card
    · exact Finset.mem_union.mpr (Or.inl ((mem_image_iff _ _ _).mpr
        ⟨C, Finset.mem_filter.mpr ⟨hC, decide_eq_true hm⟩, rfl⟩))
    · have hPos := finset_card_pos_of_mem (hf C hC)
      have hOne : C.card = 1 := by omega
      have hJ : C ∈ oneLiteralClauses S := Finset.mem_filter.mpr ⟨hC, decide_eq_true hOne⟩
      rw [hUnit C hJ]
      exact Finset.mem_union.mpr (Or.inr hJ)
  · intro hD
    rcases Finset.mem_union.mp hD with hD | hD
    · obtain ⟨C, hC, rfl⟩ := (mem_image_iff _ _ _).mp hD
      exact (mem_image_iff _ _ _).mpr ⟨C, (Finset.mem_filter.mp hC).1, rfl⟩
    · exact (mem_image_iff _ _ _).mpr ⟨D, (Finset.mem_filter.mp hD).1, hUnit D hD⟩

proof_of horn_provable_has_positive_and_goal := by
  -- BEGIN PROOF
    -- Proof: Since S is GCNF'-provable, by soundness it is valid (unsatisfiable).
    -- Part 1: S must contain a positive unit clause {pos P}.
    --   If S contained no positive unit clause, we could construct a satisfying
    --   valuation by setting all atoms to true, satisfying every clause that
    --   contains a positive literal. Since S consists of Horn clauses, each clause
    --   has at most one positive literal. Without a pure positive unit clause,
    --   the positive literal in each clause would make it satisfiable,
    --   contradicting validity.
    -- Part 2: S must contain a goal clause (all negative).
    --   If no clause were all-negative, every clause would contain a positive
    --   literal. Setting all atoms to true would satisfy every clause,
    --   contradicting validity.
    have hValid := gcnf_soundness S hProv
    constructor
    · -- Part 1: existence of a positive unit clause {pos P}.
      -- By induction on the proof tree using the Horn property:
      -- Axiom leaves have {pos P, neg P} in their sequent.
      -- At rule nodes, the positive unit propagates through the Horn structure.
      obtain ⟨T⟩ := hProv
      exact gcnf_tree_has_pos_unit T hHorn
    · -- Part 2: existence of a goal clause (all-negative clause).
      -- If no goal clause exists, every clause C in S contains a positive literal.
      -- Setting all atoms to true satisfies every such clause via its positive literal.
      suffices h : ¬(∃ goal, goal ∈ S ∧ isGoalClause goal) → False from
        Classical.byContradiction fun hNoGoal => h hNoGoal
      intro hNoGoal
      -- hNoGoal : ¬∃ goal, goal ∈ S ∧ isGoalClause goal
      -- So for all C ∈ S, ¬isGoalClause C.
      have hNotGoalAll : ∀ C ∈ S, ¬isGoalClause C := by
        intro C hC hGoalC
        exact hNoGoal ⟨C, hC, hGoalC⟩
      -- Every C ∈ S has a positive literal (since it's Horn but not a goal clause).
      -- Construct a satisfying valuation: set all atoms to true.
      -- This contradicts the validity of S.
      apply hValid
      refine ⟨fun _ => true, fun C hC => ?_⟩
      have hNotGoal := hNotGoalAll C hC
      have hHornC := hHorn C hC
      -- ¬isGoalClause with isHornClause means not all literals are negative
      have hNotAllNeg : ¬(∀ l ∈ C, match l with | Literal.neg _ => True | _ => False) := by
        intro h; exact hNotGoal ⟨hHornC, h⟩
      -- There exists a literal in C that is positive
      have hHasPos : ∃ P, Literal.pos P ∈ C := by
        suffices ¬(∃ P, Literal.pos P ∈ C) → False from
          Classical.byContradiction fun hNoPos => this hNoPos
        intro hNoPos
        exact hNotAllNeg (fun l hl => by
          cases l with
          | neg _ => trivial
          | pos P => exfalso; exact hNoPos ⟨P, hl⟩)
      obtain ⟨P, hP⟩ := hHasPos
      exact ⟨Literal.pos P, hP, rfl⟩

end LCS.SLD.SLDForm.Completeness
end
