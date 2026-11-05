import LCS.SLD.SLDForm.Completeness.RootPartition

section

namespace LCS.SLD.SLDForm.Completeness

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

open LCS.SLD.SLDForm.Occurrence

proof_of gcnf_proof_without_weakenings := by
  -- BEGIN PROOF
    obtain ⟨D, hLeaves⟩ :=
      gcnf_occurrence_proof_without_weakenings
        S hNe hProv
    exact
      ⟨D.compress hLeaves,
        isWithoutWeakenings_of_isUnaryOccurrenceCompression
          (D.compress hLeaves) (D.compress_isUnaryOccurrenceCompression hLeaves),
        D.compress_axiomsAllSingleLiteral hLeaves⟩


helper /-- Base case: when all clauses are single-literal, a single axiom node
    suffices. The axiom is vacuously StrictIWW and satisfies
    axiomsAllSingleLiteral by the singleton hypothesis. -/
theorem all_singletons_strict (S : ClauseSequent)
    (hSingle : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L)
    (hValid : ClauseSequent.isValid S) :
    ∃ t : GCNFProofTree S, IsStrictIWW t ∧ t.axiomsAllSingleLiteral :=
-- BEGIN PROOF
  ⟨.axiom_ S (ordinary_of_singletons hSingle) (singletons_valid_imp_trivial S hSingle hValid), trivial, hSingle⟩

helper /-- Inductive step: decompose clauseWithLiteral A B into A and {B},
    building a rule node with Gamma1 = Gamma2 = Gamma. -/
theorem ofList_strict_step
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (ihLeft : ∃ t : GCNFProofTree (Finset.ofList (pre ++ A :: suf)),
      IsStrictIWW t ∧ t.axiomsAllSingleLiteral)
    (ihRight : ∃ t : GCNFProofTree (Finset.ofList (pre ++ Clause.single B :: suf)),
      IsStrictIWW t ∧ t.axiomsAllSingleLiteral) :
    ∃ t : GCNFProofTree (Finset.ofList (pre ++ clauseWithLiteral A B :: suf)),
      IsStrictIWW t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  let Gamma := Finset.ofList (pre ++ suf)
  have heqL := ofList_replace_eq_union pre suf A
  have heqR := ofList_replace_eq_union pre suf (Clause.single B)
  have heqC := ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  rw [heqC]; rw [heqL] at ihLeft; rw [heqR] at ihRight
  obtain ⟨leftTree, hLIWW, hLeftSL⟩ := ihLeft
  obtain ⟨rightTree, hRIWW, hRightSL⟩ := ihRight
  have heq : Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply Finset.ext; intro C; constructor
    · intro hC; rw [Finset.mem_union] at hC ⊢; rcases hC with hG | hC
      · exact Or.inl hG
      · right; rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC; rw [Finset.mem_union] at hC ⊢; rcases hC with hG | hC
      · exact Or.inl hG
      · right; obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'; rw [mem_csingle]; exact hCA'.symm
  rw [heq]
  exact ⟨GCNFProofTree.rule Gamma (ClauseSequent.single A) B (ClauseSequent.single A)
    Gamma Gamma (ordinary_left leftTree) (ordinary_right leftTree) leftTree rightTree
    ⟨A, (Finset.mem_singleton A A).mpr rfl⟩ (fun C hC => hC)
    (fun _ h => (Finset.mem_union_exp _ Gamma _).mpr (Or.inl h))
    (fun _ h => (Finset.mem_union_exp _ Gamma _).mpr (Or.inl h)),
    ⟨rfl, rfl, rfl, hLIWW, hRIWW⟩, ⟨hLeftSL, hRightSL⟩⟩

helper /-- Main induction on literal lists: produces StrictIWW + allSingleLiteral. -/
theorem gcnf_strict_of_lit_lists :
    ∀ (ll : List (List Literal)),
    (∀ ls ∈ ll, ls ≠ []) →
    ClauseSequent.isValid (litListsToClauseSeq ll) →
    ∃ t : GCNFProofTree (litListsToClauseSeq ll), IsStrictIWW t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  suffices hwf : ∀ (n : Nat) (ll : List (List Literal)),
      totalLitCount ll ≤ n →
      (∀ ls ∈ ll, ls ≠ []) →
      ClauseSequent.isValid (litListsToClauseSeq ll) →
      ∃ t : GCNFProofTree (litListsToClauseSeq ll), IsStrictIWW t ∧ t.axiomsAllSingleLiteral from
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
          cases hd with | nil => exact absurd rfl hhdNe | cons _ _ => simp
        omega
    subst hEmpty
    exfalso; apply hValid
    exact ⟨fun _ => true, fun C hC => absurd ((Finset.mem_ofList_exp C []).mp hC) List.not_mem_nil⟩
  | succ n ih =>
    intro ll hBound hNe hValid
    by_cases hAllSingle : ∀ ls ∈ ll, ∃ L, ls = [L]
    · have hSingle : ∀ C ∈ litListsToClauseSeq ll, ∃ L : Literal, C = Clause.single L := by
        intro C hC
        change C ∈ Finset.ofList (List.map Clause.ofList ll) at hC
        rw [Finset.mem_ofList] at hC
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hC
        obtain ⟨L, rfl⟩ := hAllSingle ls hls
        exact ⟨L, ofList_singleton_eq L⟩
      exact all_singletons_strict (litListsToClauseSeq ll) hSingle hValid
    · have ⟨ls, hls_mem, hls_not_single⟩ : ∃ ls ∈ ll, ∀ L, ls ≠ [L] :=
        Classical.byContradiction fun hAll => hAllSingle fun ls hls =>
          Classical.byContradiction fun hNo => hAll ⟨ls, hls, fun L hEq => hNo ⟨L, hEq⟩⟩
      have hls_ne := hNe ls hls_mem
      obtain ⟨L, rest, rfl⟩ : ∃ L rest, ls = L :: rest := by
        cases ls with | nil => exact absurd rfl hls_ne | cons hd tl => exact ⟨hd, tl, rfl⟩
      have hrest_ne : rest ≠ [] := by intro h; subst h; exact hls_not_single L rfl
      have mem_split : ∀ (xs : List (List Literal)) (x : List Literal),
          x ∈ xs → ∃ pre suf, xs = pre ++ x :: suf := by
        intro xs x hx; induction xs with
        | nil => exact absurd hx List.not_mem_nil
        | cons hd tl ih_s =>
          rw [List.mem_cons] at hx; rcases hx with rfl | htl
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
          Finset.ofList (pre.map Clause.ofList ++ clauseWithLiteral (Clause.ofList rest) L :: suf.map Clause.ofList) := by
        show Finset.ofList (ll.map Clause.ofList) = _; rw [hll_map2]
      rw [hseq_eq]; rw [hseq_eq] at hValid
      have hLeftValid := ofList_left_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hRightValid := ofList_right_valid (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hLeftEq : Finset.ofList (pre.map Clause.ofList ++ Clause.ofList rest :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ rest :: suf) := by
        simp only [litListsToClauseSeq, List.map_append, List.map_cons]
      have hRightEq : Finset.ofList (pre.map Clause.ofList ++ Clause.single L :: suf.map Clause.ofList) =
          litListsToClauseSeq (pre ++ [L] :: suf) := by
        unfold litListsToClauseSeq; simp only [List.map_append, List.map_cons]; rw [ofList_singleton_eq]
      have hLeftSize : totalLitCount (pre ++ rest :: suf) < totalLitCount ll := by
        rw [hll_eq]; exact totalLitCount_replace_lt pre (L :: rest) suf rest (by simp)
      have hRightSize : totalLitCount (pre ++ [L] :: suf) < totalLitCount ll := by
        rw [hll_eq]; apply totalLitCount_replace_lt pre (L :: rest) suf [L]
        cases rest with | nil => exact absurd rfl hrest_ne | cons _ _ => simp
      have hNe' : ∀ ls ∈ pre ++ (L :: rest) :: suf, ls ≠ [] := hll_eq ▸ hNe
      have hLeftNe : ∀ ls ∈ pre ++ rest :: suf, ls ≠ [] := by
        intro ls' hls'; rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact hrest_ne
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have hRightNe : ∀ ls ∈ pre ++ [L] :: suf, ls ≠ [] := by
        intro ls' hls'; rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact hNe' ls' (List.mem_append.mpr (Or.inl hPre))
        · exact List.cons_ne_nil L []
        · exact hNe' ls' (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hSuf))))
      have ihL := ih (pre ++ rest :: suf) (by omega) hLeftNe (hLeftEq ▸ hLeftValid)
      have ihR := ih (pre ++ [L] :: suf) (by omega) hRightNe (hRightEq ▸ hRightValid)
      rw [← hLeftEq] at ihL; rw [← hRightEq] at ihR
      exact ofList_strict_step (pre.map Clause.ofList) (suf.map Clause.ofList)
        (Clause.ofList rest) L ihL ihR

helper /-- Lift from literal lists to clause lists. -/
theorem gcnf_strict_of_list (l : List Clause)
    (hNe : ∀ C ∈ l, C ≠ Clause.empty)
    (hValid : ClauseSequent.isValid (Finset.ofList l)) :
    ∃ t : GCNFProofTree (Finset.ofList l), IsStrictIWW t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  let ll := l.map clauseToLitList
  have hMapEq : ll.map Clause.ofList = l := map_ofList_map_toList l
  have hSeqEq : litListsToClauseSeq ll = Finset.ofList l := by
    unfold litListsToClauseSeq; rw [hMapEq]
  have hllNe : ∀ ls ∈ ll, ls ≠ [] := by
    intro ls hls; obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hls
    intro hempty; apply hNe C hC; apply Finset.ext; intro a
    constructor
    · intro (ha : a ∈ C)
      have haTL : a ∈ clauseToLitList C := (Finset.mem_toList C a).mpr ha
      have hNoMem : clauseToLitList C = [] := hempty
      rw [hNoMem] at haTL; exact absurd haTL List.not_mem_nil
    · intro ha; exact ((Finset.mem_empty a).mp ha).elim
  have := gcnf_strict_of_lit_lists ll hllNe (hSeqEq ▸ hValid)
  rwa [hSeqEq] at this

helper /-- Lift from clause lists to arbitrary ClauseSequent. -/
theorem gcnf_strict_from_normal_form (S : ClauseSequent)
    (hValid : ClauseSequent.isValid S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    ∃ t : GCNFProofTree S, IsStrictIWW t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  have hSeq : S = Finset.ofList S.toList := (finset_ofList_toList_eq S).symm
  rw [hSeq]
  refine gcnf_strict_of_list S.toList ?_ (hSeq ▸ hValid)
  intro C hC
  exact hNe C ((Finset.mem_toList S C).mp hC)

helper /-- Compatibility wrapper for the former strict-IWW construction. Both
    predicate names now denote the same exact no-weakening condition. -/
theorem gcnf_proof_strict_iww (S : ClauseSequent) (hProv : GCNFProvable S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    ∃ T : GCNFProofTree S, IsStrictIWW T ∧ T.axiomsAllSingleLiteral :=
-- BEGIN PROOF
  gcnf_strict_from_normal_form S (gcnf_soundness S hProv) hNe

proof_of rootPlan_selectedPair_permutation := by
  refine ⟨⟨plan.permutationCertificate⟩, ?_, ?_, ?_, ?_, hGen, hGen'⟩
  · subst T
    exact isWithoutWeakenings_of_isUnaryOccurrenceCompression _
      (Occurrence.compress_isUnaryOccurrenceCompression source hMin)
  · subst T'
    exact isWithoutWeakenings_of_isUnaryOccurrenceCompression _
      (Occurrence.compress_isUnaryOccurrenceCompression _ _)
  · subst T
    exact Occurrence.compress_axiomsAllSingleLiteral _ _
  · subst T'
    exact Occurrence.compress_axiomsAllSingleLiteral _ _


proof_of gcnf_permutation_at_root := by
  -- DEBT(OD-9-2: root/partition contribution of Lemma 9.2.2 kept open; not emended)
  sorry


helper /-- Consequently, the proposed exact-expanded-depth conclusion fails for the
    concrete proof satisfying all of Lemma 9.2.2's hypotheses. -/
theorem expandedDepthAlias_no_exact_depth_root_partition :
    ¬ ∃ T' : GCNFProofTree expandedDepthAliasSequent,
      RootPartitionCertificate T' expandedDepthAliasTarget
        expandedDepthAliasA expandedDepthAliasB ∧
      expandedDepth T' = expandedDepth expandedDepthAliasTree := by
  rintro ⟨T', hCertificate, hDepth⟩
  apply expandedDepthAlias_no_root_partition_at_depth_two
  exact
    ⟨T', hCertificate,
      hDepth.trans expandedDepthAliasTree_expandedDepth⟩

helper /-- If clauseWithLiteral A B has card 1 and A has an element, then A = {B}. -/
theorem cwl_card_one_implies_singleton (A : Clause) (B : Literal)
    (hCard : (clauseWithLiteral A B).card = 1) (L : Literal) (hL : L ∈ A) :
    A = Clause.single B := by
-- BEGIN PROOF
  have hBin : B ∈ clauseWithLiteral A B := (Finset.mem_insert_exp B B A).mpr (Or.inl rfl)
  have hLin : L ∈ clauseWithLiteral A B := (Finset.mem_insert_exp B L A).mpr (Or.inr hL)
  have hLeqB : L = B := finset_card_one_eq hCard L B hLin hBin
  rw [hLeqB] at hL
  have hInsEq : clauseWithLiteral A B = A := by
    apply Finset.ext; intro x; show x ∈ Finset.insert B A ↔ x ∈ A
    rw [Finset.mem_insert]; exact ⟨fun h => h.elim (· ▸ hL) id, Or.inr⟩
  rw [hInsEq] at hCard
  apply Finset.ext; intro x; constructor
  · intro hx; show x ∈ Finset.singleton B; rw [Finset.mem_singleton]
    exact finset_card_one_eq hCard x B hx hL
  · intro hx; rw [(Finset.mem_singleton x B).mp hx]; exact hL



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
