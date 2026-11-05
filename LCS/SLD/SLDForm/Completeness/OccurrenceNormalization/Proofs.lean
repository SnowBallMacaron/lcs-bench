import LCS.SLD.SLDForm.Completeness.OccurrenceNormalization

section

namespace LCS.SLD.SLDForm.Completeness

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

open LCS.SLD.SLDForm.Occurrence















helper /-- Alias of `totalLits_insert` under the classic "of_not_mem" naming. -/
theorem totalLits_insert_of_not_mem (S : ClauseSequent) (C : Clause) (hC : C ∉ S) :
    totalLits (Finset.insert C S) = totalLits S + C.card :=
-- BEGIN PROOF
  totalLits_insert S C hC



helper /-- Delta lemma (subtraction form). Using `Nat.sub`, `totalLits (S.erase C)`
    equals `totalLits S - C.card` when `C ∈ S`. -/
theorem totalLits_erase (S : ClauseSequent) (C : Clause) (hC : C ∈ S) :
    totalLits (S.erase C) = totalLits S - C.card := by
-- BEGIN PROOF
  have h := totalLits_erase_add S C hC
  omega













helper
theorem IsStrictIWW_implies_IWW : {S : ClauseSequent} → (T : GCNFProofTree S) →
    IsStrictIWW T → IsWithoutWeakenings T :=
  fun _ h => h



helper /-- Occurrence-level refinement of a finite-set GCNF' proof.  Each rule chooses
    duplicate-free enumerations of its context and principal family, but the
    two lists are concatenated without deduplication in the left premise.
    Consequently, a clause selected as principal while already in `Gamma`
    retains two distinct occurrences instead of being silently contracted by
    `Finset.union`. -/
def occurrenceFaithfulIWW :
    {S : ClauseSequent} →
    (T : GCNFProofTree S) → List Clause → Prop
  | _, .axiom_ S hOrd _, occurrences =>
      ClauseSequent.ofList occurrences = S
  | _, .rule Gamma As pivot Cs Gamma1 Gamma2 hGammaOrd hAsOrd left right _ _ _ _,
      occurrences =>
      ClauseSequent.ofList occurrences =
          Finset.union Gamma
            (ClauseSequent.mapSet As
              (fun A => clauseWithLiteral A pivot)) ∧
      ∃ gammaOccurrences asOccurrences : List Clause,
        gammaOccurrences.Nodup ∧
        asOccurrences.Nodup ∧
        ClauseSequent.ofList gammaOccurrences = Gamma ∧
        ClauseSequent.ofList asOccurrences = As ∧
        Cs = As ∧
        Gamma1 = Gamma ∧
        Gamma2 = Gamma ∧
        occurrences.Perm
          (gammaOccurrences ++
            asOccurrences.map
              (fun A => clauseWithLiteral A pivot)) ∧
        occurrenceFaithfulIWW left
          (gammaOccurrences ++ asOccurrences) ∧
        occurrenceFaithfulIWW right
          (gammaOccurrences ++ [Clause.single pivot])

helper /-- A canonical occurrence refinement starts with one occurrence for each
    clause in the finite-set root.  Internal left premises may still contain
    duplicates arising from distinct context/principal roles. -/
def OccurrenceProvenance {S : ClauseSequent}
    (T : GCNFProofTree S) : Prop :=
  ∃ rootOccurrences : List Clause,
    rootOccurrences.Nodup ∧
    occurrenceFaithfulIWW T rootOccurrences

helper /-- Occurrence-faithful proofs satisfy the existing extensional definition of
    "without weakenings"; the converse fails because finite sets erase role
    multiplicity. -/
theorem occurrenceFaithfulIWW_implies_withoutWeakenings :
    {S : ClauseSequent} →
    (T : GCNFProofTree S) → (occurrences : List Clause) →
    occurrenceFaithfulIWW T occurrences →
      IsWithoutWeakenings T
  | _, .axiom_ _ hOrd _, _, _ => trivial
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd left right _ _ _ _, _, h => by
      rcases h.2 with
        ⟨gammaOccurrences, asOccurrences, _hGammaNodup, _hAsNodup,
          _hGamma, _hAs, hCs, hGamma1, hGamma2, _hPerm,
          hLeft, hRight⟩
      exact
        ⟨hCs, hGamma1, hGamma2,
          occurrenceFaithfulIWW_implies_withoutWeakenings
            left (gammaOccurrences ++ asOccurrences) hLeft,
          occurrenceFaithfulIWW_implies_withoutWeakenings
            right (gammaOccurrences ++ [Clause.single _]) hRight⟩

helper /-- Reindexing does not change whether a proof is weakening-free. -/
@[simp]
theorem isWithoutWeakenings_transport {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) :
    IsWithoutWeakenings (transportGCNFProofTree h T) ↔
      IsWithoutWeakenings T := by
  subst S'
  rfl

helper /-- Reindexing does not change the axiom leaves. -/
@[simp]
theorem axiomsAllSingleLiteral_transport_iff {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) :
    (transportGCNFProofTree h T).axiomsAllSingleLiteral ↔
      T.axiomsAllSingleLiteral := by
  subst S'
  rfl

helper /-- Reindexing does not change expanded depth. -/
@[simp]
theorem expandedDepth_transport {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) :
    expandedDepth (transportGCNFProofTree h T) =
      expandedDepth T := by
  subst S'
  rfl

helper /-- The occurrence-aliasing tree satisfies the theorem's weakening-free
    premise under the current finite-set representation. -/
theorem expandedDepthAliasTree_withoutWeakenings :
    IsWithoutWeakenings expandedDepthAliasTree := by
  have hInner : IsWithoutWeakenings expandedDepthAliasInner := by
    exact ⟨rfl, rfl, rfl, trivial, trivial⟩
  unfold expandedDepthAliasTree
  rw [isWithoutWeakenings_transport]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact (isWithoutWeakenings_transport _ _).2 hInner
  · exact (isWithoutWeakenings_transport _ _).2 hInner

helper /-- Every leaf in the occurrence-aliasing tree consists only of singleton
    literal clauses, as required by Lemma 9.2.2. -/
theorem expandedDepthAliasTree_axiomsAllSingleLiteral :
    expandedDepthAliasTree.axiomsAllSingleLiteral := by
  simp only [expandedDepthAliasTree, expandedDepthAliasInner,
    expandedDepthAliasLeftAxiom, expandedDepthAliasRightAxiom,
    axiomsAllSingleLiteral_transport_iff,
    GCNFProofTree.axiomsAllSingleLiteral, and_self]
  constructor
  · intro C hC
    have hC' :
        C ∈ ClauseSequent.ofList
              [Clause.single (Literal.pos 1),
                Clause.single (Literal.pos 0)] ∨
          C ∈ ClauseSequent.single (Clause.single (Literal.neg 0)) :=
      (Finset.mem_union_exp _ _ _).mp hC
    rcases hC' with hC | hC
    · have hList :
          C ∈ [Clause.single (Literal.pos 1),
            Clause.single (Literal.pos 0)] :=
        (Finset.mem_ofList_exp _ _).mp hC
      rcases List.mem_cons.mp hList with rfl | hList
      · exact ⟨Literal.pos 1, rfl⟩
      · have hEq := List.mem_singleton.mp hList
        subst C
        exact ⟨Literal.pos 0, rfl⟩
    · have hEq :=
        (Finset.mem_singleton _ _).mp hC
      subst C
      exact ⟨Literal.neg 0, rfl⟩
  · intro C hC
    have hC' :
        C ∈ ClauseSequent.ofList
              [Clause.single (Literal.pos 1),
                Clause.single (Literal.pos 0)] ∨
          C ∈ ClauseSequent.single (Clause.single (Literal.neg 1)) :=
      (Finset.mem_union_exp _ _ _).mp hC
    rcases hC' with hC | hC
    · have hList :
          C ∈ [Clause.single (Literal.pos 1),
            Clause.single (Literal.pos 0)] :=
        (Finset.mem_ofList_exp _ _).mp hC
      rcases List.mem_cons.mp hList with rfl | hList
      · exact ⟨Literal.pos 1, rfl⟩
      · have hEq := List.mem_singleton.mp hList
        subst C
        exact ⟨Literal.pos 0, rfl⟩
    · have hEq :=
        (Finset.mem_singleton _ _).mp hC
      subst C
      exact ⟨Literal.neg 1, rfl⟩

helper
theorem all_singletons_combined (S : ClauseSequent)
    (hSingle : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L)
    (hValid : ClauseSequent.isValid S) :
    ∃ t : GCNFProofTree S, IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  exact ⟨.axiom_ S (ordinary_of_singletons hSingle) (singletons_valid_imp_trivial S hSingle hValid), trivial, hSingle⟩

helper
theorem ofList_combined_step
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (ihLeft : ∃ t : GCNFProofTree (Finset.ofList (pre ++ A :: suf)),
      IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral)
    (ihRight : ∃ t : GCNFProofTree (Finset.ofList (pre ++ Clause.single B :: suf)),
      IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral) :
    ∃ t : GCNFProofTree (Finset.ofList (pre ++ clauseWithLiteral A B :: suf)),
      IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  let Gamma := Finset.ofList (pre ++ suf)
  have heqL : Finset.ofList (pre ++ A :: suf) = Finset.union Gamma (ClauseSequent.single A) :=
    ofList_replace_eq_union pre suf A
  have heqR : Finset.ofList (pre ++ Clause.single B :: suf) =
      Finset.union Gamma (ClauseSequent.single (Clause.single B)) :=
    ofList_replace_eq_union pre suf (Clause.single B)
  have heqC : Finset.ofList (pre ++ clauseWithLiteral A B :: suf) =
      Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) :=
    ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  rw [heqC]; rw [heqL] at ihLeft; rw [heqR] at ihRight
  obtain ⟨leftTree, hLIWW, hLeftLiterals⟩ := ihLeft
  obtain ⟨rightTree, hRIWW, hRightLiterals⟩ := ihRight
  have heq : Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply Finset.ext; intro C; constructor
    · intro hC; rw [Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right; rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC; rw [Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right; obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'; rw [mem_csingle]; exact hCA'.symm
  rw [heq]
  exact ⟨GCNFProofTree.rule Gamma (ClauseSequent.single A) B (ClauseSequent.single A)
    Gamma Gamma (ordinary_left leftTree) (ordinary_right leftTree) leftTree rightTree
    ⟨A, (Finset.mem_singleton A A).mpr rfl⟩ (fun C hC => hC)
    (fun _ h => (Finset.mem_union_exp _ Gamma _).mpr (Or.inl h))
    (fun _ h => (Finset.mem_union_exp _ Gamma _).mpr (Or.inl h)),
    ⟨rfl, rfl, rfl, hLIWW, hRIWW⟩,
    And.intro hLeftLiterals hRightLiterals⟩







helper
theorem gcnf_combined_of_lit_lists :
    ∀ (ll : List (List Literal)),
    (∀ ls ∈ ll, ls ≠ []) →
    ClauseSequent.isValid (litListsToClauseSeq ll) →
    ∃ t : GCNFProofTree (litListsToClauseSeq ll),
      IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  suffices hwf : ∀ (n : Nat) (ll : List (List Literal)),
      totalLitCount ll ≤ n →
      (∀ ls ∈ ll, ls ≠ []) →
      ClauseSequent.isValid (litListsToClauseSeq ll) →
      ∃ t : GCNFProofTree (litListsToClauseSeq ll),
        IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral from
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
      exact all_singletons_combined (litListsToClauseSeq ll) hSingle hValid
    · have ⟨ls, hls_mem, hls_not_single⟩ : ∃ ls ∈ ll, ∀ L, ls ≠ [L] :=
        Classical.byContradiction fun hAll => hAllSingle fun ls hls =>
          Classical.byContradiction fun hNo =>
            hAll ⟨ls, hls, fun L hEq => hNo ⟨L, hEq⟩⟩
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
      exact ofList_combined_step (pre.map Clause.ofList) (suf.map Clause.ofList)
        (Clause.ofList rest) L ihL ihR









helper
theorem gcnf_combined_of_list (l : List Clause)
    (hNe : ∀ C ∈ l, C ≠ Clause.empty)
    (hValid : ClauseSequent.isValid (Finset.ofList l)) :
    ∃ t : GCNFProofTree (Finset.ofList l),
      IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  let ll := l.map clauseToLitList
  have hMapEq : ll.map Clause.ofList = l := map_ofList_map_toList l
  have hSeqEq : litListsToClauseSeq ll = Finset.ofList l := by
    unfold litListsToClauseSeq; rw [hMapEq]
  have hllNe : ∀ ls ∈ ll, ls ≠ [] := by
    intro ls hls
    show ls ≠ []
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hls
    intro hempty
    apply hNe C hC; apply Finset.ext; intro a
    constructor
    · intro (ha : a ∈ C)
      have haTL : a ∈ clauseToLitList C := (Finset.mem_toList C a).mpr ha
      have hNoMem : clauseToLitList C = [] := hempty
      rw [hNoMem] at haTL; exact absurd haTL List.not_mem_nil
    · intro ha; exact ((Finset.mem_empty a).mp ha).elim
  have := gcnf_combined_of_lit_lists ll hllNe (hSeqEq ▸ hValid)
  rwa [hSeqEq] at this





helper
theorem gcnf_combined_from_normal_form (S : ClauseSequent)
    (hValid : ClauseSequent.isValid S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    ∃ t : GCNFProofTree S, IsWithoutWeakenings t ∧ t.axiomsAllSingleLiteral := by
-- BEGIN PROOF
  have hSeq : S = Finset.ofList S.toList := (finset_ofList_toList_eq S).symm
  rw [hSeq]
  refine gcnf_combined_of_list S.toList ?_ (hSeq ▸ hValid)
  intro C hC
  exact hNe C ((Finset.mem_toList S C).mp hC)





helper /-- Admissible weakening for GCNF': if T proves S, then S ∪ D is provable
    for any extra clauses D. -/
theorem gcnf_admissible_weakening {S : ClauseSequent} (T : GCNFProofTree S)
    (D : ClauseSequent) (hD : D.isOrdinary) : GCNFProvable (Finset.union S D) :=
  ⟨T.weaken D hD⟩

helper /-- Weakening to an ordinary superset. -/
theorem gcnf_provable_superset (S S' : ClauseSequent)
    (hSub : ∀ C, C ∈ S → C ∈ S')
    (hProv : GCNFProvable S) (hOrd : S'.isOrdinary) : GCNFProvable S' := by
  obtain ⟨T⟩ := hProv
  have hEq : Finset.union S S' = S' := by
    apply Finset.ext
    intro C
    simp only [Finset.mem_union]
    exact ⟨fun h => h.elim (hSub C) id, Or.inr⟩
  exact ⟨hEq ▸ T.weaken S' hOrd⟩

helper /-- Any GCNFProvable sequent has at least one non-empty clause. -/
theorem gcnf_provable_has_nonempty_clause (S : ClauseSequent) (h : GCNFProvable S) :
    ∃ C ∈ S, C ≠ Clause.empty := by
-- BEGIN PROOF
  obtain ⟨T⟩ := h
  match T with
  | .axiom_ S hOrd ⟨P, hPos, _⟩ =>
    refine ⟨Clause.single (Literal.pos P), hPos, ?_⟩
    intro heq; have : Literal.pos P ∈ Clause.empty := heq ▸ (Finset.mem_singleton _ _).mpr rfl
    exact (Finset.mem_empty _).mp this
  | .rule Gamma As B Cs _ _ hGammaOrd hAsOrd _ _ ⟨C0, hC0⟩ hCsSub _ _ =>
    let cwlC0 := clauseWithLiteral C0 B
    have hCwlMem : cwlC0 ∈ Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
      (Finset.mem_union_exp _ Gamma _).mpr (Or.inr ((mem_image_iff _ _ _).mpr ⟨C0, hCsSub C0 hC0, rfl⟩))
    refine ⟨cwlC0, hCwlMem, ?_⟩
    intro heq
    have hBmem : B ∈ cwlC0 := (Finset.mem_insert_exp B B C0).mpr (Or.inl rfl)
    exact (Finset.mem_empty _).mp (heq ▸ hBmem)





helper /-- Erasing empty from G ∪ mapSet equals (G.erase ∅) ∪ mapSet. -/
theorem erase_empty_union_mapSet (G As : ClauseSequent) (B : Literal) :
    Finset.erase (Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) Clause.empty =
    Finset.union (Finset.erase G Clause.empty) (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) := by
-- BEGIN PROOF
  apply Finset.ext; intro x
  rw [Finset.mem_erase, Finset.mem_union, Finset.mem_union, Finset.mem_erase]
  constructor
  · intro ⟨hMem, hNe⟩
    rcases hMem with hG | hM
    · exact Or.inl ⟨hG, hNe⟩
    · exact Or.inr hM
  · intro h
    rcases h with ⟨hG, hNe⟩ | hM
    · exact ⟨Or.inl hG, hNe⟩
    · constructor
      · exact Or.inr hM
      · intro heq
        obtain ⟨A, _, hfA⟩ := (mem_image_iff _ _ _).mp hM
        have : clauseWithLiteral A B = Clause.empty := by rw [hfA]; exact heq
        exact cwl_ne_empty A B this

helper /-- Erased union subset helper. -/
theorem erase_sub_union_left (G1 Cs : ClauseSequent) :
    ∀ C, C ∈ Finset.erase (Finset.union G1 Cs) Clause.empty →
         C ∈ Finset.union (Finset.erase G1 Clause.empty) Cs := by
-- BEGIN PROOF
  intro C hC; have ⟨hMem, hNe⟩ := (Finset.mem_erase _ _ _).mp hC
  rw [Finset.mem_union] at hMem ⊢
  rcases hMem with h1 | h2
  · exact Or.inl ((Finset.mem_erase _ _ _).mpr ⟨h1, hNe⟩)
  · exact Or.inr h2



helper /-- cwl(C, L) = C when L ∈ C (idempotent insertion). -/
theorem cwl_mem_eq (C : Clause) (L : Literal) (hL : L ∈ C) :
    clauseWithLiteral C L = C := by
-- BEGIN PROOF
  apply Finset.ext; intro x
  show x ∈ Finset.insert L C ↔ x ∈ C
  rw [Finset.mem_insert]; constructor
  · intro h; rcases h with rfl | hx; exact hL; exact hx
  · exact Or.inr



end LCS.SLD.SLDForm.Completeness

end
