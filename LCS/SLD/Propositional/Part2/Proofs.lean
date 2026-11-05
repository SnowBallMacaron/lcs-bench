import LCS.SLD.Propositional.Part2

section

namespace LCS.SLD.Propositional

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

helper /-- Adding negative literals to an all-negative clause preserves the all-negative property. -/
theorem augmentClause_allNeg (c : Clause) (extra : List Literal)
    (hc : ∀ l ∈ c, match l with | Literal.neg _ => True | _ => False)
    (hextra : ∀ l ∈ extra, match l with | Literal.neg _ => True | _ => False) :
    ∀ l ∈ augmentClause c extra,
      match l with | Literal.neg _ => True | _ => False := by
-- BEGIN PROOF
  intro l hl
  unfold augmentClause Clause.union at hl
  rw [Finset.mem_union] at hl
  rcases hl with hc' | he
  · exact hc l hc'
  · unfold Clause.ofList at he; exact hextra l ((Finset.mem_ofList_exp l extra).mp he)

helper /-- The head of modifiedSubsequence is the augmented head of the input. -/
theorem modifiedSubsequence_head' (seq : List Clause) (extra : List Literal)
    (h : seq.length ≥ 2) :
    (modifiedSubsequence seq extra).head (modifiedSubsequence_nonempty_of_ge_two seq extra h)
    = augmentClause (seq.head (by intro heq; rw [heq] at h; simp at h)) extra := by
-- BEGIN PROOF
  match seq, h with
  | _ :: _ :: _, _ => simp [modifiedSubsequence]

helper /-- The head of any linearized proof tree consists only of negative literals. -/
theorem linearize_head_allNeg' : {S : ClauseSequent} → (T : GCNFProofTree S) →
    ∀ l ∈ (linearize T).head (linearize_nonempty T),
      match l with | Literal.neg _ => True | _ => False
  | _, .axiom_ _ _hOrd _ => by
    simp [linearize, List.head]; intro l hl
    unfold Clause.single at hl
    have := (Finset.mem_singleton _ _).mp hl; subst this; trivial
  | _, .rule Gamma As B _ _ _ _hGammaOrd _hAsOrd leftTree rightTree _ _ _ _ => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simp only [linearize, dif_pos hAx, List.head_cons]
      intro l hl
      have heq := (Finset.mem_singleton _ _).mp hl
      subst l
      trivial
    cases B with
    | pos _ =>
      simp only [linearize, dif_neg hAx, List.head_cons]; intro l hl
      unfold Clause.single at hl
      have := (Finset.mem_singleton _ _).mp hl; subst this; trivial
    | neg Q =>
      simp only [linearize, dif_neg hAx]
      have hlen := linearize_length_ge_two leftTree
      have hne := modifiedSubsequence_nonempty_of_ge_two
        (linearize leftTree) [Literal.neg Q] hlen
      intro l hl
      rw [List.head_append_of_ne_nil hne] at hl
      rw [modifiedSubsequence_head' _ _ hlen] at hl
      exact augmentClause_allNeg _ [Literal.neg Q] (linearize_head_allNeg' leftTree)
        (fun l' hl' => by simp at hl'; subst hl'; trivial) l hl

helper /-- Compute the head of linearize (matching linearize's recursion). -/
noncomputable def linearizeHead : {S : ClauseSequent} → GCNFProofTree S → Clause
  | _, .axiom_ _S _hOrd hTriv => Clause.single (Literal.neg (Classical.choose hTriv))
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree _rightTree _ _ _ _ =>
    letI : Decidable (ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) := Classical.propDecidable _
    if hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) then
      Clause.single (Literal.neg (Classical.choose hAx))
    else
      match B with
      | Literal.pos P => Clause.single (Literal.neg P)
      | Literal.neg Q => augmentClause (linearizeHead leftTree) [Literal.neg Q]

helper /-- The head of linearize equals linearizeHead. -/
theorem linearize_head_eq : {S : ClauseSequent} → (T : GCNFProofTree S) →
    (linearize T).head (linearize_nonempty T) = linearizeHead T
  | _, .axiom_ _S _hOrd _hTriv => by simp [linearize, linearizeHead]
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _ _ _ _ => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simp [linearize, linearizeHead, hAx]
    cases B with
    | pos _P =>
      simp [linearize, dif_neg hAx, linearizeHead]
    | neg Q =>
      simp only [linearize, dif_neg hAx, linearizeHead]
      have hlen := linearize_length_ge_two leftTree
      have hne := modifiedSubsequence_nonempty_of_ge_two (linearize leftTree) [Literal.neg Q] hlen
      rw [List.head_append_of_ne_nil hne, modifiedSubsequence_head' _ _ hlen]
      congr 1
      exact linearize_head_eq leftTree

helper /-- Length of modifiedSubsequence is one less than the input. -/
theorem modifiedSubsequence_length (seq : List Clause) (extra : List Literal)
    (h : seq.length ≥ 2) :
    (modifiedSubsequence seq extra).length = seq.length - 1 := by
-- BEGIN PROOF
  induction seq with
  | nil => simp at h
  | cons a rest ih =>
    cases rest with
    | nil => simp at h
    | cons b rest' =>
      simp only [modifiedSubsequence, List.length_cons]
      by_cases hrest : (b :: rest').length ≥ 2
      · have := ih hrest; simp [List.length_cons] at this ⊢; omega
      · have h1 : rest' = [] := by simp [List.length_cons] at hrest; omega
        subst h1; simp [modifiedSubsequence]

helper /-- Indexing into modifiedSubsequence gives the augmented original element. -/
theorem modifiedSubsequence_get (seq : List Clause) (extra : List Literal)
    (hlen : seq.length ≥ 2) (i : Nat) (hi : i < (modifiedSubsequence seq extra).length) :
    (modifiedSubsequence seq extra).get ⟨i, hi⟩ =
      augmentClause (seq.get ⟨i, by
        have := modifiedSubsequence_length seq extra hlen; omega⟩) extra := by
-- BEGIN PROOF
  induction seq generalizing i with
  | nil => simp at hlen
  | cons a rest ih =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [modifiedSubsequence] at hi ⊢
      cases i with
      | zero => simp [List.get]
      | succ n =>
        simp only [List.get]
        by_cases hrest : (b :: rest').length ≥ 2
        · exact ih hrest n (by simp [List.length_cons] at hi; exact hi)
        · have h1 : rest' = [] := by simp [List.length_cons] at hrest; omega
          subst h1; simp [modifiedSubsequence] at hi

helper /-- resolveStep commutes with augmentClause when the removed literal is not
    among the extra literals (the extra literals pass through unchanged). -/
theorem resolveStep_augmentClause (Ni : Clause) (A : Nat) (C : Clause)
    (extraLits : List Literal)
    (h : Literal.neg A ∉ Clause.ofList extraLits) :
    resolveStep (augmentClause Ni extraLits) A C =
      augmentClause (resolveStep Ni A C) extraLits := by
-- BEGIN PROOF
  unfold resolveStep augmentClause Clause.union Clause.remove
  apply Finset.ext; intro l
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro (⟨hNiOrExtra, hne⟩ | ⟨hC, hF⟩)
    · rcases hNiOrExtra with hNi | hExtra
      · exact Or.inl (Or.inl ⟨hNi, hne⟩)
      · exact Or.inr hExtra
    · exact Or.inl (Or.inr ⟨hC, hF⟩)
  · rintro (hResolve | hExtra)
    · rcases hResolve with ⟨hNi, hne⟩ | ⟨hC, hF⟩
      · exact Or.inl ⟨Or.inl hNi, hne⟩
      · exact Or.inr ⟨hC, hF⟩
    · exact Or.inl ⟨Or.inr hExtra, fun heq => h (heq ▸ hExtra)⟩

helper /-- selectedAtomMatches is preserved by augmentClause (the extra negative
    literals don't affect the selected atom or the definite clause). -/
theorem selectedAtomMatches_augment (Ni : Clause) (A : Nat) (C : Clause)
    (extraLits : List Literal)
    (h : selectedAtomMatches Ni A C) :
    selectedAtomMatches (augmentClause Ni extraLits) A C := by
-- BEGIN PROOF
  unfold selectedAtomMatches at *
  unfold augmentClause Clause.union
  exact ⟨(Finset.mem_union_exp _ _ _).mpr (Or.inl h.1), h.2⟩

helper /-- Resolving a singleton {neg Q} against {pos Q} ∪ head (all-negative)
    yields head. Used for the transition step in goal splitting. -/
theorem resolveStep_singleton_neg_target (Q : Nat) (head : Clause)
    (hhead : ∀ l ∈ head, match l with | Literal.neg _ => True | _ => False) :
    resolveStep (Clause.single (Literal.neg Q)) Q
      (Finset.insert (Literal.pos Q) head) = head := by
  unfold resolveStep Clause.single Clause.remove Clause.union
  apply Finset.ext; intro l
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro (⟨heq, hne⟩ | ⟨hins, hf⟩)
    · exact absurd heq hne
    · rcases hins with rfl | hmem
      · simp at hf
      · exact hmem
  · intro hmem; right
    exact ⟨Or.inr hmem,
      by have := hhead l hmem; cases l with | neg _ => rfl | pos _ => simp at this⟩

helper /-- augmentClause of empty with [neg Q] gives the singleton {neg Q}. -/
theorem augmentClause_empty_singleton (Q : Nat) :
    augmentClause Clause.empty [Literal.neg Q] = Clause.single (Literal.neg Q) := by
-- BEGIN PROOF
  unfold augmentClause Clause.union Clause.empty Clause.single Clause.ofList
  apply Finset.ext; intro l
  constructor
  · intro h
    rw [Finset.mem_union] at h
    rcases h with hE | hL
    · exact ((Finset.mem_empty _).mp hE).elim
    · rw [Finset.mem_ofList] at hL
      rcases List.mem_cons.mp hL with rfl | h
      · exact (Finset.mem_singleton _ _).mpr rfl
      · exact absurd h List.not_mem_nil
  · intro h
    rw [Finset.mem_union]; right
    have : l = Literal.neg Q := (Finset.mem_singleton _ _).mp h
    rw [Finset.mem_ofList, this]; exact List.mem_cons_self

helper theorem goalSplit_implies_linHead (Q : Nat) :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isSLDForm_goalSplit Q T → linearizeHead T = Clause.single (Literal.neg Q)
  | _, .axiom_ _ _ hTriv, h =>
    h.2.1 _ (Classical.choose_spec hTriv).2 (isGoalClause_single_neg _)
  | _, .rule Gamma As B Cs G1 G2 hG hAs left right hNe hSub hG1 hG2, h => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simpa only [linearizeHead, dif_pos hAx] using
        h.2.1 _ (Classical.choose_spec hAx).2 (isGoalClause_single_neg _)
    · have hLocal := h.2.2.resolve_left hAx
      obtain ⟨hB, _⟩ := hLocal
      cases B with
      | neg P => contradiction
      | pos P =>
        have hPQ := Literal.pos.inj hB
        subst P
        simp [linearizeHead, hAx]

helper noncomputable def sldGoalHead : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _hOrd _ => True
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _hNe _hSub _ _ =>
    sldGoalHead leftTree ∧ sldGoalHead rightTree ∧
    (ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) ∨
      match B with
      | Literal.neg Q => linearizeHead rightTree = Clause.single (Literal.neg Q)
      | _ => True)

helper theorem isSLDForm_implies_sldGoalHead :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    LCS.SLD.SLDForm.isSLDForm T → sldGoalHead T
  | _, .axiom_ _ _hOrd _, _ => trivial
  | _, .rule _ _ B _ _ _ _hGammaOrd _hAsOrd leftTree rightTree _ _ _ _, h => by
    obtain ⟨hL, hR, hB⟩ := h
    refine ⟨isSLDForm_implies_sldGoalHead leftTree hL,
            isSLDForm_implies_sldGoalHead rightTree hR, ?_⟩
    rcases hB with hAx | hB
    · exact Or.inl hAx
    apply Or.inr
    match B with
    | Literal.pos _ => trivial
    | Literal.neg Q => exact goalSplit_implies_linHead Q rightTree hB.1

helper /-- resolveStep distributes over augmentClause when the definite clause
    is also augmented with the same extra negative literal. This avoids
    the A = Q issue that arises with resolveStep_augmentClause. -/
theorem resolveStep_augment_both (Ni : Clause) (A : Nat) (C : Clause) (Q : Nat) :
    resolveStep (augmentClause Ni [Literal.neg Q]) A (Finset.insert (Literal.neg Q) C) =
    augmentClause (resolveStep Ni A C) [Literal.neg Q] := by
-- BEGIN PROOF
  unfold resolveStep augmentClause Clause.union Clause.remove
  apply Finset.ext; intro l
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, Finset.mem_insert]
  unfold Clause.ofList
  simp only [Finset.mem_ofList, List.mem_singleton]
  constructor
  · rintro (⟨hMem, hne⟩ | ⟨hIns, hf⟩)
    · rcases hMem with hNi | rfl
      · left; left; exact ⟨hNi, hne⟩
      · right; rfl
    · rcases hIns with rfl | hC
      · right; rfl
      · left; right; exact ⟨hC, hf⟩
  · rintro ((⟨hNi, hne⟩ | ⟨hFilter, hf⟩) | rfl)
    · left; exact ⟨Or.inl hNi, hne⟩
    · right; exact ⟨Or.inr hFilter, hf⟩
    · by_cases hAQ : A = Q
      · subst hAQ; right; exact ⟨Or.inl rfl, rfl⟩
      · left; exact ⟨Or.inr rfl, fun h => hAQ (Literal.neg.inj h.symm)⟩

helper /-- Inserting a negative literal into a definite clause preserves definiteness. -/
theorem isDefiniteClause_insert_neg (C : Clause) (Q : Nat)
    (h : isDefiniteClause C) :
    isDefiniteClause (Finset.insert (Literal.neg Q) C) := by
-- BEGIN PROOF
  obtain ⟨hHorn, P, hP⟩ := h
  constructor
  · refine ⟨Clause.ordinary_of_mem (Finset.mem_insert.mpr (Or.inl rfl)), ?_⟩
    intro R S' hR hS'
    rw [Finset.mem_insert] at hR hS'
    rcases hR with hR | hR <;> rcases hS' with hS' | hS'
    · exact Literal.noConfusion hR
    · exact Literal.noConfusion hR
    · exact Literal.noConfusion hS'
    · exact hHorn.2 R S' hR hS'
  · exact ⟨P, (Finset.mem_insert_exp _ _ _).mpr (Or.inr hP)⟩

helper /-- selectedAtomMatches is preserved by augmenting the clause and inserting
    a negative literal into the definite clause. -/
theorem selectedAtomMatches_augment_insert_neg (Ni : Clause) (A : Nat)
    (C : Clause) (Q : Nat) (extra : List Literal)
    (h : selectedAtomMatches Ni A C) :
    selectedAtomMatches (augmentClause Ni extra) A (Finset.insert (Literal.neg Q) C) := by
-- BEGIN PROOF
  unfold selectedAtomMatches at *
  unfold augmentClause Clause.union
  exact ⟨(Finset.mem_union_exp _ _ _).mpr (Or.inl h.1),
         (Finset.mem_insert_exp _ _ _).mpr (Or.inr h.2)⟩

helper /-- Structural invariant: for any SLD-form GCNF'-proof T on sequent S, the head clause
    of the linearization lives in S and is a goal clause. Proved by induction on T.
    Does not require uniqueness of the goal clause — used as a building block where
    the proof tree's internal structure determines the head. -/
theorem linearizeHead_mem_and_goalClause :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    LCS.SLD.SLDForm.isSLDForm T →
    linearizeHead T ∈ S ∧ LCS.SLD.SLDForm.isGoalClause (linearizeHead T)
  | _, .axiom_ _ _hOrd hTriv, _ => by
    simp only [linearizeHead]
    refine ⟨(Classical.choose_spec hTriv).2, ?_⟩
    exact isGoalClause_single_neg (Classical.choose hTriv)
  | _, .rule Gamma As B Cs Gamma1 _ _hGammaOrd _hAsOrd leftTree _rightTree _hNe hCsSub _hG1Sub _hG2Sub, hSLD => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simpa only [linearizeHead, dif_pos hAx] using
        And.intro (Classical.choose_spec hAx).2 (isGoalClause_single_neg (Classical.choose hAx))
    obtain ⟨hSLDL, _hSLDR, hB⟩ := hSLD
    have hB := hB.resolve_left hAx
    cases B with
    | pos P =>
      obtain ⟨_hCsNeg, _hAxiom, hNegInGamma, _hDrop, _hWit⟩ := hB
      simp only [linearizeHead, dif_neg hAx]
      refine ⟨?_, isGoalClause_single_neg P⟩
      exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hNegInGamma)
    | neg Q =>
      obtain ⟨_hGoalSplit, _hCsAllNeg, ⟨G, hGCs, hGGoal, _hGNoNegQ, hGUnique⟩⟩ := hB
      simp only [linearizeHead, dif_neg hAx]
      obtain ⟨hLHmem, hLHgc⟩ := linearizeHead_mem_and_goalClause leftTree hSLDL
      have hLHeqG : linearizeHead leftTree = G := hGUnique _ hLHmem hLHgc
      rw [hLHeqG]
      refine ⟨?_, ?_⟩
      · have hGinAs : G ∈ As := hCsSub G hGCs
        have heqCwl : clauseWithLiteral G (Literal.neg Q) =
            augmentClause G [Literal.neg Q] := by
          unfold clauseWithLiteral augmentClause Clause.union Clause.ofList
          apply Finset.ext; intro l
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_ofList,
            List.mem_cons, List.not_mem_nil, or_false]
          exact Or.comm
        refine (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)
        rw [← heqCwl]
        exact (mem_image_iff _ _ _).mpr ⟨G, hGinAs, rfl⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨Clause.ordinary_of_mem (show Literal.neg Q ∈ augmentClause G [Literal.neg Q] by
            simp [augmentClause, Clause.union, Clause.ofList]), ?_⟩
          intro P1 P2 hP1 _
          unfold augmentClause Clause.union Clause.ofList at hP1
          simp only [Finset.mem_union, Finset.mem_ofList,
            List.mem_cons, List.not_mem_nil, or_false] at hP1
          rcases hP1 with hG' | hExtra
          · have := hGGoal.2 (Literal.pos P1) hG'; simp at this
          · exact absurd hExtra Literal.noConfusion
        · intro l hl
          unfold augmentClause Clause.union Clause.ofList at hl
          simp only [Finset.mem_union, Finset.mem_ofList,
            List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with hG' | hExtra
          · exact hGGoal.2 l hG'
          · subst hExtra; trivial

helper /-- Helper: if every element of a sequence `seq` avoids `Literal.neg Q`, and also
    `Q' ≠ Q`, then every element of `modifiedSubsequence seq [Literal.neg Q']` avoids
    `Literal.neg Q`. -/
theorem modifiedSubsequence_no_neg_lit (Q Q' : Nat) (hQne : Q ≠ Q') :
    ∀ (seq : List Clause),
    (∀ N ∈ seq, Literal.neg Q ∉ N) →
    ∀ M ∈ modifiedSubsequence seq [Literal.neg Q'], Literal.neg Q ∉ M
  | [], _ => by intro M hM; simp [modifiedSubsequence] at hM
  | [_], _ => by intro M hM; simp [modifiedSubsequence] at hM
  | c :: c' :: rest, h => by
    intro M hM
    simp only [modifiedSubsequence, List.mem_cons] at hM
    rcases hM with rfl | hMtail
    · -- M = augmentClause c [neg Q']
      intro hNegQinM
      unfold augmentClause Clause.union Clause.ofList at hNegQinM
      rw [Finset.mem_union_exp] at hNegQinM
      rcases hNegQinM with hInC | hInExtra
      · exact h c (List.Mem.head _) hInC
      · rw [Finset.mem_ofList] at hInExtra
        rcases List.mem_cons.mp hInExtra with heq | hNil
        · apply hQne
          cases heq; rfl
        · exact (List.not_mem_nil hNil).elim
    · -- M ∈ modifiedSubsequence (c' :: rest) [neg Q']
      exact modifiedSubsequence_no_neg_lit Q Q' hQne (c' :: rest)
        (fun M' hM' => h M' (List.Mem.tail _ hM')) M hMtail

helper /-- Structural invariant: if every clause in an SLD-form tree's sequent avoids
    `Literal.neg Q`, then every clause produced by `linearize` also avoids it.
    Used to ensure that the resolution steps in the left region of a goal-split
    linearization don't select the split atom `Q`, allowing unaugmented definite
    clauses to be used in the SLDDerivation. -/
theorem linearize_no_neg_lit (Q : Nat) : {S : ClauseSequent} → (T : GCNFProofTree S) →
    LCS.SLD.SLDForm.isSLDForm T →
    (∀ C ∈ S, Literal.neg Q ∉ C) →
    ∀ N ∈ linearize T, Literal.neg Q ∉ N
  | S, T, hSLD, hNoQS => by
    induction T with
    | axiom_ S' _hOrd hTriv =>
      clear hSLD
      intro N hN hNegQinN
      simp only [linearize, List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl
      · have hNegPwitInS : Clause.single (Literal.neg (Classical.choose hTriv)) ∈ S' :=
          (Classical.choose_spec hTriv).2
        have hEq := (Finset.mem_singleton _ _).mp hNegQinN
        have hQeq : Q = Classical.choose hTriv := by cases hEq; rfl
        apply hNoQS _ hNegPwitInS
        rw [hQeq]
        exact (Finset.mem_singleton _ _).mpr rfl
      · exact ((Finset.mem_empty _).mp hNegQinN).elim
    | rule Gamma As B Cs Gamma1 Gamma2 _hGammaOrd _hAsOrd leftTree rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
      classical
      by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
      · intro N hN hNegQinN
        simp only [linearize, dif_pos hAx, List.mem_cons, List.not_mem_nil, or_false] at hN
        rcases hN with rfl | rfl
        · have hEq := (Finset.mem_singleton _ _).mp hNegQinN
          have hQeq : Q = Classical.choose hAx := Literal.neg.inj hEq
          exact hNoQS _ (Classical.choose_spec hAx).2
            (hQeq ▸ (Finset.mem_singleton _ _).mpr rfl)
        · exact Finset.not_mem_empty hNegQinN
      obtain ⟨hSLDL, hSLDR, hB⟩ := hSLD
      have hB := hB.resolve_left hAx
      have hNoQ_L : ∀ C ∈ LCS.Finset.union Gamma1 Cs, Literal.neg Q ∉ C := by
        intro C hC
        rw [Finset.mem_union] at hC
        rcases hC with hG1 | hCs
        · exact hNoQS _ (hG1Sub C hG1)
        · have hCinAs : C ∈ As := hCsSub C hCs
          have hCwlinS : clauseWithLiteral C B ∈ LCS.Finset.union Gamma
              (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
            (Finset.mem_union_exp _ _ _).mpr (Or.inr
              ((mem_image_iff _ _ _).mpr ⟨C, hCinAs, rfl⟩))
          intro hNegQinC
          apply hNoQS _ hCwlinS
          unfold clauseWithLiteral
          exact (Finset.mem_insert_exp _ _ _).mpr (Or.inr hNegQinC)
      cases B with
      | pos P =>
        simp only [linearize, dif_neg hAx]
        intro N hN hNegQinN
        simp only [List.mem_cons] at hN
        rcases hN with rfl | hN
        · have hEq := (Finset.mem_singleton _ _).mp hNegQinN
          have hQeq : Q = P := by cases hEq; rfl
          obtain ⟨_, _, hNegPinGamma, _⟩ := hB
          have hNegPinS : Clause.single (Literal.neg P) ∈ LCS.Finset.union Gamma
              (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos P))) :=
            (Finset.mem_union_exp _ _ _).mpr (Or.inl hNegPinGamma)
          exact hNoQS _ hNegPinS (by rw [hQeq]; exact (Finset.mem_singleton _ _).mpr rfl)
        · exact ihL hSLDL hNoQ_L N hN hNegQinN
      | neg Q' =>
        have hQne : Q ≠ Q' := by
          obtain ⟨A, hA⟩ := hCsNe
          have hAinAs : A ∈ As := hCsSub A hA
          have hCwlinS : clauseWithLiteral A (Literal.neg Q') ∈ LCS.Finset.union Gamma
              (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.neg Q'))) :=
            (Finset.mem_union_exp _ _ _).mpr (Or.inr
              ((mem_image_iff _ _ _).mpr ⟨A, hAinAs, rfl⟩))
          intro hEq
          apply hNoQS _ hCwlinS
          unfold clauseWithLiteral
          rw [hEq]
          exact (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
        have hNoQ_R : ∀ C ∈ LCS.Finset.union Gamma2
            (ClauseSequent.single (Clause.single (Literal.neg Q'))), Literal.neg Q ∉ C := by
          intro C hC
          rw [Finset.mem_union] at hC
          rcases hC with hG2 | hSing
          · exact hNoQS _ (hG2Sub C hG2)
          · have hCeq : C = Clause.single (Literal.neg Q') :=
              (Finset.mem_singleton _ _).mp hSing
            intro hNegQinC
            rw [hCeq] at hNegQinC
            have : Literal.neg Q = Literal.neg Q' :=
              (Finset.mem_singleton _ _).mp hNegQinC
            exact hQne (by cases this; rfl)
        have hLinLeft := ihL hSLDL hNoQ_L
        have hLinRight := ihR hSLDR hNoQ_R
        have hModLeft := modifiedSubsequence_no_neg_lit Q Q' hQne (linearize leftTree) hLinLeft
        simp only [linearize, dif_neg hAx]
        intro N hN
        rw [List.mem_append] at hN
        rcases hN with hL | hR
        · exact hModLeft N hL
        · exact hLinRight N hR

helper /-- The original-input provenance requirement for the linearization
    specification. SQ18 leaves this claim false on unrestricted inputs. -/
def linearize_definiteClauses_in_S
    (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hSLD : LCS.SLD.SLDForm.isSLDForm T)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (goal : Clause)
    (hGoal : goal ∈ S)
    (hGoalPred : LCS.SLD.SLDForm.isGoalClause goal)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C → C = goal) : Prop :=
    ∃ d : SLDDerivation,
      (∀ C ∈ d.definiteClauses, LCS.SLD.SLDForm.isDefiniteClause C) ∧
      goal ∈ d.goals ∧
      d.sequence = linearize T ∧
      isSLDRefutation d ∧
      (∀ C ∈ d.definiteClauses, C ∈ S)

helper /-- The head of the linearized sequence of an SLD-form proof tree over a sequent
    with a unique goal equals that goal. This follows because the SLD-form tree's
    root structure (with the Phase A3-fix strengthening of `isSLDForm`) ensures
    the linearization starts from the unique goal clause at every node. -/
theorem linearize_head_eq_goal
    (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hSLD : LCS.SLD.SLDForm.isSLDForm T)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (goal : Clause)
    (hGoal : goal ∈ S)
    (hGoalPred : LCS.SLD.SLDForm.isGoalClause goal)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C → C = goal) :
    (linearize T).head (linearize_nonempty T) = goal := by
  rw [linearize_head_eq]
  obtain ⟨hMem, hGoal⟩ := linearizeHead_mem_and_goalClause T hSLD
  exact hUnique _ hMem hGoal

helper /-- Helper: For an SLD-form tree T on S whose unique goal is `{neg P}` (singleton
    negative), the head of linearize T equals `{neg P}`, so the first selected
    atom of any selectedAtomMatches predicate must be P.

    Auxiliary fact: in any SLD-form tree T whose unique goal is `{neg P}`, the
    structural recursion on T (using `linearize_head_eq_goal`) ensures that
    `(linearize T).head = {neg P}`. -/
theorem first_atom_singleton_goal
    (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hSLD : LCS.SLD.SLDForm.isSLDForm T)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (P : Nat)
    (hP : Clause.single (Literal.neg P) ∈ S)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C →
        C = Clause.single (Literal.neg P)) :
    (linearize T).head (linearize_nonempty T) = Clause.single (Literal.neg P) := by
-- BEGIN PROOF
  exact linearize_head_eq_goal S T hSLD hDef
    (Clause.single (Literal.neg P)) hP (isGoalClause_single_neg' P) hUnique

helper /-- Helper: An SLD-form tree on a sequent whose unique goal is `{neg P}` has
    a definite clause containing `pos P` in its sequent. This follows from the
    structure of SLD-form proofs: the first step resolves `{neg P}` against
    some definite clause containing `pos P`.

    The witness is provided by `sld_form_completeness`'s case `B'.card = 1`,
    which produces a tree whose root rule has `B = pos P` against a definite
    clause `C` with `pos P ∈ C` and `C ∈ S`. -/
theorem singleton_goal_pos_witness
    (S : ClauseSequent)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (P : Nat)
    (hP : Clause.single (Literal.neg P) ∈ S)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C →
        C = Clause.single (Literal.neg P))
    (hProv : GCNFProvable S) :
    ∃ C ∈ S, Literal.pos P ∈ C := by
-- BEGIN PROOF
  -- By soundness, S is unsatisfiable. Setting v(P) = false satisfies {neg P}.
  -- For S to be unsatisfiable, some clause must contain pos P.
  have hValid := gcnf_soundness S hProv
  -- Suppose ∀ C ∈ S, pos P ∉ C. Construct v(n) = if n = P then false else true.
  -- This v satisfies all C ∈ S: {neg P} via neg P. Other clauses are definite,
  -- and their positive literal pos R has R ≠ P (since pos P ∉ C), so v(R) = true.
  apply Classical.byContradiction
  intro hNoPos
  have hNoPos' : ∀ C ∈ S, Literal.pos P ∉ C := by
    intro C hC hPosInC
    exact hNoPos ⟨C, hC, hPosInC⟩
  apply hValid
  refine ⟨fun n => if n = P then false else true, fun C hC => ?_⟩
  -- Case on C = {neg P} vs C ≠ {neg P}.
  by_cases hCgoal : C = Clause.single (Literal.neg P)
  · subst hCgoal
    refine ⟨Literal.neg P, (LCS.Finset.mem_singleton _ _).mpr rfl, ?_⟩
    show (if P = P then false else true) = false
    simp
  · -- C ≠ {neg P}; by hUnique, C is not a goal clause.
    have hNotGoal : ¬LCS.SLD.SLDForm.isGoalClause C :=
      fun hGC => hCgoal (hUnique C hC hGC)
    -- By hDef, C is definite.
    have hDefC : LCS.SLD.SLDForm.isDefiniteClause C := by
      rcases hDef C hC with hd | hg
      · exact hd
      · exact absurd hg hNotGoal
    -- C has a positive literal pos R, R ≠ P (since pos P ∉ C).
    obtain ⟨_, R, hR⟩ := hDefC
    have hRneP : R ≠ P := fun heq => hNoPos' C hC (heq ▸ hR)
    refine ⟨Literal.pos R, hR, ?_⟩
    show (if R = P then false else true) = true
    simp [hRneP]

helper /-- Generalized witness for definite-clause pos-atom: under GCNFProvable S
    with definite/goal structure and unique goal clause, any negative literal
    `neg P` in the unique goal has a witness clause `C ∈ S` with `pos P ∈ C`.

    Textbook reasoning: by soundness, S is unsatisfiable. If no clause in S
    contained `pos P`, then setting v(P) = false would satisfy both:
    - The goal (containing `neg P`, satisfied since v(P) = false)
    - All other (definite) clauses (their positive literals have R ≠ P, so
      v(R) = true)
    contradicting validity. -/
theorem goal_atom_pos_witness
    (S : ClauseSequent)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (goal : Clause)
    (hGoal : goal ∈ S)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C → C = goal)
    (P : Nat)
    (hP : Literal.neg P ∈ goal)
    (hProv : GCNFProvable S) :
    ∃ C ∈ S, Literal.pos P ∈ C := by
-- BEGIN PROOF
  have hValid := gcnf_soundness S hProv
  apply Classical.byContradiction
  intro hNoPos
  have hNoPos' : ∀ C ∈ S, Literal.pos P ∉ C := by
    intro C hC hPosInC
    exact hNoPos ⟨C, hC, hPosInC⟩
  apply hValid
  refine ⟨fun n => if n = P then false else true, fun C hC => ?_⟩
  -- Case on C is a goal clause vs definite clause.
  rcases hDef C hC with hDefC | hGoalC
  · -- Definite C: has a positive literal pos R, R ≠ P (else hNoPos' violated).
    obtain ⟨_, R, hR⟩ := hDefC
    have hRneP : R ≠ P := fun heq => hNoPos' C hC (heq ▸ hR)
    refine ⟨Literal.pos R, hR, ?_⟩
    show (if R = P then false else true) = true
    simp [hRneP]
  · -- Goal clause C = goal (by uniqueness). neg P ∈ C, satisfied since v(P) = false.
    have hCEq : C = goal := hUnique C hC hGoalC
    refine ⟨Literal.neg P, hCEq ▸ hP, ?_⟩
    show (if P = P then false else true) = false
    simp

proof_of sld_resolution_completeness := by
  -- REPAIR(T9-10): proof pending
  sorry

end LCS.SLD.Propositional

end
