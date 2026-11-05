import LCS.SLD.SLDForm.Completeness.GoalReduction

section

namespace LCS.SLD.SLDForm.Completeness

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

open LCS.SLD.SLDForm.Occurrence

helper /-- Lemma 9.2.2 (companion): Semantic validity of the left premise of ∨:left.
    If `S` is valid, then `(S.erase (clauseWithLiteral B'' Q)) ∪ {B''}` is
    valid. Membership of `clauseWithLiteral B'' Q` in `S` is not required for
    this semantic step (the conclusion follows from validity of `S` and the
    fact that any valuation satisfying the left premise also satisfies `S`). -/
theorem gcnf_valid_split_left (S : ClauseSequent) (B'' : Clause) (Q : Literal)
    (hValid : ClauseSequent.isValid S) :
    ClauseSequent.isValid
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B'')) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  apply hValid
  refine ⟨v, fun C hC => ?_⟩
  by_cases hCeq : C = clauseWithLiteral B'' Q
  · -- C is the split clause; use satisfaction of B'' to witness neg Q ∉ or insertion.
    subst hCeq
    have hB''sat : Clause.satisfiedBy B'' v :=
      hSat B'' ((Finset.mem_union_exp _ _ _).mpr
        (Or.inr ((mem_csingle B'' B'').mpr rfl)))
    obtain ⟨L, hLmem, hLsat⟩ := hB''sat
    -- L ∈ B'' ⊆ insert Q B'' = clauseWithLiteral B'' Q
    refine ⟨L, ?_, hLsat⟩
    show L ∈ Finset.insert Q B''
    exact (Finset.mem_insert_exp Q L B'').mpr (Or.inr hLmem)
  · -- C is in the erase, i.e., C ∈ S with C ≠ clauseWithLiteral B'' Q.
    have hCerase : C ∈ Finset.erase S (clauseWithLiteral B'' Q) :=
      (Finset.mem_erase _ _ _).mpr ⟨hC, hCeq⟩
    exact hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hCerase))

helper /-- Lemma 9.2.2 (companion): Semantic validity of the right premise of ∨:left.
    If `S` is valid, then `(S.erase (clauseWithLiteral B'' Q)) ∪ {{Q}}` is
    valid. Membership of `clauseWithLiteral B'' Q` in `S` is not required for
    this semantic step (the conclusion follows from validity of `S` and the
    fact that any valuation satisfying the right premise also satisfies `S`). -/
theorem gcnf_valid_split_right (S : ClauseSequent) (B'' : Clause) (Q : Literal)
    (hValid : ClauseSequent.isValid S) :
    ClauseSequent.isValid
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q))) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  apply hValid
  refine ⟨v, fun C hC => ?_⟩
  by_cases hCeq : C = clauseWithLiteral B'' Q
  · -- C is the split clause; use satisfaction of {Q} to witness Q ∈ insert Q B''.
    subst hCeq
    have hQClause : Clause.single Q ∈
        Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
          (ClauseSequent.single (Clause.single Q)) :=
      (Finset.mem_union_exp _ _ _).mpr
        (Or.inr ((mem_csingle (Clause.single Q) (Clause.single Q)).mpr rfl))
    have hQsat : Clause.satisfiedBy (Clause.single Q) v := hSat _ hQClause
    obtain ⟨L, hLmem, hLsat⟩ := hQsat
    have hLeqQ : L = Q := (Finset.mem_singleton L Q).mp hLmem
    -- L ∈ insert Q B'' = clauseWithLiteral B'' Q (via L = Q)
    refine ⟨L, ?_, hLsat⟩
    show L ∈ Finset.insert Q B''
    exact (Finset.mem_insert_exp Q L B'').mpr (Or.inl hLeqQ)
  · -- C is in the erase, i.e., C ∈ S with C ≠ clauseWithLiteral B'' Q.
    have hCerase : C ∈ Finset.erase S (clauseWithLiteral B'' Q) :=
      (Finset.mem_erase _ _ _).mpr ⟨hC, hCeq⟩
    exact hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hCerase))

proof_of gcnf_provable_clause_split := by
  -- BEGIN PROOF
    have hValid : ClauseSequent.isValid S := gcnf_soundness S hProv
    -- Left sub-sequent: validity + non-emptiness → provability
    have hValidL := gcnf_valid_split_left S B'' Q hValid
    have hValidR := gcnf_valid_split_right S B'' Q hValid
    -- Non-emptiness of clauses in left sub-sequent
    have hNeL : ∀ C ∈ Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B''), C ≠ Clause.empty := by
      intro C hC
      rw [Finset.mem_union] at hC
      rcases hC with hGamma | hSing
      · exact hGammaNe C hGamma
      · rw [(mem_csingle C B'').mp hSing]; exact hB''ne
    -- Non-emptiness of clauses in right sub-sequent
    have hNeR : ∀ C ∈ Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q)), C ≠ Clause.empty := by
      intro C hC
      rw [Finset.mem_union] at hC
      rcases hC with hGamma | hSing
      · exact hGammaNe C hGamma
      · rw [(mem_csingle C (Clause.single Q)).mp hSing]; exact single_ne_empty Q
    refine ⟨?_, ?_⟩
    · exact (gcnf_completeness _ hValidL hNeL).1
    · exact (gcnf_completeness _ hValidR hNeR).1


helper /-- Helper (Thm 9.2.1 goal-split support): no SLD-form proof exists for a sequent
    whose every clause is either empty or carries a positive literal. This rules
    out degenerate inner goal-splits whose left premise would otherwise carry an
    empty-clause witness G = ∅ ∈ Cs atop a context of definite clauses. The three
    structural cases (axiom, ∨:left at pos P, ∨:left at neg Q) each force a
    clause with no positive literal and no emptiness into the root sequent,
    contradicting the hypothesis. -/
theorem isSLDForm_empty_or_pos_impossible :
    {S : ClauseSequent} → (T : GCNFProofTree S) → isSLDForm T →
    (∀ C ∈ S, C = Clause.empty ∨ ∃ P : Nat, Literal.pos P ∈ C) → False
  | _, .axiom_ _ hOrd hTriv, _, hAll => by
-- BEGIN PROOF
    obtain ⟨P, _hPos, hNeg⟩ := hTriv
    rcases hAll _ hNeg with hEmpty | ⟨R, hR⟩
    · exact single_ne_empty _ hEmpty
    · exact Literal.noConfusion ((Finset.mem_singleton _ _).mp hR)
  | _, .rule Gamma As B _ _ _ hGammaOrd hAsOrd _ _ _ hCsSub _ _, hSLD, hAll => by
-- BEGIN PROOF
    obtain ⟨_hSLDL, _hSLDR, hB⟩ := hSLD
    rcases hB with hAx | hB
    · obtain ⟨P, _, hNeg⟩ := hAx
      rcases hAll _ hNeg with hEmpty | ⟨R, hR⟩
      · exact single_ne_empty _ hEmpty
      · exact Literal.noConfusion ((Finset.mem_singleton _ _).mp hR)
    cases B with
    | pos P =>
      obtain ⟨_hCsNeg, _hAxiom, hNegInGamma, _hDrop, _hWit⟩ := hB
      have hNegInS : Clause.single (Literal.neg P) ∈
          Finset.union Gamma (ClauseSequent.mapSet As
            (fun A => clauseWithLiteral A (Literal.pos P))) :=
        (Finset.mem_union_exp _ _ _).mpr (Or.inl hNegInGamma)
      rcases hAll _ hNegInS with hEmpty | ⟨R, hR⟩
      · exact single_ne_empty _ hEmpty
      · exact Literal.noConfusion ((Finset.mem_singleton _ _).mp hR)
    | neg Q =>
      obtain ⟨_hGoalSplit, _hCsAllNeg, ⟨G, hGCs, hGGoal, _hGNoNegQ, _hGUnique⟩⟩ := hB
      have hGinAs : G ∈ As := hCsSub _ hGCs
      have hcwlMem : clauseWithLiteral G (Literal.neg Q) ∈
          Finset.union Gamma (ClauseSequent.mapSet As
            (fun A => clauseWithLiteral A (Literal.neg Q))) :=
        (Finset.mem_union_exp _ _ _).mpr
          (Or.inr ((mem_image_iff _ _ _).mpr ⟨G, hGinAs, rfl⟩))
      rcases hAll _ hcwlMem with hEmpty | ⟨R, hR⟩
      · exact cwl_ne_empty G (Literal.neg Q) hEmpty
      · -- clauseWithLiteral G (neg Q) = insert (neg Q) G; R ∈ it means R = neg Q or R ∈ G.
        show False
        have hRinsert : Literal.pos R ∈ Finset.insert (Literal.neg Q) G := hR
        rw [Finset.mem_insert_exp] at hRinsert
        rcases hRinsert with hEq | hInG
        · exact Literal.noConfusion hEq
        · have := hGGoal.2 (Literal.pos R) hInG
          simp at this

helper /-- Helper (Thm 9.2.1 goal-split support): any SLD-form proof of
    `Γ ∪ {{¬Q}}` (where every clause in `Γ` is definite, hence `{¬P} ∉ Γ`)
    satisfies `isSLDForm_goalSplit Q`. The rule B = ¬Q' case is ruled out by
    showing its Cs witness would need to be `∅`, which in turn would force the
    left subtree onto a sequent consisting of `∅` plus definite clauses, and
    such a sequent has no SLD-form proof (by `isSLDForm_empty_or_pos_impossible`). -/
theorem isSLDForm_goalSplit_of_definite_context
    (Gamma : ClauseSequent) (Q : Nat)
    (hGammaDef : ∀ C ∈ Gamma, isDefiniteClause C)
    (T : GCNFProofTree
          (Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q)))))
    (hSLD : isSLDForm T) :
    isSLDForm_goalSplit Q T := by
  have hMem : Clause.single (Literal.neg Q) ∈
      Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q))) :=
    Finset.mem_union.mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
  have hUnique : ∀ C ∈ Finset.union Gamma
      (ClauseSequent.single (Clause.single (Literal.neg Q))),
      isGoalClause C → C = Clause.single (Literal.neg Q) := by
    intro C hC hGoal
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨P, hP⟩ := (hGammaDef C hC).2
      exact False.elim (hGoal.2 _ hP)
    · exact (Finset.mem_singleton _ _).mp hC
  generalize hS : Finset.union Gamma
      (ClauseSequent.single (Clause.single (Literal.neg Q))) = S at T
  have hMemS := hS ▸ hMem
  have hUniqueS := hS ▸ hUnique
  refine ⟨hMemS, hUniqueS, ?_⟩
  cases T with
  | axiom_ _ _ hTriv => exact Or.inl hTriv
  | rule G As B Cs G1 G2 hG hAs left right hNe hSub hG1 hG2 =>
    rcases hSLD.2.2 with hTriv | hLocal
    · exact Or.inl hTriv
    apply Or.inr
    cases B with
    | pos P =>
      have hPQ := hUniqueS _ (Finset.mem_union.mpr (Or.inl hLocal.2.2.1))
        (singleton_neg_is_goal P)
      have hLit := single_eq_implies_lit_eq (.neg P) (.neg Q) hPQ
      have : P = Q := Literal.neg.inj hLit
      subst P
      exact ⟨rfl, hLocal.2.1⟩
    | neg R =>
      obtain ⟨_, _, Gbody, hBody, hGoal, hNot, _⟩ := hLocal
      have hIns : isGoalClause (clauseWithLiteral Gbody (.neg R)) := by
        have hn : allNegative (clauseWithLiteral Gbody (.neg R)) := by
          intro l hl
          rcases Finset.mem_insert.mp hl with rfl | hl
          · trivial
          · exact hGoal.2 l hl
        exact ⟨⟨Clause.ordinary_of_mem (Finset.mem_insert.mpr (Or.inl rfl)),
          fun P Q hP _ => False.elim (hn _ hP)⟩, hn⟩
      have heq := hUniqueS _ (Finset.mem_union.mpr (Or.inr
        ((mem_image_iff _ _ _).mpr ⟨Gbody, hSub _ hBody, rfl⟩))) hIns
      have hR : Literal.neg R ∈ Clause.single (.neg Q) := heq ▸
        (show Literal.neg R ∈ clauseWithLiteral Gbody (.neg R) from
          Finset.mem_insert.mpr (Or.inl rfl))
      have hRQ := (Finset.mem_singleton _ _).mp hR
      obtain ⟨l, hl⟩ := Finset.nonempty_of_ne_empty Gbody hGoal.1.1
      have hlQ : l ∈ Clause.single (.neg Q) := heq ▸
        (show l ∈ clauseWithLiteral Gbody (.neg R) from Finset.mem_insert.mpr (Or.inr hl))
      have hlR : l = Literal.neg R := ((Finset.mem_singleton _ _).mp hlQ).trans hRQ.symm
      exact False.elim (hNot (hlR ▸ hl))

helper /-- If `D.card ≥ 2`, then `D` cannot equal any singleton clause. This is the
    combinatorial fact justifying that the axiom-case of `isSLDForm_goalSplit`
    survives weakening by `D` (no new complementary pairs can arise, because
    singletons `{pos P}` / `{neg P}` in `insert D S` must already be in `S`). -/
theorem single_ne_of_card_ge_two (D : Clause) (hCard : D.card ≥ 2) (L : Literal) :
    Clause.single L ≠ D := by
-- BEGIN PROOF
  intro heq
  have : (Clause.single L).card = D.card := congrArg Finset.card heq
  -- (Clause.single L).card = 1.
  have hcard : (Clause.single L).card = 1 := by
    show (Finset.singleton L).card = 1
    show ([L] : List Literal).length = 1
    rfl
  rw [hcard] at this; omega

helper /-- Transport helper: inserting a single clause into a union commutes into the
    left operand. `insert D (Γ ∪ M) = (insert D Γ) ∪ M`. -/
theorem insert_union_left (D : Clause) (Γ M : ClauseSequent) :
    Finset.insert D (Finset.union Γ M) =
      Finset.union (Finset.insert D Γ) M := by
-- BEGIN PROOF
  apply Finset.ext; intro C
  rw [Finset.mem_insert_exp, Finset.mem_union_exp, Finset.mem_union_exp,
      Finset.mem_insert_exp]
  constructor
  · rintro (rfl | hG | hM)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr hG)
    · exact Or.inr hM
  · rintro ((rfl | hG) | hM)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hG)
    · exact Or.inr (Or.inr hM)

helper /-- Add an ordinary clause at the root only. The existing premise trees and
    their contexts stay fixed, so exact cancellation labels are preserved.
    This is the insertion form of GCNFProofTree.weaken. -/
def sldWeakenByDefinite (D : Clause) (hDOrd : D.isOrdinary) :
    {S : ClauseSequent} → GCNFProofTree S → GCNFProofTree (Finset.insert D S)
  | _, .axiom_ S hOrd hTriv =>
    .axiom_ (Finset.insert D S) (ordinary_insert hDOrd hOrd) ⟨hTriv.choose,
      Finset.mem_insert.mpr (Or.inr hTriv.choose_spec.1),
      Finset.mem_insert.mpr (Or.inr hTriv.choose_spec.2)⟩
  | _, .rule G As B Cs G1 G2 hG hAs left right hNe hSub hG1 hG2 =>
    have hEq := insert_union_left D G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))
    hEq.symm ▸ GCNFProofTree.rule (Finset.insert D G) As B Cs G1 G2
      (ordinary_insert hDOrd hG) hAs left right hNe hSub
      (fun C hC => by
        rw [← hEq]
        exact Finset.mem_insert.mpr (Or.inr (hG1 C hC)))
      (fun C hC => by
        rw [← hEq]
        exact Finset.mem_insert.mpr (Or.inr (hG2 C hC)))

helper /-- Transport invariance for `isSLDForm`: the property is preserved under
    conclusion-equality transport `h ▸ t`. -/
theorem isSLDForm_transport
    {X Y : ClauseSequent} (t : GCNFProofTree X) (h : X = Y) :
    isSLDForm t → isSLDForm (h ▸ t) := by
-- BEGIN PROOF
  intro ht; subst h; exact ht

helper /-- Transport invariance for `isAxiomNode`. -/
theorem isAxiomNode_transport
    {X Y : ClauseSequent} (t : GCNFProofTree X) (h : X = Y) :
    isAxiomNode t → isAxiomNode (h ▸ t) := by
-- BEGIN PROOF
  intro ht; subst h; exact ht

helper /-- Transport invariance for `isAxiomNodeWith Q`. -/
theorem isAxiomNodeWith_transport (Q : Nat)
    {X Y : ClauseSequent} (t : GCNFProofTree X) (h : X = Y) :
    isAxiomNodeWith Q t → isAxiomNodeWith Q (h ▸ t) := by
-- BEGIN PROOF
  intro ht; subst h; exact ht

helper /-- Transport invariance for `isSLDForm_goalSplit Q`. -/
theorem isSLDForm_goalSplit_transport (Q : Nat)
    {X Y : ClauseSequent} (t : GCNFProofTree X) (h : X = Y) :
    isSLDForm_goalSplit Q t → isSLDForm_goalSplit Q (h ▸ t) := by
-- BEGIN PROOF
  intro ht; subst h; exact ht

helper /-- `sldWeakenByDefinite` preserves `isAxiomNode`: if `T` is an axiom leaf, so
    is its weakening. Structural by pattern match on `T`. -/
theorem isAxiomNode_sldWeakenByDefinite (D : Clause) (hDOrd : D.isOrdinary) :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isAxiomNode T → isAxiomNode (sldWeakenByDefinite D hDOrd T)
  | _, .axiom_ _ hOrd _, _ => by
-- BEGIN PROOF
    show isAxiomNode (sldWeakenByDefinite D hDOrd (.axiom_ _ _ _))
    unfold sldWeakenByDefinite
    trivial
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd _ _ _ _ _ _, h => h.elim

helper /-- Root-only weakening preserves SLD form: the local condition is either
    exempt by an existing trivial label or witnessed by the unchanged children. -/
theorem isSLDForm_sldWeakenByDefinite (D : Clause) (hDOrd : D.isOrdinary) (hDDef : isDefiniteClause D)
    (hDcard : D.card ≥ 2) :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isSLDForm T → isSLDForm (sldWeakenByDefinite D hDOrd T)
  | _, .axiom_ _ _ _, _ => trivial
  | _, .rule G As B Cs G1 G2 hG hAs left right hNe hSub hG1 hG2, h => by
    unfold sldWeakenByDefinite
    apply isSLDForm_transport
    refine ⟨h.1, h.2.1, ?_⟩
    rcases h.2.2 with hAx | hLocal
    · apply Or.inl
      obtain ⟨P, hp, hn⟩ := hAx
      refine ⟨P, ?_, ?_⟩ <;>
        rw [← insert_union_left] <;>
        exact Finset.mem_insert.mpr (Or.inr (by assumption))
    · apply Or.inr
      cases B with
      | pos P =>
        exact ⟨hLocal.1, hLocal.2.1,
          Finset.mem_insert.mpr (Or.inr hLocal.2.2.1), hLocal.2.2.2⟩
      | neg Q => exact hLocal

helper /-- Adding a multi-literal definite clause to the root sequent preserves the
    existence of an SLD-form proof. Existing premise trees stay unchanged. -/
theorem isSLDForm_weaken_by_definite :
    ∀ (S : ClauseSequent) (T : GCNFProofTree S),
      isSLDForm T → ∀ (D : Clause), isDefiniteClause D → D.card ≥ 2 →
      ∃ T' : GCNFProofTree (Finset.insert D S), isSLDForm T' := by
-- BEGIN PROOF
  intro S T hSLD D hDDef hDcard
  exact ⟨sldWeakenByDefinite D (ordinary_of_definite hDDef) T,
    isSLDForm_sldWeakenByDefinite D (ordinary_of_definite hDDef) hDDef hDcard T hSLD⟩

proof_of sld_form_completeness := by
  -- BEGIN PROOF
    -- Proof of Theorem 9.2.1 (Completeness of proofs in SLD-form):
    -- By well-founded induction on `totalLits S'`. The textbook uses proof depth,
    -- but we use a combinatorial measure that decreases when we replace the goal
    -- clause B' with a strictly smaller clause (either B' ∖ {neg Q} or {neg Q}).
    -- B is non-empty by hBne (textbook assumes n ≥ 1 in B = {neg P_1, ..., neg P_n}).
    -- Strong induction on totalLits S', threading the non-emptiness witness.
    suffices h : ∀ (n : Nat) (S' : ClauseSequent)
        (_hDef' : ∀ C ∈ S', isDefiniteClause C ∨ isGoalClause C)
        (B' : Clause)
        (_hB' : B' ∈ S')
        (_hGoalB' : isGoalClause B')
        (_hBne' : B' ≠ Clause.empty)
        (_hUnique' : ∀ C ∈ S', isGoalClause C → C = B')
        (_hProv' : GCNFProvable S')
        (_hMeasure : totalLits S' ≤ n),
        ∃ T' : GCNFProofTree S', isSLDForm T' by
      exact h (totalLits S) S hDef B hB hGoalB hBne hUnique hProv (Nat.le_refl _)
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro S' hDef' B' hB' hGoalB' hBne' hUnique' hProv' hMeasure
      -- Case analysis on whether S' is an axiom (has complementary pair)
      by_cases hTriv : ∃ P : Nat, Clause.single (Literal.pos P) ∈ S' ∧
          Clause.single (Literal.neg P) ∈ S'
      · -- S' has a complementary pair: build axiom (trivially SLD-form)
        obtain ⟨T⟩ := hProv'
        exact ⟨.axiom_ S' T.ordinary hTriv, trivial⟩
      · -- S' is not an axiom. S' is provable but not trivial.
        -- B' is nonempty by the threaded hypothesis hBne'.
        -- B' has at least one literal.
        have hExLit : ∃ l : Literal, l ∈ B' :=
          Classical.byContradiction fun h =>
            hBne' (Finset.ext fun x =>
              ⟨fun hx => (h ⟨x, hx⟩).elim,
               fun hx => ((Finset.mem_empty x).mp hx).elim⟩)
        -- B' is a goal clause so every literal in B' is negative.
        have hBNeg : ∀ l ∈ B', ∃ Q : Nat, l = Literal.neg Q := by
          intro l hl
          have := hGoalB'.2 l hl
          match l, this with
          | Literal.neg Q, _ => exact ⟨Q, rfl⟩
        -- Extract a concrete negative literal neg Q ∈ B'.
        obtain ⟨l0, hl0⟩ := hExLit
        obtain ⟨Q, hQeq⟩ := hBNeg l0 hl0
        have hnegQ : Literal.neg Q ∈ B' := hQeq ▸ hl0
        -- Clauses in Gamma := S'.erase B' are all definite (not goal, by uniqueness).
        have hGammaDef : ∀ C ∈ S'.erase B', isDefiniteClause C := by
          intro C hC
          have ⟨hCS, hCne⟩ := (Finset.mem_erase _ _ _).mp hC
          rcases hDef' C hCS with hDefC | hGoalC
          · exact hDefC
          · exact absurd (hUnique' C hCS hGoalC) hCne
        -- The key case split:
        -- If B'.card ≥ 2: goal-splitting (split B' at root)
        -- If B'.card = 1: resolution with a definite clause
        -- In both cases, the induction measure totalLits decreases.
        by_cases hCard : B'.card ≥ 2
        · -- ========= Case B'.card ≥ 2: goal-splitting =========
          -- Define B'' := B'.erase (neg Q) and Gamma := S'.erase B'.
          -- Apply ∨:left with B = neg Q, As = Cs = {B''}. Since neg Q ∈ B',
          --   clauseWithLiteral B'' (neg Q) = insert (neg Q) B'' = B', so
          --   conclusion = Gamma ∪ mapSet {B''} (cwl · (neg Q)) = Gamma ∪ {B'} = S'.
          -- Left subtree: Gamma ∪ {B''}, goal clause B'' (card = B'.card - 1, ≥ 1).
          -- Right subtree: Gamma ∪ {{neg Q}}, goal clause {neg Q} (card = 1).
          -- Both measures decrease (B' replaced by smaller clauses).
          let Gamma := S'.erase B'
          let B'' := B'.erase (Literal.neg Q)
          -- Basic cardinalities.
          have hB''card : B''.card + 1 = B'.card := by
            -- Cardinality of erase: card (S.erase a) + 1 = card S when a ∈ S.
            show (B'.erase (Literal.neg Q)).card + 1 = B'.card
            cases hB'mk : B' with | mk v nd =>
            induction v using LCS.Multiset.ind with
            | _ l =>
              have hlmem : Literal.neg Q ∈ l := by
                have : Literal.neg Q ∈ B' := hnegQ
                rw [hB'mk] at this
                exact this
              show (l.erase (Literal.neg Q)).length + 1 = l.length
              have hperm : l.Perm (Literal.neg Q :: l.erase (Literal.neg Q)) :=
                List.perm_cons_erase hlmem
              have := hperm.length_eq
              simp at this; omega
          have hB''ne : B'' ≠ Clause.empty := by
            intro h
            have : B''.card = 0 := by rw [h]; rfl
            omega
          have hB''card_lt : B''.card < B'.card := by omega
          -- B'' ⊆ B', so all literals in B'' are negative (goal clause).
          have hB''sub : ∀ l ∈ B'', l ∈ B' :=
            fun _ hl => ((Finset.mem_erase _ _ _).mp hl).1
          have hGoalB'' : isGoalClause B'' := by
            refine ⟨?_, ?_⟩
            · exact isHornClause_of_subset B' B'' hGoalB'.1 hB''sub hB''ne
            · intro l hl
              exact hGoalB'.2 l (hB''sub l hl)
          -- neg Q ∉ B''.
          have hnegQnB'' : Literal.neg Q ∉ B'' :=
            fun h => (((Finset.mem_erase _ _ _).mp h).2) rfl
          -- cwl B'' (neg Q) = B'.
          have hcwlEq : clauseWithLiteral B'' (Literal.neg Q) = B' := by
            show Finset.insert (Literal.neg Q) B'' = B'
            apply Finset.ext; intro x
            rw [Finset.mem_insert_exp]
            constructor
            · intro h
              rcases h with rfl | h
              · exact hnegQ
              · exact hB''sub _ h
            · intro hx
              by_cases hxeq : x = Literal.neg Q
              · exact Or.inl hxeq
              · exact Or.inr ((Finset.mem_erase _ _ _).mpr ⟨hx, hxeq⟩)
          -- B'' ∉ Gamma (else Gamma ∪ {B''} = Gamma, but B'' ≠ B' so it's a new clause).
          -- More precisely: B'' ∉ S'.erase B'. If B'' ∈ Gamma, then B'' ∈ S' and B'' ≠ B'.
          -- But B'' is a goal clause (by hGoalB''), so hUnique' forces B'' = B', contradiction.
          have hB''nmem : B'' ∉ S'.erase B' := by
            intro h
            have ⟨hMem, hNe⟩ := (Finset.mem_erase _ _ _).mp h
            have := hUnique' B'' hMem hGoalB''
            exact hNe this
          -- {neg Q} is a goal clause.
          have hSingleNegQ_goal : isGoalClause (Clause.single (Literal.neg Q)) := by
            refine ⟨isHornClause_single _, ?_⟩
            intro l hl
            have hleq : l = Literal.neg Q := (Finset.mem_singleton l (Literal.neg Q)).mp hl
            subst hleq; trivial
          have hSingleNegQ_ne : Clause.single (Literal.neg Q) ≠ Clause.empty :=
            single_ne_empty _
          -- {neg Q} ∉ Gamma: similar argument (goal clause unique).
          have hSingleNegQ_nmem : Clause.single (Literal.neg Q) ∉ S'.erase B' := by
            intro h
            have ⟨hMem, hNe⟩ := (Finset.mem_erase _ _ _).mp h
            have := hUnique' (Clause.single (Literal.neg Q)) hMem hSingleNegQ_goal
            exact hNe this
          -- S' = Gamma ∪ {B'}.
          have hS'_decomp : S' = Finset.union Gamma (ClauseSequent.single B') := by
            apply Finset.ext; intro C
            rw [Finset.mem_union_exp, Finset.mem_erase, mem_csingle]
            constructor
            · intro hC
              by_cases hCB : C = B'
              · exact Or.inr hCB
              · exact Or.inl ⟨hC, hCB⟩
            · intro h
              rcases h with ⟨h1, _⟩ | rfl
              · exact h1
              · exact hB'
          -- {B'} = mapSet {B''} (cwl · (neg Q)).
          have hSing_eq_mapset : ClauseSequent.single B' =
              ClauseSequent.mapSet (ClauseSequent.single B'') (fun A => clauseWithLiteral A (Literal.neg Q)) := by
            apply Finset.ext; intro C
            rw [mem_csingle]
            constructor
            · intro hC
              refine (mem_image_iff _ _ _).mpr ⟨B'', (mem_csingle B'' B'').mpr rfl, ?_⟩
              rw [hcwlEq]; exact hC.symm
            · intro hC
              obtain ⟨A, hA, hCA⟩ := (mem_image_iff _ _ _).mp hC
              rw [(mem_csingle A B'').mp hA] at hCA
              rw [hcwlEq] at hCA
              exact hCA.symm
          -- Combined: S' = Gamma ∪ mapSet {B''} (cwl · (neg Q)).
          have hS'_eq_rule : S' = Finset.union Gamma
              (ClauseSequent.mapSet (ClauseSequent.single B'')
                (fun A => clauseWithLiteral A (Literal.neg Q))) := by
            rw [hS'_decomp, hSing_eq_mapset]
          -- Provability of the two sub-sequents follows from ∨:left invertibility
          -- (Lemma 9.2.2): S' = Gamma ∪ {B' = B'' ∨ {neg Q}} is provable, hence so are
          -- Gamma ∪ {B''} (left premise) and Gamma ∪ {{neg Q}} (right premise).
          have hCwlMem : clauseWithLiteral B'' (Literal.neg Q) ∈ S' := hcwlEq ▸ hB'
          -- Every clause in Gamma = S'.erase B' is definite, hence non-empty.
          have hGammaNe : ∀ C ∈ Finset.erase S' (clauseWithLiteral B'' (Literal.neg Q)),
              C ≠ Clause.empty := by
            intro C hC hCeq
            -- Rewrite the erased clause back to B' via hcwlEq.
            have hCGamma : C ∈ Gamma := by
              show C ∈ Finset.erase S' B'
              have : Finset.erase S' (clauseWithLiteral B'' (Literal.neg Q)) =
                  Finset.erase S' B' := by rw [hcwlEq]
              rwa [this] at hC
            -- C is definite; pick a positive literal, but then C = ∅ is impossible.
            obtain ⟨_, P, hPinC⟩ := hGammaDef C hCGamma
            have : Literal.pos P ∈ Clause.empty := hCeq ▸ hPinC
            exact (Finset.mem_empty (Literal.pos P)).mp this
          -- Apply ∨:left invertibility (Lem 9.2.2) to S' at the clause B' = cwl B'' (neg Q).
          have hSplit := gcnf_provable_clause_split S' B'' (Literal.neg Q)
            hCwlMem hB''ne hGammaNe hProv'
          -- Rewrite the erased clause back to B' in both sub-sequents.
          have hEraseEq : Finset.erase S' (clauseWithLiteral B'' (Literal.neg Q)) = Gamma := by
            show Finset.erase S' (clauseWithLiteral B'' (Literal.neg Q)) = Finset.erase S' B'
            rw [hcwlEq]
          have hLeftProv : GCNFProvable (Finset.union Gamma (ClauseSequent.single B'')) := by
            have := hSplit.1
            rwa [hEraseEq] at this
          have hRightProv : GCNFProvable (Finset.union Gamma
              (ClauseSequent.single (Clause.single (Literal.neg Q)))) := by
            have := hSplit.2
            rwa [hEraseEq] at this
          -- Sub-sequent definite/goal hypotheses.
          have hDefLeft : ∀ C ∈ Finset.union Gamma (ClauseSequent.single B''),
              isDefiniteClause C ∨ isGoalClause C := by
            intro C hC
            rw [Finset.mem_union_exp] at hC
            rcases hC with hGamma | hSing
            · exact Or.inl (hGammaDef C hGamma)
            · rw [mem_csingle] at hSing
              subst hSing
              exact Or.inr hGoalB''
          have hDefRight : ∀ C ∈ Finset.union Gamma
              (ClauseSequent.single (Clause.single (Literal.neg Q))),
              isDefiniteClause C ∨ isGoalClause C := by
            intro C hC
            rw [Finset.mem_union_exp] at hC
            rcases hC with hGamma | hSing
            · exact Or.inl (hGammaDef C hGamma)
            · rw [mem_csingle] at hSing
              subst hSing
              exact Or.inr hSingleNegQ_goal
          -- Uniqueness hypotheses: Gamma has no goal clauses.
          have hGammaNoGoal : ∀ C ∈ Gamma, ¬ isGoalClause C := by
            intro C hC hGC
            have hDefC := hGammaDef C hC
            -- A definite clause has a positive literal; a goal clause has all negative — contradiction.
            obtain ⟨P, hP⟩ := hDefC.2
            have := hGC.2 (Literal.pos P) hP
            simp at this
          have hUniqueLeft : ∀ C ∈ Finset.union Gamma (ClauseSequent.single B''),
              isGoalClause C → C = B'' := by
            intro C hC hGC
            rw [Finset.mem_union_exp] at hC
            rcases hC with hGamma | hSing
            · exact absurd hGC (hGammaNoGoal C hGamma)
            · rw [mem_csingle] at hSing; exact hSing
          have hUniqueRight : ∀ C ∈ Finset.union Gamma
              (ClauseSequent.single (Clause.single (Literal.neg Q))),
              isGoalClause C → C = Clause.single (Literal.neg Q) := by
            intro C hC hGC
            rw [Finset.mem_union_exp] at hC
            rcases hC with hGamma | hSing
            · exact absurd hGC (hGammaNoGoal C hGamma)
            · rw [mem_csingle] at hSing; exact hSing
          -- B'' ∈ Gamma ∪ {B''} and {neg Q} ∈ Gamma ∪ {{neg Q}}.
          have hB''mem : B'' ∈ Finset.union Gamma (ClauseSequent.single B'') :=
            (Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_csingle B'' B'').mpr rfl))
          have hSingQmem : Clause.single (Literal.neg Q) ∈ Finset.union Gamma
              (ClauseSequent.single (Clause.single (Literal.neg Q))) :=
            (Finset.mem_union_exp _ _ _).mpr (Or.inr
              ((mem_csingle _ _).mpr rfl))
          -- totalLits decrease: left side and right side.
          have hLeftMeasure :
              totalLits (Finset.union Gamma (ClauseSequent.single B'')) < totalLits S' := by
            -- S' = Gamma ∪ {B'}, and Gamma ∪ {B''} = insert B'' Gamma where B'' ∉ Gamma.
            -- Apply totalLits_replace_with_smaller.
            have hGammaEq : Gamma = S'.erase B' := rfl
            have hInsertEq : Finset.union Gamma (ClauseSequent.single B'') =
                Finset.insert B'' (S'.erase B') := by
              apply Finset.ext; intro x
              rw [Finset.mem_union_exp, Finset.mem_insert_exp, mem_csingle]
              exact ⟨fun h => h.symm.imp id id, fun h => h.symm.imp id id⟩
            rw [hInsertEq]
            exact totalLits_replace_with_smaller S' B' B'' hB' hB''nmem hB''card_lt
          have hRightMeasure :
              totalLits (Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q))))
                < totalLits S' := by
            have hInsertEq : Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q))) =
                Finset.insert (Clause.single (Literal.neg Q)) (S'.erase B') := by
              apply Finset.ext; intro x
              rw [Finset.mem_union_exp, Finset.mem_insert_exp, mem_csingle]
              exact ⟨fun h => h.symm.imp id id, fun h => h.symm.imp id id⟩
            rw [hInsertEq]
            refine totalLits_replace_with_smaller S' B' (Clause.single (Literal.neg Q)) hB'
              hSingleNegQ_nmem ?_
            -- (Clause.single _).card = 1 < B'.card (since B'.card ≥ 2).
            have : (Clause.single (Literal.neg Q)).card = 1 := by
              show ([Literal.neg Q] : List _).length = 1
              rfl
            omega
          -- Apply IH to each subtree.
          obtain ⟨leftTree, hLeftSLD⟩ := ih (totalLits (Finset.union Gamma (ClauseSequent.single B'')))
            (Nat.lt_of_lt_of_le hLeftMeasure hMeasure)
            (Finset.union Gamma (ClauseSequent.single B''))
            hDefLeft B'' hB''mem hGoalB'' hB''ne hUniqueLeft hLeftProv (Nat.le_refl _)
          obtain ⟨rightTree, hRightSLD⟩ := ih
            (totalLits (Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q)))))
            (Nat.lt_of_lt_of_le hRightMeasure hMeasure)
            (Finset.union Gamma (ClauseSequent.single (Clause.single (Literal.neg Q))))
            hDefRight (Clause.single (Literal.neg Q)) hSingQmem hSingleNegQ_goal hSingleNegQ_ne
            hUniqueRight hRightProv (Nat.le_refl _)
          -- Combine via .rule with B = neg Q, As = Cs = {B''}, Gamma = Gamma1 = Gamma2 = Gamma.
          have hCsNonempty : ∃ C, C ∈ ClauseSequent.single B'' :=
            ⟨B'', (mem_csingle B'' B'').mpr rfl⟩
          have hCsSub : LCS.Finset.Subset (ClauseSequent.single B'')
              (ClauseSequent.single B'') := fun _ h => h
          have hGsub : LCS.Finset.Subset Gamma
              (Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single B'')
                (fun A => clauseWithLiteral A (Literal.neg Q)))) :=
            fun _ h => (Finset.mem_union_exp _ _ _).mpr (Or.inl h)
          -- The .rule conclusion is Gamma ∪ mapSet {B''} (cwl · (neg Q)) = S'.
          -- Rewrite the goal to match the rule tree's type so we can build it directly.
          rw [hS'_eq_rule]
          -- Construct the rule tree at the exact index.
          refine ⟨GCNFProofTree.rule Gamma (ClauseSequent.single B'') (Literal.neg Q)
              (ClauseSequent.single B'') Gamma Gamma (ordinary_left leftTree) (ordinary_right leftTree) leftTree rightTree
              hCsNonempty hCsSub hGsub hGsub, ?_⟩
          -- Prove isSLDForm of the constructed rule tree.
          -- isSLDForm unfolds on the .rule constructor; B = neg Q case adds 3 conjuncts.
          show isSLDForm _  -- keeps it schematic so the pattern match reduces
          unfold isSLDForm
          refine ⟨hLeftSLD, hRightSLD, Or.inr ⟨?_, ?_, ?_⟩⟩
          · -- isSLDForm_goalSplit Q rightTree follows from rightTree's sequent
            -- Gamma ∪ {{neg Q}} being definite-only-plus-{¬Q}: Γ all-definite forces
            -- the rule's B' = pos Q branch (the only way to close on a singleton neg),
            -- and the degenerate B' = neg Q branch is ruled out by contradiction.
            exact isSLDForm_goalSplit_of_definite_context Gamma Q hGammaDef
              rightTree hRightSLD
          · -- All literals in Cs = {B''} are negative.
            intro C hC l hl
            rw [mem_csingle] at hC
            subst hC
            have hlB' := hB''sub l hl
            have hlneg := hGoalB'.2 l hlB'
            match l, hlneg with
            | Literal.neg _, _ => trivial
          · -- ∃ G ∈ Cs, goal clause G, neg Q ∉ G, G unique in Gamma ∪ Cs.
            refine ⟨B'', (mem_csingle B'' B'').mpr rfl, hGoalB'', ?_, ?_⟩
            · -- neg Q ∉ B'' since B'' = B'.erase (neg Q).
              show Literal.neg Q ∉ B'.erase (Literal.neg Q)
              exact fun h => ((Finset.mem_erase _ _ _).mp h).2 rfl
            · intro C hC hGC
              rw [Finset.mem_union_exp] at hC
              rcases hC with hGamma | hSing
              · exact absurd hGC (hGammaNoGoal C hGamma)
              · rw [mem_csingle] at hSing; exact hSing
        · -- ========= Case B'.card = 1: resolution with a definite clause =========
          -- B' has at least one literal (neg Q), so B'.card ≥ 1.
          -- ¬(B'.card ≥ 2) combined with B'.card ≥ 1 gives B'.card = 1,
          -- so B' = Clause.single (neg Q).
          -- Strategy (textbook Thm 9.2.1 Case =1): apply ∨:left to resolve
          -- B' = {¬Q} with a definite clause C = {¬Q_1,...,¬Q_p, pos Q}.
          -- rule at root splits into:
          --   right: axiom {pos Q, ¬Q} (since Gamma2 ∋ B' = {¬Q}),
          --   left:  Gamma1 ∪ {A} where A = C.erase (pos Q), the new all-negative goal.
          -- Gamma1 drops B' so the left subtree has a unique goal A (dropping
          -- the exhausted goal {¬Q} is justified by Lem 9.2.5: the left premise
          -- Gamma_C ∪ {A, B'} with two goals is GCNF'-provable, so one of them
          -- alone suffices; weakening from Gamma_C ∪ {A} argument using
          -- goal_reduction).
          -- The {pos Q} ∈ S' unit-axiom sub-case doesn't occur here: hTriv rules
          -- it out (with B' = {¬Q} ∈ S', having {pos Q} ∈ S' triggers triviality).
          have hB'card1 : B'.card = 1 := by
            have hCardGe1 : 1 ≤ B'.card := by
              cases hB'mk : B' with | mk v nd =>
              induction v using LCS.Multiset.ind with
              | _ l =>
                have hlmem : Literal.neg Q ∈ l := by
                  have : Literal.neg Q ∈ B' := hnegQ
                  rw [hB'mk] at this; exact this
                show 1 ≤ l.length
                cases hv : l with
                | nil => rw [hv] at hlmem; exact absurd hlmem List.not_mem_nil
                | cons _ _ => simp [List.length]
            omega
          have hB'eq : B' = Clause.single (Literal.neg Q) := by
            apply Finset.ext; intro x; constructor
            · intro hx
              have := finset_card_one_eq hB'card1 x (Literal.neg Q) hx hnegQ
              exact (Finset.mem_singleton x (Literal.neg Q)).mpr this
            · intro hx
              rw [(Finset.mem_singleton x (Literal.neg Q)).mp hx]; exact hnegQ
          -- hTriv forces {pos Q} ∉ S' (else P=Q witnesses triviality).
          have hPosQ_nmem : Clause.single (Literal.pos Q) ∉ S' := by
            intro hPos
            apply hTriv
            refine ⟨Q, hPos, ?_⟩
            rw [← hB'eq]; exact hB'
          -- S' is valid (unsatisfiable) by soundness.
          have hValid : ClauseSequent.isValid S' := gcnf_soundness S' hProv'
          -- Some clause in S' must contain `pos Q`; otherwise the valuation
          -- v = (Q ↦ false, else ↦ true) would satisfy S'.
          have hExClausePosQ : ∃ C, C ∈ S' ∧ Literal.pos Q ∈ C := by
            suffices h : ¬(∃ C, C ∈ S' ∧ Literal.pos Q ∈ C) → False from
              Classical.byContradiction fun hNo => h hNo
            intro hNoPos
            apply hValid
            refine ⟨fun n => if n = Q then false else true, fun C hC => ?_⟩
            -- Case on C = B' (goal {neg Q}, satisfied since Q=false) vs C ∈ Gamma.
            by_cases hCB : C = B'
            · subst hCB
              refine ⟨Literal.neg Q, hnegQ, ?_⟩
              show (if Q = Q then false else true) = false
              simp
            · -- C ∈ Gamma, definite with some pos R ∈ C; R ≠ Q since hNoPos.
              have hCGamma : C ∈ S'.erase B' := (Finset.mem_erase _ _ _).mpr ⟨hC, hCB⟩
              obtain ⟨_, R, hR⟩ := hGammaDef C hCGamma
              have hRneQ : R ≠ Q := fun heq => hNoPos ⟨C, hC, heq ▸ hR⟩
              refine ⟨Literal.pos R, hR, ?_⟩
              show (if R = Q then false else true) = true
              simp [hRneQ]
          obtain ⟨C, hCS', hPosInC⟩ := hExClausePosQ
          -- C is definite: it's not a goal clause (goal clauses are all-negative,
          -- but C has pos Q), so by hDef' it's definite.
          have hCDef : isDefiniteClause C := by
            rcases hDef' C hCS' with hDefC | hGoalC
            · exact hDefC
            · -- hGoalC: C all negative, but pos Q ∈ C. Contradiction.
              have := hGoalC.2 (Literal.pos Q) hPosInC
              exact absurd this (by simp)
          -- C ≠ B' since B' is goal clause (all-negative), C has pos Q.
          have hCneB' : C ≠ B' := by
            intro h; rw [h] at hPosInC
            have := hGoalB'.2 (Literal.pos Q) hPosInC
            exact absurd this (by simp)
          -- C ≠ Clause.single (Literal.pos Q) since {pos Q} ∉ S'.
          have hCneUnit : C ≠ Clause.single (Literal.pos Q) := by
            intro h; rw [h] at hCS'; exact hPosQ_nmem hCS'
          -- C has a literal other than pos Q (i.e., C.card ≥ 2).
          -- If every literal in C is pos Q, then C = {pos Q}, contradicting hCneUnit.
          have hExOther : ∃ l, l ∈ C ∧ l ≠ Literal.pos Q := by
            apply Classical.byContradiction; intro hNo
            have hAll : ∀ x ∈ C, x = Literal.pos Q := by
              intro x hx
              apply Classical.byContradiction; intro hne
              exact hNo ⟨x, hx, hne⟩
            apply hCneUnit
            apply Finset.ext; intro x; constructor
            · intro hx
              exact (Finset.mem_singleton x (Literal.pos Q)).mpr (hAll x hx)
            · intro hx
              rw [(Finset.mem_singleton x (Literal.pos Q)).mp hx]; exact hPosInC
          -- Let A := C.erase (pos Q). A is all-negative (Horn + unique pos literal).
          let A : Clause := C.erase (Literal.pos Q)
          -- A is subset of C.
          have hAsub : ∀ l ∈ A, l ∈ C :=
            fun _ hl => ((Finset.mem_erase _ _ _).mp hl).1
          -- pos Q ∉ A.
          have hPosQ_nmem_A : Literal.pos Q ∉ A :=
            fun h => (((Finset.mem_erase _ _ _).mp h).2) rfl
          -- A is nonempty (C has at least 2 literals: pos Q and something else).
          have hAne : A ≠ Clause.empty := by
            obtain ⟨l, hl, hlne⟩ := hExOther
            intro hAEmpty
            have : l ∈ A := (Finset.mem_erase _ _ _).mpr ⟨hl, hlne⟩
            rw [hAEmpty] at this
            exact (Finset.mem_empty l).mp this
          -- A.card + 1 = C.card (erase decreases card by 1 when element is present).
          have hAcard : A.card + 1 = C.card := by
            show (C.erase (Literal.pos Q)).card + 1 = C.card
            cases hCmk : C with | mk v nd =>
            induction v using LCS.Multiset.ind with
            | _ l =>
              have hlmem : Literal.pos Q ∈ l := by
                have : Literal.pos Q ∈ C := hPosInC
                rw [hCmk] at this; exact this
              show (l.erase (Literal.pos Q)).length + 1 = l.length
              have hperm : l.Perm (Literal.pos Q :: l.erase (Literal.pos Q)) :=
                List.perm_cons_erase hlmem
              have := hperm.length_eq
              simp at this; omega
          -- A is all-negative (C is Horn: its only positive literal is pos Q,
          -- which we removed).
          have hAallNeg : ∀ l ∈ A, ∃ R : Nat, l = Literal.neg R := by
            intro l hl
            have hlC : l ∈ C := hAsub l hl
            have hlNeQ : l ≠ Literal.pos Q := ((Finset.mem_erase _ _ _).mp hl).2
            cases l with
            | neg R => exact ⟨R, rfl⟩
            | pos R =>
              -- By Horn property, R = Q, but then l = pos Q, contradicting hlNeQ.
              have : R = Q := hCDef.1.2 R Q hlC hPosInC
              subst this; exact absurd rfl hlNeQ
          -- A is a goal clause.
          have hGoalA : isGoalClause A := by
            refine ⟨isHornClause_of_subset C A hCDef.1 hAsub hAne, ?_⟩
            intro l hl
            obtain ⟨R, hR⟩ := hAallNeg l hl
            rw [hR]; trivial
          -- cwl A (pos Q) = C.
          have hcwlEq : clauseWithLiteral A (Literal.pos Q) = C := by
            show Finset.insert (Literal.pos Q) A = C
            apply Finset.ext; intro x
            rw [Finset.mem_insert_exp]
            constructor
            · intro h
              rcases h with rfl | h
              · exact hPosInC
              · exact hAsub _ h
            · intro hx
              by_cases hxeq : x = Literal.pos Q
              · exact Or.inl hxeq
              · exact Or.inr ((Finset.mem_erase _ _ _).mpr ⟨hx, hxeq⟩)
          -- Let Gamma_C := S'.erase C. B' ∈ Gamma_C since B' ≠ C.
          let Gamma_C : ClauseSequent := S'.erase C
          have hB'_in_Gamma_C : B' ∈ Gamma_C :=
            (Finset.mem_erase _ _ _).mpr ⟨hB', fun heq => hCneB' heq.symm⟩
          -- Every clause in Gamma_C other than B' is definite (by hGammaDef).
          -- We'll need: all of Gamma_C except B' is definite; but B' ∈ Gamma_C is the goal.
          -- For the rule, we need Gamma_C ∪ mapSet({A}, cwl·(pos Q)) = S'.
          have hS'_decomp : S' = Finset.union Gamma_C (ClauseSequent.single C) := by
            apply Finset.ext; intro D
            rw [Finset.mem_union_exp, Finset.mem_erase, mem_csingle]
            constructor
            · intro hD
              by_cases hDC : D = C
              · exact Or.inr hDC
              · exact Or.inl ⟨hD, hDC⟩
            · intro h
              rcases h with ⟨h1, _⟩ | rfl
              · exact h1
              · exact hCS'
          have hSing_eq_mapset : ClauseSequent.single C =
              ClauseSequent.mapSet (ClauseSequent.single A)
                (fun X => clauseWithLiteral X (Literal.pos Q)) := by
            apply Finset.ext; intro D
            rw [mem_csingle]
            constructor
            · intro hD
              refine (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, ?_⟩
              rw [hcwlEq]; exact hD.symm
            · intro hD
              obtain ⟨X, hX, hDX⟩ := (mem_image_iff _ _ _).mp hD
              rw [(mem_csingle X A).mp hX] at hDX
              rw [hcwlEq] at hDX
              exact hDX.symm
          have hS'_eq_rule : S' = Finset.union Gamma_C
              (ClauseSequent.mapSet (ClauseSequent.single A)
                (fun X => clauseWithLiteral X (Literal.pos Q))) := by
            rw [hS'_decomp, hSing_eq_mapset]
          -- Provability of the two sub-sequents via ∨:left invertibility (Lem 9.2.2).
          have hCwlInS' : clauseWithLiteral A (Literal.pos Q) ∈ S' := hcwlEq ▸ hCS'
          -- All clauses in S'.erase (cwl A (pos Q)) = S'.erase C = Gamma_C are non-empty:
          -- they're either definite (from hGammaDef, treating Gamma = S'.erase B') or B' itself.
          -- B' = {neg Q}, which is non-empty.
          have hGammaNeSplit : ∀ D ∈ Finset.erase S' (clauseWithLiteral A (Literal.pos Q)),
              D ≠ Clause.empty := by
            intro D hD hDeq
            have hDGamma_C : D ∈ Gamma_C := by
              show D ∈ Finset.erase S' C
              have : Finset.erase S' (clauseWithLiteral A (Literal.pos Q)) =
                  Finset.erase S' C := by rw [hcwlEq]
              rwa [this] at hD
            have ⟨hDS', hDneC⟩ := (Finset.mem_erase _ _ _).mp hDGamma_C
            -- D ∈ S'. Case: D = B' or D ∈ Gamma = S'.erase B'.
            by_cases hDB' : D = B'
            · subst hDB'
              -- D = B' = {neg Q}; B' ≠ empty by hBne' or directly.
              exact hBne' hDeq
            · have hDGamma : D ∈ S'.erase B' := (Finset.mem_erase _ _ _).mpr ⟨hDS', hDB'⟩
              obtain ⟨_, P, hPinD⟩ := hGammaDef D hDGamma
              have : Literal.pos P ∈ Clause.empty := hDeq ▸ hPinD
              exact (Finset.mem_empty (Literal.pos P)).mp this
          have hSplit := gcnf_provable_clause_split S' A (Literal.pos Q)
            hCwlInS' hAne hGammaNeSplit hProv'
          have hEraseEq : Finset.erase S' (clauseWithLiteral A (Literal.pos Q)) = Gamma_C := by
            show Finset.erase S' (clauseWithLiteral A (Literal.pos Q)) = Finset.erase S' C
            rw [hcwlEq]
          have hLeftProv : GCNFProvable (Finset.union Gamma_C (ClauseSequent.single A)) := by
            have := hSplit.1
            rwa [hEraseEq] at this
          have hRightProv : GCNFProvable (Finset.union Gamma_C
              (ClauseSequent.single (Clause.single (Literal.pos Q)))) := by
            have := hSplit.2
            rwa [hEraseEq] at this
          -- To apply IH on the left subtree, we need a sequent with a unique
          -- goal clause. `Gamma_C ∪ {A}` has TWO goal clauses (A and B'), so
          -- we drop B' to get `Gamma1 ∪ {A}` with A as the unique goal. The
          -- provability of `Gamma1 ∪ {A}` is obtained from `Gamma_C ∪ {A}`
          -- (which we have from hLeftProv) by applying Lemma 9.2.5 (goal_reduction):
          -- since Gamma_C ∪ {A} has two goal clauses, one of them alone suffices.
          -- goal_reduction outputs ∃ i, (J ∪ defs ∪ {goal_i}) provable, where
          -- i = A yields our desired sequent Gamma1 ∪ {A}, and i = B' yields
          -- Gamma_C (prov'd via IH on Gamma_C then weakened by definite clause C).
          let Gamma1 : ClauseSequent := Gamma_C.erase B'
          -- Every clause in Gamma1 is definite.
          have hGamma1Def : ∀ D ∈ Gamma1, isDefiniteClause D := by
            intro D hD
            have ⟨hDGamma_C, hDneB'⟩ := (Finset.mem_erase _ _ _).mp hD
            have ⟨hDS', _⟩ := (Finset.mem_erase _ _ _).mp hDGamma_C
            exact hGammaDef D ((Finset.mem_erase _ _ _).mpr ⟨hDS', hDneB'⟩)
          -- A ∉ Gamma1: A is goal, so if A ∈ S' then A = B'. If A = B', A ∉ Gamma1
          -- (B' explicitly erased). If A ≠ B', A is not a goal clause in S', so A ∉ Gamma1.
          -- Actually Gamma1 has only definite clauses (from hGamma1Def), and A is goal.
          -- A definite clause has a positive literal; a goal clause has none. So A ∉ Gamma1.
          have hA_nmem_Gamma1 : A ∉ Gamma1 := by
            intro hAG1
            obtain ⟨_, P, hP⟩ := hGamma1Def A hAG1
            have := hGoalA.2 (Literal.pos P) hP
            exact absurd this (by simp)
          -- Prove left subtree provability: Gamma1 ∪ {A} is GCNF'-provable.
          -- Strategy: apply Lem 9.2.5 via horn_all_goals_sat_of_each_sat.
          -- Gamma_C ∪ {A} is provable (hLeftProv), hence valid. Gamma_C = Gamma1 ∪ {B'}.
          -- So (Gamma1 ∪ {A}) and (Gamma1 ∪ {B'}) cannot BOTH be satisfiable
          -- (else horn model intersection would satisfy Gamma1 ∪ {A, B'} = Gamma_C ∪ {A}).
          -- Hence at least one of (Gamma1 ∪ {A}), (Gamma_C) is valid → provable (Lem 4.2.1).
          -- Case α: Gamma1 ∪ {A} valid → apply IH → rule-tree construction.
          -- Case β: Gamma_C valid → Gamma_C provable → apply IH on Gamma_C → use
          --   SLD-preserving weakening by definite clause C to lift to S'.
          have hGamma1_as_JD : ∀ D ∈ Gamma1,
              (∃ P : Nat, D = Clause.single (Literal.pos P)) ∨ isDefiniteClause D :=
            fun D hD => Or.inr (hGamma1Def D hD)
          have hLeftProv_valid : ClauseSequent.isValid (Finset.union Gamma_C (ClauseSequent.single A)) :=
            gcnf_soundness _ hLeftProv
          -- Auxiliary: Gamma_C ∪ {A} = Gamma1 ∪ {A} ∪ {B'} (= Gamma1 ∪ {A, B'}).
          -- We reformulate: if Gamma1 ∪ {A} is sat by v_A and Gamma1 ∪ {B'} is sat by v_B',
          -- combine via Horn intersection to get Gamma_C ∪ {A} sat, contradicting validity.
          have hValidOneGoal : ClauseSequent.isValid (Finset.union Gamma1 (ClauseSequent.single A))
              ∨ ClauseSequent.isValid (Finset.union Gamma1 (ClauseSequent.single B')) := by
            apply Classical.byContradiction
            intro hNeither
            -- Neither is valid: both are satisfiable.
            have hNotA : ¬ ClauseSequent.isValid (Finset.union Gamma1 (ClauseSequent.single A)) :=
              fun h => hNeither (Or.inl h)
            have hNotB' : ¬ ClauseSequent.isValid (Finset.union Gamma1 (ClauseSequent.single B')) :=
              fun h => hNeither (Or.inr h)
            -- Build satisfiers.
            have hSatA : ∃ v, ClauseSequent.satisfiedBy (Finset.union Gamma1
                (ClauseSequent.single A)) v := Classical.byContradiction fun h => hNotA h
            have hSatB' : ∃ v, ClauseSequent.satisfiedBy (Finset.union Gamma1
                (ClauseSequent.single B')) v := Classical.byContradiction fun h => hNotB' h
            obtain ⟨vA, hvA⟩ := hSatA
            obtain ⟨vB, hvB⟩ := hSatB'
            -- Use horn_all_goals_sat_of_each_sat with goals = [A, B'].
            have hEach : ∀ i : Fin [A, B'].length, ∃ v : Nat → Bool,
                ClauseSequent.satisfiedBy Gamma1 v ∧ Clause.satisfiedBy ([A, B'].get i) v := by
              intro ⟨i, hi⟩
              match i, hi with
              | 0, _ =>
                exact ⟨vA, fun D hD => hvA D ((Finset.mem_union_exp _ _ _).mpr (Or.inl hD)),
                  hvA A ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_csingle A A).mpr rfl)))⟩
              | 1, _ =>
                exact ⟨vB, fun D hD => hvB D ((Finset.mem_union_exp _ _ _).mpr (Or.inl hD)),
                  hvB B' ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_csingle B' B').mpr rfl)))⟩
            have hGoalsList : ∀ C_ ∈ [A, B'], isGoalClause C_ := by
              intro C_ hC_
              rw [List.mem_cons] at hC_
              rcases hC_ with rfl | hC1
              · exact hGoalA
              · rw [List.mem_singleton] at hC1; rw [hC1]; exact hGoalB'
            obtain ⟨vW, hvWG1, hvWgoals⟩ := horn_all_goals_sat_of_each_sat Gamma1 [A, B']
              hGamma1_as_JD hGoalsList (by simp) hEach
            -- vW satisfies Gamma1 and both A, B'. So vW satisfies Gamma_C ∪ {A}.
            exact hLeftProv_valid ⟨vW, fun D hD => by
              rw [Finset.mem_union_exp] at hD
              rcases hD with hDGamma_C | hDA
              · have ⟨hDS', hDneC⟩ := (Finset.mem_erase _ _ _).mp hDGamma_C
                by_cases hDB'' : D = B'
                · rw [hDB'']
                  exact hvWgoals B' (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
                · exact hvWG1 D ((Finset.mem_erase _ _ _).mpr ⟨hDGamma_C, hDB''⟩)
              · rw [(mem_csingle D A).mp hDA]
                exact hvWgoals A (List.mem_cons.mpr (Or.inl rfl))⟩
          -- Non-emptiness of clauses in Gamma1 ∪ {A} (Gamma1 definite → pos literal → non-empty).
          have hLeftNe : ∀ D ∈ Finset.union Gamma1 (ClauseSequent.single A),
              D ≠ Clause.empty := by
            intro D hD hDeq
            rw [Finset.mem_union_exp] at hD
            rcases hD with hDG1 | hDA
            · obtain ⟨_, P, hP⟩ := hGamma1Def D hDG1
              have : Literal.pos P ∈ Clause.empty := hDeq ▸ hP
              exact (Finset.mem_empty _).mp this
            · rw [(mem_csingle D A).mp hDA] at hDeq; exact hAne hDeq
          -- Non-emptiness for Gamma1 ∪ {B'} (= Gamma_C, since B' ∈ Gamma_C):
          have hBothNe : ∀ D ∈ Finset.union Gamma1 (ClauseSequent.single B'),
              D ≠ Clause.empty := by
            intro D hD hDeq
            rw [Finset.mem_union_exp] at hD
            rcases hD with hDG1 | hDB'
            · obtain ⟨_, P, hP⟩ := hGamma1Def D hDG1
              have : Literal.pos P ∈ Clause.empty := hDeq ▸ hP
              exact (Finset.mem_empty _).mp this
            · rw [(mem_csingle D B').mp hDB'] at hDeq; exact hBne' hDeq
          -- Helper: Gamma1 ∪ {B'} = Gamma_C.
          have hG1B'_eq_Gamma_C : Finset.union Gamma1 (ClauseSequent.single B') = Gamma_C := by
            apply Finset.ext; intro D
            rw [Finset.mem_union_exp, mem_csingle]
            constructor
            · intro hD
              rcases hD with hDG1 | rfl
              · exact ((Finset.mem_erase _ _ _).mp hDG1).1
              · exact hB'_in_Gamma_C
            · intro hD
              by_cases hDB'' : D = B'
              · exact Or.inr hDB''
              · exact Or.inl ((Finset.mem_erase _ _ _).mpr ⟨hD, hDB''⟩)
          -- Case split on hValidOneGoal.
          rcases hValidOneGoal with hLeftValid | hRightValid
          · -- Case α: Gamma1 ∪ {A} is valid → provable → IH gives SLD tree → rule-tree construction.
            -- Left sequent is provable via gcnf_completeness (Lem 4.2.1).
            have hLeftProv' : GCNFProvable (Finset.union Gamma1 (ClauseSequent.single A)) :=
              (gcnf_completeness _ hLeftValid hLeftNe).1
            -- Exact cancellation pair; only the selected goal remains in its context.
            let rightTree : GCNFProofTree (Finset.union
                (ClauseSequent.single (Clause.single (Literal.neg Q)))
                (ClauseSequent.single (Clause.single (Literal.pos Q)))) :=
              GCNFProofTree.axiom_ _
                (ClauseSequent.ordinary_union
                  (ClauseSequent.ordinary_single (Clause.single_ordinary _))
                  (ClauseSequent.ordinary_single (Clause.single_ordinary _)))
                ⟨Q, Finset.mem_union.mpr (Or.inr ((mem_csingle _ _).mpr rfl)),
                  Finset.mem_union.mpr (Or.inl ((mem_csingle _ _).mpr rfl))⟩
            have hRightSLD : isSLDForm rightTree := trivial
            have hRightExact : isAxiomNodeWith Q rightTree := by
              change Finset.union (ClauseSequent.single (Clause.single (Literal.neg Q)))
                (ClauseSequent.single (Clause.single (Literal.pos Q))) = pairSet Q
              apply Finset.ext; intro D
              simp [ClauseSequent.single, pairSet, Finset.mem_union, Finset.mem_ofList,
                Finset.mem_singleton, or_comm]
            have hGammaCOrd : Gamma_C.isOrdinary := by
              obtain ⟨T⟩ := hProv'
              exact ClauseSequent.ordinary_subset T.ordinary
                (fun D hD => ((Finset.mem_erase _ _ _).mp hD).1)
            -- Measure decrease for left subtree.
            have hLeftMeasure : totalLits (Finset.union Gamma1 (ClauseSequent.single A))
                < totalLits S' := by
              have hInsertEq : Finset.union Gamma1 (ClauseSequent.single A) =
                  Finset.insert A ((S'.erase C).erase B') := by
                show Finset.union (Gamma_C.erase B') (ClauseSequent.single A) = _
                apply Finset.ext; intro x
                rw [Finset.mem_union_exp, Finset.mem_insert_exp, mem_csingle]
                exact ⟨fun h => h.symm.imp id id, fun h => h.symm.imp id id⟩
              rw [hInsertEq]
              have h1 := totalLits_insert ((S'.erase C).erase B') A hA_nmem_Gamma1
              have h2 := totalLits_erase_add (S'.erase C) B' (by
                show B' ∈ S'.erase C
                exact (Finset.mem_erase _ _ _).mpr ⟨hB', fun heq => hCneB' heq.symm⟩)
              have h3 := totalLits_erase_add S' C hCS'
              have hB'card : B'.card = 1 := hB'card1
              rw [h1]
              have hAcard_ge1 : A.card ≥ 1 := by
                obtain ⟨L, hL⟩ : ∃ L, L ∈ A := by
                  apply Classical.byContradiction; intro hNo
                  apply hAne; apply Finset.ext; intro x
                  exact ⟨fun hx => (hNo ⟨x, hx⟩).elim,
                         fun hx => ((Finset.mem_empty x).mp hx).elim⟩
                cases hAmk : A with | mk v nd =>
                induction v using LCS.Multiset.ind with
                | _ l =>
                  have hLl : L ∈ l := by
                    have : L ∈ A := hL
                    rw [hAmk] at this; exact this
                  show 1 ≤ l.length
                  cases hv : l with
                  | nil => rw [hv] at hLl; exact absurd hLl List.not_mem_nil
                  | cons _ _ => simp [List.length]
              omega
            -- Apply IH to the left subtree.
            obtain ⟨leftTree, hLeftSLD⟩ := ih
              (totalLits (Finset.union Gamma1 (ClauseSequent.single A)))
              (Nat.lt_of_lt_of_le hLeftMeasure hMeasure)
              (Finset.union Gamma1 (ClauseSequent.single A))
              (fun D hD => by
                rw [Finset.mem_union_exp] at hD
                rcases hD with hDG1 | hDA
                · exact Or.inl (hGamma1Def D hDG1)
                · rw [mem_csingle] at hDA; subst hDA; exact Or.inr hGoalA)
              A
              ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_csingle A A).mpr rfl)))
              hGoalA hAne
              (fun D hD hGC => by
                rw [Finset.mem_union_exp] at hD
                rcases hD with hDG1 | hDA
                · obtain ⟨_, P, hP⟩ := hGamma1Def D hDG1
                  have := hGC.2 (Literal.pos P) hP
                  exact absurd this (by simp)
                · rw [mem_csingle] at hDA; exact hDA)
              hLeftProv'
              (Nat.le_refl _)
            -- Construct S' tree via rule constructor with B = pos Q, As = Cs = {A},
            -- Gamma = Gamma_C, Gamma1 = Gamma_C.erase B', Gamma2 = {{neg Q}}.
            have hCsNonempty : ∃ D, D ∈ ClauseSequent.single A :=
              ⟨A, (mem_csingle A A).mpr rfl⟩
            have hCsSubClaus : LCS.Finset.Subset (ClauseSequent.single A)
                (ClauseSequent.single A) := fun _ h => h
            have hG1Sub : LCS.Finset.Subset Gamma1
                (Finset.union Gamma_C (ClauseSequent.mapSet (ClauseSequent.single A)
                  (fun X => clauseWithLiteral X (Literal.pos Q)))) := by
              intro D hD
              have ⟨hDG_C, _⟩ := (Finset.mem_erase _ _ _).mp hD
              exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hDG_C)
            have hG2Sub : LCS.Finset.Subset
                (ClauseSequent.single (Clause.single (Literal.neg Q)))
                (Finset.union Gamma_C (ClauseSequent.mapSet (ClauseSequent.single A)
                  (fun X => clauseWithLiteral X (Literal.pos Q)))) := by
              intro D hD
              rw [(mem_csingle _ _).mp hD]
              exact Finset.mem_union.mpr (Or.inl (hB'eq ▸ hB'_in_Gamma_C))
            rw [hS'_eq_rule]
            refine ⟨GCNFProofTree.rule Gamma_C (ClauseSequent.single A) (Literal.pos Q)
                (ClauseSequent.single A) Gamma1
                (ClauseSequent.single (Clause.single (Literal.neg Q))) hGammaCOrd
                (ordinary_right leftTree) leftTree rightTree
                hCsNonempty hCsSubClaus hG1Sub hG2Sub, ?_⟩
            show isSLDForm _
            unfold isSLDForm
            refine ⟨hLeftSLD, hRightSLD, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
            · intro D hD l hl
              rw [mem_csingle] at hD; subst hD
              obtain ⟨R, hR⟩ := hAallNeg l hl
              rw [hR]; trivial
            · exact hRightExact
            · exact hB'eq ▸ hB'_in_Gamma_C
            · intro hMem
              exact ((Finset.mem_erase _ _ _).mp hMem).2 hB'eq.symm
            · refine ⟨A, (mem_csingle A A).mpr rfl, hGoalA, ?_⟩
              intro D hD hGC
              rw [Finset.mem_union_exp] at hD
              rcases hD with hDG1 | hDA
              · obtain ⟨_, P, hP⟩ := hGamma1Def D hDG1
                have := hGC.2 (Literal.pos P) hP
                exact absurd this (by simp)
              · rw [mem_csingle] at hDA; exact hDA
          · -- Case β: Gamma_C is valid (= Gamma1 ∪ {B'}) → apply IH on Gamma_C and
            -- lift the resulting SLD-form tree to S' via definite-clause weakening.
            -- Gamma_C = Gamma1 ∪ {B'}, so hRightValid : Gamma1 ∪ {B'} valid.
            rw [hG1B'_eq_Gamma_C] at hRightValid hBothNe
            -- Gamma_C provable via gcnf_completeness.
            have hGamma_C_prov : GCNFProvable Gamma_C :=
              (gcnf_completeness _ hRightValid hBothNe).1
            -- Measure decrease for Gamma_C.
            have hGamma_C_measure : totalLits Gamma_C < totalLits S' := by
              show totalLits (S'.erase C) < totalLits S'
              have h3 := totalLits_erase_add S' C hCS'
              have hCge2 : C.card ≥ 2 := by
                have hAcard_ge1 : A.card ≥ 1 := by
                  obtain ⟨L, hL⟩ : ∃ L, L ∈ A := by
                    apply Classical.byContradiction; intro hNo
                    apply hAne; apply Finset.ext; intro x
                    exact ⟨fun hx => (hNo ⟨x, hx⟩).elim,
                           fun hx => ((Finset.mem_empty x).mp hx).elim⟩
                  cases hAmk : A with | mk v nd =>
                  induction v using LCS.Multiset.ind with
                  | _ l =>
                    have hLl : L ∈ l := by
                      have : L ∈ A := hL
                      rw [hAmk] at this; exact this
                    show 1 ≤ l.length
                    cases hv : l with
                    | nil => rw [hv] at hLl; exact absurd hLl List.not_mem_nil
                    | cons _ _ => simp [List.length]
                omega
              omega
            -- Apply IH on Gamma_C (smaller totalLits). Gamma_C has hGammaDef
            -- (all definite except B' = {¬Q} which is the unique goal).
            have hDef_Gamma_C : ∀ D ∈ Gamma_C, isDefiniteClause D ∨ isGoalClause D := by
              intro D hD
              by_cases hDB' : D = B'
              · subst hDB'; exact Or.inr hGoalB'
              · have ⟨hDS', _⟩ := (Finset.mem_erase _ _ _).mp hD
                exact Or.inl (hGammaDef D ((Finset.mem_erase _ _ _).mpr ⟨hDS', hDB'⟩))
            have hUnique_Gamma_C : ∀ D ∈ Gamma_C, isGoalClause D → D = B' := by
              intro D hD hGC
              by_cases hDB' : D = B'
              · exact hDB'
              · have ⟨hDS', _⟩ := (Finset.mem_erase _ _ _).mp hD
                have := hGammaDef D ((Finset.mem_erase _ _ _).mpr ⟨hDS', hDB'⟩)
                obtain ⟨_, P, hP⟩ := this
                have := hGC.2 (Literal.pos P) hP
                exact absurd this (by simp)
            obtain ⟨T_GammaC, hT_GammaC_SLD⟩ := ih (totalLits Gamma_C)
              (Nat.lt_of_lt_of_le hGamma_C_measure hMeasure)
              Gamma_C hDef_Gamma_C B' hB'_in_Gamma_C hGoalB' hBne' hUnique_Gamma_C
              hGamma_C_prov (Nat.le_refl _)
            -- Lift T_GammaC to S' via SLD-preserving weakening by definite clause C.
            -- Re-derive C.card ≥ 2 (available earlier as hCge2 inside the measure
            -- `have`; redo it here since that scope was closed). C =
            -- clauseWithLiteral A (pos Q) = insert (pos Q) A where A is nonempty,
            -- so C.card = A.card + 1 ≥ 2 via hAcard + A.card ≥ 1.
            have hCge2' : C.card ≥ 2 := by
              have hAcard_ge1 : A.card ≥ 1 := by
                obtain ⟨L, hL⟩ : ∃ L, L ∈ A := by
                  apply Classical.byContradiction; intro hNo
                  apply hAne; apply Finset.ext; intro x
                  exact ⟨fun hx => (hNo ⟨x, hx⟩).elim,
                         fun hx => ((Finset.mem_empty x).mp hx).elim⟩
                cases hAmk : A with | mk v nd =>
                induction v using LCS.Multiset.ind with
                | _ l =>
                  have hLl : L ∈ l := by
                    have : L ∈ A := hL
                    rw [hAmk] at this; exact this
                  show 1 ≤ l.length
                  cases hv : l with
                  | nil => rw [hv] at hLl; exact absurd hLl List.not_mem_nil
                  | cons _ _ => simp [List.length]
              omega
            obtain ⟨T_S', hT_S'_SLD⟩ :=
              isSLDForm_weaken_by_definite Gamma_C T_GammaC hT_GammaC_SLD C hCDef hCge2'
            -- T_S' has type GCNFProofTree (insert C Gamma_C) = GCNFProofTree S'.
            have hS'_eq : Finset.insert C Gamma_C = S' := by
              show Finset.insert C (S'.erase C) = S'
              apply Finset.ext; intro x
              rw [Finset.mem_insert_exp, Finset.mem_erase]
              constructor
              · intro h
                rcases h with rfl | ⟨hx, _⟩
                · exact hCS'
                · exact hx
              · intro hx
                by_cases hxC : x = C
                · exact Or.inl hxC
                · exact Or.inr ⟨hx, hxC⟩
            -- Use Eq.rec transport: given hS'_eq : insert C Gamma_C = S', convert
            -- T_S' : GCNFProofTree (insert C Gamma_C) to GCNFProofTree S'.
            have hEquivSLD : ∀ {U V : ClauseSequent} (hUV : U = V)
                (T_U : GCNFProofTree U), isSLDForm T_U → isSLDForm (hUV ▸ T_U) := by
              intro U V hUV T_U hT_U
              cases hUV; exact hT_U
            exact ⟨hS'_eq ▸ T_S', hEquivSLD hS'_eq T_S' hT_S'_SLD⟩


proof_of sld_form_completeness_multiple_goals := by
  -- BEGIN PROOF
    -- Step 1: Apply goal_reduction (Lemma 9.2.5) Part (a) to get some i
    -- with GCNFProvable (J ∪ defs ∪ {goals.get i})
    let JD := Finset.union J (ClauseSequent.ofList defs)
    obtain ⟨⟨i, hProvI⟩, _⟩ := goal_reduction J goals defs hJ hGoals hGoalsNe hDefs S hS hProv
    -- Step 2: Apply sld_form_completeness (Theorem 9.2.1) to the single-goal set
    let Si := Finset.union JD (ClauseSequent.single (goals.get i))
    have hDefSi : ∀ C ∈ Si, isDefiniteClause C ∨ isGoalClause C := by
      intro C hC
      rw [Finset.mem_union] at hC
      rcases hC with hCJD | hCSing
      · rw [Finset.mem_union] at hCJD
        rcases hCJD with hCJ | hCD
        · obtain ⟨P, rfl⟩ := hJ C hCJ
          left; constructor
          · exact isHornClause_single (Literal.pos P)
          · exact ⟨P, (Finset.mem_singleton _ _).mpr rfl⟩
        · exact Or.inl (hDefs C ((Finset.mem_ofList_exp _ _).mp hCD)).1
      · right
        have hCeq := (Finset.mem_singleton C _).mp hCSing
        rw [hCeq]
        exact hGoals _ (List.get_mem goals i)
    have hBmem : goals.get i ∈ Si :=
      (Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
    have hGoalB : isGoalClause (goals.get i) := hGoals _ (List.get_mem goals i)
    have hBne : goals.get i ≠ Clause.empty := hGoalsNonempty _ (List.get_mem goals i)
    have hUnique : ∀ C ∈ Si, isGoalClause C → C = goals.get i := by
      intro C hC hGC
      rw [Finset.mem_union] at hC
      rcases hC with hCJD | hCSing
      · rw [Finset.mem_union] at hCJD
        rcases hCJD with hCJ | hCD
        · obtain ⟨P, rfl⟩ := hJ C hCJ
          exact absurd (hGC.2 (Literal.pos P) ((Finset.mem_singleton _ _).mpr rfl)) (by simp)
        · obtain ⟨⟨_, ⟨P, hP⟩⟩, _⟩ := hDefs C ((Finset.mem_ofList_exp _ _).mp hCD)
          exact absurd (hGC.2 (Literal.pos P) hP) (by simp)
      · exact (Finset.mem_singleton C _).mp hCSing
    obtain ⟨T, hSLD⟩ := sld_form_completeness Si hDefSi (goals.get i) hBmem hGoalB hBne hUnique hProvI
    exact ⟨i, T, hSLD⟩


end LCS.SLD.SLDForm.Completeness

end
