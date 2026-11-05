import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import Attach
import LCS.SLD.SLDForm.Completeness.OccurrenceNormalization.ProofsStamp

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.RootPartition
/-- Literal-only sequents satisfy the GCNF' clause grammar. -/
theorem ordinary_of_singletons {S : ClauseSequent}
    (h : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L) : S.isOrdinary := by
  intro C hC
  obtain ⟨L, rfl⟩ := h C hC
  exact Clause.single_ordinary L

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A premise certifies ordinariness of each half of its context. -/
theorem ordinary_left {G A : ClauseSequent} (T : GCNFProofTree (Finset.union G A)) :
    G.isOrdinary :=
  ClauseSequent.ordinary_subset T.ordinary (fun _ h => Finset.mem_union.mpr (Or.inl h))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem ordinary_right {G A : ClauseSequent} (T : GCNFProofTree (Finset.union G A)) :
    A.isOrdinary :=
  ClauseSequent.ordinary_subset T.ordinary (fun _ h => Finset.mem_union.mpr (Or.inr h))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- A positive literal witnesses nonemptiness of a definite clause. -/
theorem ordinary_of_definite {C : Clause} (h : isDefiniteClause C) : C.isOrdinary := by
  obtain ⟨P, hP⟩ := h.2
  exact Clause.ordinary_of_mem hP

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
theorem ordinary_insert {D : Clause} {S : ClauseSequent}
    (hD : D.isOrdinary) (hS : S.isOrdinary) : ClauseSequent.isOrdinary (Finset.insert D S) := by
  intro C hC
  rcases Finset.mem_insert.mp hC with rfl | hC
  · exact hD
  · exact hS C hC

-- ========= totalLits measure (Phase A4-sub1 infrastructure) =========
--
-- For the main step of Thm 9.2.1 we need a strictly decreasing measure
-- on `ClauseSequent`s whose decrease is justified by replacing one clause
-- with a strictly smaller one. `totalLits S` is the sum over `S` of each
-- clause's literal count. Because `ClauseSequent = LCS.Finset Clause` is a
-- quotient of lists under permutation, we first lift `List.sum ∘ List.map`
-- through `List.Perm`.

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Permutation preserves `List.sum` on `Nat` lists. Used to lift summation
    through the quotient `LCS.Multiset = Quotient List.isSetoid`. -/
theorem listPerm_sum_eq {l1 l2 : List Nat} (h : l1.Perm l2) :
    l1.sum = l2.sum := by
-- BEGIN PROOF
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap => simp [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Generic `Nat`-valued sum over an `LCS.Finset`, parameterised by a weight
    function `f`. Defined by quotient lift of `List.map f |>.sum`. -/
def finsetSum {α : Type} (s : LCS.Finset α) (f : α → Nat) : Nat :=
  Quot.liftOn s.val (fun l => (l.map f).sum)
    (fun _ _ hp => listPerm_sum_eq (hp.map f))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Total literal count of a `ClauseSequent`: sum over `S` of each clause's
    `card`. This is the termination measure for the inductive construction
    in Thm 9.2.1 (replace an oversized clause by a strictly smaller one). -/
def totalLits (S : ClauseSequent) : Nat := finsetSum S (fun C => C.card)

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Delta lemma: inserting a fresh clause adds its cardinality to `totalLits`. -/
theorem totalLits_insert (S : ClauseSequent) (C : Clause) (hC : C ∉ S) :
    totalLits (Finset.insert C S) = totalLits S + C.card := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hC
  induction v using LCS.Multiset.ind with
  | _ l =>
    intro nd hC
    have hCl : C ∉ l := hC
    show ((if C ∈ l then l else C :: l).map (fun D => D.card)).sum
        = (l.map (fun D => D.card)).sum + C.card
    simp [hCl, List.sum_cons]; omega



-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Delta lemma: erasing a present clause decreases `totalLits` by its
    cardinality. Stated in additive form to avoid `Nat` truncated subtraction. -/
theorem totalLits_erase_add (S : ClauseSequent) (C : Clause) (hC : C ∈ S) :
    totalLits (S.erase C) + C.card = totalLits S := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hC
  induction v using LCS.Multiset.ind with
  | _ l =>
    intro nd hC
    have hCl : C ∈ l := hC
    show ((l.erase C).map (fun D => D.card)).sum + C.card
        = (l.map (fun D => D.card)).sum
    have hp : l.Perm (C :: l.erase C) := List.perm_cons_erase hCl
    have hmp : (l.map (fun D => D.card)).Perm ((C :: l.erase C).map (fun D => D.card)) :=
      hp.map (fun D => D.card)
    have hsum := listPerm_sum_eq hmp
    simp [List.sum_cons] at hsum
    omega



-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Main delta lemma: replacing a clause `C ∈ S` by a strictly smaller clause
    `C'` (absent from `S.erase C`) strictly decreases `totalLits`. This is the
    termination argument for the Thm 9.2.1 main step. -/
theorem totalLits_replace_with_smaller
    (S : ClauseSequent) (C C' : Clause)
    (hC : C ∈ S) (hC' : C' ∉ S.erase C) (hLt : C'.card < C.card) :
    totalLits (Finset.insert C' (S.erase C)) < totalLits S := by
-- BEGIN PROOF
  have h1 := totalLits_insert (S.erase C) C' hC'
  have h2 := totalLits_erase_add S C hC
  rw [h1]; omega

-- ========= Helper lemmas for Horn clause reasoning =========

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- An ordinary subset of an ordinary Horn clause is Horn. -/
theorem isHornClause_of_subset (C D : Clause) (hHorn : isHornClause C)
    (hSub : ∀ l ∈ D, l ∈ C) (hD : D.isOrdinary) : isHornClause D :=
  ⟨hD, fun P Q hP hQ => hHorn.2 P Q (hSub _ hP) (hSub _ hQ)⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- If cwl A (pos Q) is Horn and pos R ∈ A, then R = Q. -/
theorem horn_cwl_pos_unique (A : Clause) (Q R : Nat)
    (hHorn : isHornClause (clauseWithLiteral A (Literal.pos Q)))
    (hR : Literal.pos R ∈ A) : R = Q :=
-- BEGIN PROOF
  hHorn.2 R Q
    ((Finset.mem_insert_exp (Literal.pos Q) (Literal.pos R) A).mpr (Or.inr hR))
    ((Finset.mem_insert_exp (Literal.pos Q) (Literal.pos Q) A).mpr (Or.inl rfl))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Singleton clause equality implies literal equality. -/
theorem single_eq_implies_lit_eq (L B : Literal) (h : Clause.single L = Clause.single B) : L = B := by
-- BEGIN PROOF
  have hL : L ∈ Clause.single B := h ▸ (Finset.mem_singleton L L).mpr rfl
  exact (Finset.mem_singleton L B).mp hL

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton clause is Horn. -/
theorem isHornClause_single (L : Literal) : isHornClause (Clause.single L) := by
-- BEGIN PROOF
  refine ⟨Clause.single_ordinary _, ?_⟩
  intro P Q hP hQ
  have hP' := (Finset.mem_singleton (Literal.pos P) L).mp hP
  have hQ' := (Finset.mem_singleton (Literal.pos Q) L).mp hQ
  cases L with
  | pos n => injection hP' with hp; injection hQ' with hq; rw [hp, hq]
  | neg n => exact absurd hP' (by intro h; exact Literal.noConfusion h)

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- By induction on the proof tree: any GCNFProofTree for a set of Horn clauses
    has a positive unit clause in its conclusion. -/
theorem gcnf_tree_has_pos_unit {S : ClauseSequent}
    (T : GCNFProofTree S)
    (hHorn : ∀ C ∈ S, isHornClause C) :
    ∃ P : Nat, Clause.single (Literal.pos P) ∈ S := by
-- BEGIN PROOF
  induction T with
  | axiom_ S hOrd hTriv => exact ⟨hTriv.choose, hTriv.choose_spec.1⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGammaOrd hAsOrd leftTree rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
    have hHornRight : ∀ C ∈ Finset.union Gamma2 (ClauseSequent.single (Clause.single B)), isHornClause C := by
      intro C hC; rw [Finset.mem_union] at hC
      rcases hC with hG2 | hSing
      · exact hHorn C (hG2Sub C hG2)
      · rw [mem_csingle] at hSing; rw [hSing]; exact isHornClause_single B
    obtain ⟨Q, hQ⟩ := ihR hHornRight
    rw [Finset.mem_union] at hQ
    rcases hQ with hQG2 | hQSing
    · exact ⟨Q, hG2Sub _ hQG2⟩
    · rw [mem_csingle] at hQSing
      have hLit : Literal.pos Q = B := single_eq_implies_lit_eq (Literal.pos Q) B hQSing
      have hHornLeft : ∀ C ∈ Finset.union Gamma1 Cs, isHornClause C := by
        intro C hC; rw [Finset.mem_union] at hC
        rcases hC with hG1 | hCs
        · exact hHorn C (hG1Sub C hG1)
        · exact isHornClause_of_subset (clauseWithLiteral C B) C
            (hHorn _ ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCsSub C hCs, rfl⟩))))
            (fun l hl => (Finset.mem_insert_exp B l C).mpr (Or.inr hl))
            (hAsOrd C (hCsSub C hCs))
      obtain ⟨R, hR⟩ := ihL hHornLeft
      rw [Finset.mem_union] at hR
      rcases hR with hRG1 | hRCs
      · exact ⟨R, hG1Sub _ hRG1⟩
      · have hRAs := hCsSub _ hRCs
        have hCwl_in : clauseWithLiteral (Clause.single (Literal.pos R)) B ∈
            Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
          (Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr
            ⟨Clause.single (Literal.pos R), hRAs, rfl⟩))
        have hH := hHorn _ hCwl_in
        have hReqQ : R = Q := by
          rw [← hLit] at hH
          exact horn_cwl_pos_unique (Clause.single (Literal.pos R)) Q R hH
            ((Finset.mem_singleton _ _).mpr rfl)
        rw [hReqQ] at hCwl_in
        have hSimp : clauseWithLiteral (Clause.single (Literal.pos Q)) B =
            Clause.single (Literal.pos Q) := by
          rw [← hLit]; exact clauseWithLiteral_single_self _
        rw [hSimp] at hCwl_in
        exact ⟨Q, hCwl_in⟩

-- ========= Definition 9.2.3: GCNF'-proof without weakenings =========

/-- Definition 9.2.3: A GCNF'-proof is without weakenings iff every application
    of the lor:left rule uses the shared context Gamma with no extra formulae. -/
@[blueprint "chap9__definition_9_2_3" (main := true)]
def IsWithoutWeakenings : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ hOrd _ => True
  | _, .rule Gamma As _B Cs Gamma1 Gamma2 hGammaOrd hAsOrd leftTree rightTree _hNe _hSub _ _ =>
    Cs = As ∧ Gamma1 = Gamma ∧ Gamma2 = Gamma ∧
    IsWithoutWeakenings leftTree ∧
    IsWithoutWeakenings rightTree

/-- Definition 9.2.3 (compatibility alias): the former `IsStrictIWW` name now
    denotes exactly the textbook's weakening-free condition. -/
@[blueprint "chap9__definition_9_2_3"]
abbrev IsStrictIWW {S : ClauseSequent} (T : GCNFProofTree S) : Prop :=
  IsWithoutWeakenings T

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- A genuine literal-B decomposition removes the pivot from every residual
    clause and removes the selected principal clauses from the context. These
    standing GCNF' conventions are checked at every rule node, independently
    of the weakening-free context equalities. -/
@[blueprint "chap9__lemma_9_2_3"]
def GenuineDecompositions : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _ _ => True
  | _, .rule Gamma As B _ _ _ _ _ left right _ _ _ _ =>
      (∀ A ∈ As, B ∉ A) ∧
      (∀ A ∈ As, clauseWithLiteral A B ∉ Gamma) ∧
      GenuineDecompositions left ∧ GenuineDecompositions right



-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- The local singleton/no-weakening shape exported by occurrence compression
    implies the textbook's general no-weakening condition. -/
theorem isWithoutWeakenings_of_isUnaryOccurrenceCompression :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    IsUnaryOccurrenceCompression T →
    IsWithoutWeakenings T
  | _, .axiom_ _ hOrd _, _ => trivial
  | _, .rule _ As _ Cs _ _ hGammaOrd hAsOrd left right _ _ _ _, hShape => by
      rcases hShape with
        ⟨⟨A, hAs, hCs⟩, hGamma1, hGamma2, hLeft, hRight⟩
      exact
        ⟨hCs.trans hAs.symm, hGamma1, hGamma2,
          isWithoutWeakenings_of_isUnaryOccurrenceCompression left hLeft,
          isWithoutWeakenings_of_isUnaryOccurrenceCompression right hRight⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Regression: equality `Cs = As` alone is insufficient. A rule whose left
    premise changes the shared context cannot be weakening-free. -/
theorem isWithoutWeakenings_rejects_changed_left_context
    (Gamma As : ClauseSequent) (B : Literal)
    (Gamma1 Gamma2 : ClauseSequent)
    (leftTree : GCNFProofTree (Finset.union Gamma1 As))
    (rightTree : GCNFProofTree
      (Finset.union Gamma2 (ClauseSequent.single (Clause.single B))))
    (hAsNonempty : ∃ C, C ∈ As)
    (hG1Sub : Finset.Subset Gamma1
      (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))))
    (hG2Sub : Finset.Subset Gamma2
      (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))))
    (hChanged : Gamma1 ≠ Gamma) (hGammaOrd : Gamma.isOrdinary) :
    ¬ IsWithoutWeakenings
      (.rule Gamma As B As Gamma1 Gamma2 hGammaOrd (ordinary_right leftTree) leftTree rightTree
        hAsNonempty (fun _ h => h) hG1Sub hG2Sub) := by
  intro h
  exact hChanged h.2.1

-- ATTACH-BLOCKER: unsupported untagged example
/-- Concrete regression for the former `Cs = As`-only body. Both children are
    exact-pair axioms and `Cs = As`, but the rule drops the extra `pos 1`
    context clause, so the repaired predicate rejects it. -/
example : ∃ (S : ClauseSequent) (T : GCNFProofTree S),
    ¬ IsWithoutWeakenings T := by
  let base : ClauseSequent := pairSet 0
  let unitPos : Clause := Clause.single (Literal.pos 0)
  let extra : Clause := Clause.single (Literal.pos 1)
  let As : ClauseSequent := ClauseSequent.single unitPos
  let Gamma : ClauseSequent := Finset.insert extra base
  have hAbsorb : Finset.union base As = base := by
    apply Finset.ext
    intro C
    rw [Finset.mem_union]
    constructor
    · rintro (hBase | hAs)
      · exact hBase
      · have hEq : C = unitPos := (mem_csingle C unitPos).mp hAs
        rw [hEq]
        exact (Finset.mem_ofList_exp unitPos
          [Clause.single (Literal.pos 0), Clause.single (Literal.neg 0)]).mpr
          (List.mem_cons.mpr (Or.inl rfl))
    · exact Or.inl
  let premTree : GCNFProofTree (Finset.union base As) :=
    Eq.mpr (congrArg GCNFProofTree hAbsorb) (pairAxiom 0)
  have hBaseSub : Finset.Subset base
      (Finset.union Gamma
        (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos 0)))) := by
    intro C hC
    exact (Finset.mem_union_exp C Gamma _).mpr
      (Or.inl ((Finset.mem_insert_exp extra C base).mpr (Or.inr hC)))
  have hChanged : base ≠ Gamma := by
    intro hEq
    have hExtraGamma : extra ∈ Gamma :=
      (Finset.mem_insert_exp extra extra base).mpr (Or.inl rfl)
    have hExtraBase : extra ∈ base := by
      rw [hEq]
      exact hExtraGamma
    change Clause.single (Literal.pos 1) ∈ pairSet 0 at hExtraBase
    unfold pairSet at hExtraBase
    rw [Finset.mem_ofList] at hExtraBase
    rcases List.mem_cons.mp hExtraBase with hPos | hTail
    · have hLit := single_eq_implies_lit_eq _ _ hPos
      injection hLit with hNat
      omega
    · have hNeg := List.mem_singleton.mp hTail
      have hLit := single_eq_implies_lit_eq _ _ hNeg
      exact Literal.noConfusion hLit
  let T := GCNFProofTree.rule Gamma As (Literal.pos 0) As base base
    (by simp [Gamma, extra, base, pairSet, ClauseSequent.isOrdinary, Finset.mem_insert, Finset.mem_ofList])
    (ordinary_right premTree) premTree premTree
    ⟨unitPos, (Finset.mem_singleton unitPos unitPos).mpr rfl⟩
    (fun _ h => h) hBaseSub hBaseSub
  refine ⟨_, T, ?_⟩
  exact isWithoutWeakenings_rejects_changed_left_context
    Gamma As (Literal.pos 0) base base premTree premTree
    ⟨unitPos, (Finset.mem_singleton unitPos unitPos).mpr rfl⟩
    hBaseSub hBaseSub hChanged
    (by simp [Gamma, extra, base, pairSet, ClauseSequent.isOrdinary, Finset.mem_insert, Finset.mem_ofList])

-- ATTACH-BLOCKER: unsupported untagged example
/-- Concrete regression for the Lemma 9.2.1 axiom contract: a literal-only
    axiom may contain more than the exact complementary pair. -/
example :
    let S := Finset.insert (Clause.single (Literal.pos 1)) (pairSet 0)
    ∃ T : GCNFProofTree S,
      T.axiomsAllSingleLiteral ∧ ¬ T.axiomsMinimal := by
  let S := Finset.insert (Clause.single (Literal.pos 1)) (pairSet 0)
  have hTriv : ClauseSequent.isTrivial S := by
    refine ⟨0, ?_, ?_⟩
    · exact (Finset.mem_insert_exp _ _ _).mpr
        (Or.inr ((Finset.mem_ofList_exp _ _).mpr
          (List.mem_cons.mpr (Or.inl rfl))))
    · exact (Finset.mem_insert_exp _ _ _).mpr
        (Or.inr ((Finset.mem_ofList_exp _ _).mpr
          (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))))
  let T : GCNFProofTree S := .axiom_ S (by simp [S, pairSet, ClauseSequent.isOrdinary, Finset.mem_insert, Finset.mem_ofList]) hTriv
  refine ⟨T, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hBase
    · exact ⟨Literal.pos 1, rfl⟩
    · unfold pairSet at hBase
      rw [Finset.mem_ofList] at hBase
      rcases List.mem_cons.mp hBase with rfl | hTail
      · exact ⟨Literal.pos 0, rfl⟩
      · rw [List.mem_singleton.mp hTail]
        exact ⟨Literal.neg 0, rfl⟩
  · intro hMin
    obtain ⟨P, hEq⟩ := hMin
    have positive_mem_pair_eq :
        ∀ Q P : Nat, Clause.single (Literal.pos Q) ∈ pairSet P → Q = P := by
      intro Q P hMem
      unfold pairSet at hMem
      rw [Finset.mem_ofList] at hMem
      rcases List.mem_cons.mp hMem with hPos | hTail
      · have hLit := single_eq_implies_lit_eq _ _ hPos
        injection hLit
      · have hNeg := List.mem_singleton.mp hTail
        have hLit := single_eq_implies_lit_eq _ _ hNeg
        exact Literal.noConfusion hLit
    have hPos0 : Clause.single (Literal.pos 0) ∈ S :=
      (Finset.mem_insert_exp _ _ _).mpr
        (Or.inr ((Finset.mem_ofList_exp _ _).mpr
          (List.mem_cons.mpr (Or.inl rfl))))
    have hPos1 : Clause.single (Literal.pos 1) ∈ S :=
      (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
    change Clause.single (Literal.pos 0) ∈
      Finset.insert (Clause.single (Literal.pos 1)) (pairSet 0) at hPos0
    change Clause.single (Literal.pos 1) ∈
      Finset.insert (Clause.single (Literal.pos 1)) (pairSet 0) at hPos1
    rw [hEq] at hPos0 hPos1
    have hP0 := positive_mem_pair_eq 0 P hPos0
    have hP1 := positive_mem_pair_eq 1 P hPos1
    omega

-- ATTACH-BLOCKER: unsupported untagged example
/-- The GCNF' carrier rejects a sequent containing the empty clause. -/
example :
    let S := Finset.insert Clause.empty (pairSet 0)
    ¬ GCNFProvable S := by
  dsimp only
  rintro ⟨T⟩
  exact T.ordinary Clause.empty (Finset.mem_insert.mpr (Or.inl rfl)) rfl

-- ========= Helper defs for Lemma 9.2.2: proof depth =========

/-- Lemma 9.2.2 (companion): The depth of a GCNFProofTree, defined as
    the maximum number of rule applications on any root-to-leaf path.
    Axioms have depth 0; the rule node has depth 1 + max of subtrees. -/
@[blueprint "chap9__lemma_9_2_2"]
def proofDepth : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ hOrd _ => 0
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd leftTree rightTree _ _ _ _ =>
    1 + max (proofDepth leftTree) (proofDepth rightTree)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Candidate depth of the ordinary G' inference occurrences represented by a
    compressed GCNF' tree: a simultaneous rule is charged once per member of
    `As`.  This recurrence is sound only together with occurrence provenance;
    the finite-set aliasing regression below proves it is insufficient alone. -/
def expandedDepth : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ hOrd _ => 0
  | _, .rule _ As _ _ _ _ hGammaOrd hAsOrd leftTree rightTree _ _ _ _ =>
    As.card + max (expandedDepth leftTree) (expandedDepth rightTree)







-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Reindex a proof tree along equality of its root sequent.  Naming this
    otherwise invisible transport makes representation regressions readable. -/
def transportGCNFProofTree {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) : GCNFProofTree S' :=
  h ▸ T







-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Shared context for the occurrence-aliasing regression below.  It already
    contains the residual clause selected by the outer simultaneous rule. -/
def expandedDepthAliasGamma : ClauseSequent :=
  ClauseSequent.ofList
    [Clause.single (Literal.pos 1),
      Clause.single (Literal.pos 0),
      Clause.ofList [Literal.neg 0, Literal.neg 1]]

/-- The left premise of the inner rule is the complementary-literal axiom
    `{+1}, {+0}, {-0}`. -/
def expandedDepthAliasLeftAxiom :
    GCNFProofTree
      (Finset.union
        (ClauseSequent.ofList
          [Clause.single (Literal.pos 1), Clause.single (Literal.pos 0)])
        (ClauseSequent.single (Clause.single (Literal.neg 0)))) :=
  .axiom_ _
    (by simp [ClauseSequent.isOrdinary, ClauseSequent.ofList, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton, or_assoc])
    ⟨0,
      by native_decide,
      by native_decide⟩

/-- The right premise of the inner rule is the complementary-literal axiom
    `{+1}, {+0}, {-1}`. -/
def expandedDepthAliasRightAxiom :
    GCNFProofTree
      (Finset.union
        (ClauseSequent.ofList
          [Clause.single (Literal.pos 1), Clause.single (Literal.pos 0)])
        (ClauseSequent.single (Clause.single (Literal.neg 1)))) :=
  .axiom_ _
    (by simp [ClauseSequent.isOrdinary, ClauseSequent.ofList, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton, or_assoc])
    ⟨1,
      by native_decide,
      by native_decide⟩

/-- A one-step weakening-free proof of `expandedDepthAliasGamma`. -/
def expandedDepthAliasInner :
    GCNFProofTree expandedDepthAliasGamma := by
  let Gamma₀ : ClauseSequent :=
    ClauseSequent.ofList
      [Clause.single (Literal.pos 1), Clause.single (Literal.pos 0)]
  let As₀ : ClauseSequent :=
    ClauseSequent.single (Clause.single (Literal.neg 0))
  change GCNFProofTree
    (Finset.union Gamma₀
      (ClauseSequent.mapSet As₀
        (fun A => clauseWithLiteral A (Literal.neg 1))))
  exact .rule Gamma₀ As₀ (Literal.neg 1) As₀ Gamma₀ Gamma₀
    (ordinary_left expandedDepthAliasLeftAxiom) (ordinary_right expandedDepthAliasLeftAxiom)
    expandedDepthAliasLeftAxiom expandedDepthAliasRightAxiom
    ⟨Clause.single (Literal.neg 0), by native_decide⟩
    (fun _ h => h)
    (fun D hD => (Finset.mem_union_exp _ _ _).mpr (Or.inl hD))
    (fun D hD => (Finset.mem_union_exp _ _ _).mpr (Or.inl hD))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The target clause in the outer occurrence-aliasing regression. -/
def expandedDepthAliasTarget : Clause :=
  Clause.ofList [Literal.pos 0, Literal.neg 0, Literal.neg 1]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Left side of the target partition in the occurrence-aliasing regression. -/
def expandedDepthAliasA : Clause :=
  Clause.single (Literal.pos 0)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Right side of the target partition in the occurrence-aliasing regression. -/
def expandedDepthAliasB : Clause :=
  Clause.ofList [Literal.neg 0, Literal.neg 1]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The sequent proved by the outer occurrence-aliasing regression. -/
def expandedDepthAliasSequent : ClauseSequent :=
  Finset.union expandedDepthAliasGamma
    (ClauseSequent.single expandedDepthAliasTarget)

/-- A weakening-free outer rule whose selected residual clause is already in
    its shared context.  Both exact premises therefore erase to the same
    finite-set sequent, losing the selected occurrence's provenance. -/
def expandedDepthAliasTree :
    GCNFProofTree expandedDepthAliasSequent := by
  let As : ClauseSequent :=
    ClauseSequent.single (Clause.ofList [Literal.neg 0, Literal.neg 1])
  have hLeft :
      Finset.union expandedDepthAliasGamma As =
        expandedDepthAliasGamma := by
    native_decide
  have hRight :
      Finset.union expandedDepthAliasGamma
          (ClauseSequent.single (Clause.single (Literal.pos 0))) =
        expandedDepthAliasGamma := by
    native_decide
  have leftTree :
      GCNFProofTree (Finset.union expandedDepthAliasGamma As) := by
    exact transportGCNFProofTree hLeft.symm expandedDepthAliasInner
  have rightTree :
      GCNFProofTree
        (Finset.union expandedDepthAliasGamma
          (ClauseSequent.single (Clause.single (Literal.pos 0)))) := by
    exact transportGCNFProofTree hRight.symm expandedDepthAliasInner
  have hConclusion :
      expandedDepthAliasSequent =
        Finset.union expandedDepthAliasGamma
          (ClauseSequent.mapSet As
            (fun A => clauseWithLiteral A (Literal.pos 0))) := by
    native_decide
  exact transportGCNFProofTree hConclusion.symm
    (.rule expandedDepthAliasGamma As (Literal.pos 0) As
      expandedDepthAliasGamma expandedDepthAliasGamma (ordinary_left leftTree) (ordinary_right leftTree) leftTree rightTree
      ⟨Clause.ofList [Literal.neg 0, Literal.neg 1], by native_decide⟩
      (fun _ h => h)
      (fun D hD => (Finset.mem_union_exp _ _ _).mpr (Or.inl hD))
      (fun D hD => (Finset.mem_union_exp _ _ _).mpr (Or.inl hD)))



/-- Its compressed tree has two ordinary rule occurrences after simultaneous
    nodes are charged by the size of their principal family. -/
theorem expandedDepthAliasTree_expandedDepth :
    expandedDepth expandedDepthAliasTree = 2 := by
  native_decide



/-- The concrete aliasing example satisfies every clause-partition premise of
    Lemma 9.2.2. -/
theorem expandedDepthAlias_partition_hypotheses :
    expandedDepthAliasTarget ∈ expandedDepthAliasSequent ∧
    (∃ l₁ l₂,
      l₁ ∈ expandedDepthAliasTarget ∧
      l₂ ∈ expandedDepthAliasTarget ∧
      l₁ ≠ l₂) ∧
    (∃ a, a ∈ expandedDepthAliasA) ∧
    (∃ b, b ∈ expandedDepthAliasB) ∧
    (∀ l, l ∈ expandedDepthAliasA →
      l ∉ expandedDepthAliasB) ∧
    expandedDepthAliasTarget =
      Clause.union expandedDepthAliasA expandedDepthAliasB := by
  refine ⟨by native_decide, ?_, ?_, ?_, ?_, by native_decide⟩
  · exact
      ⟨Literal.pos 0, Literal.neg 0,
        by native_decide, by native_decide, by native_decide⟩
  · exact ⟨Literal.pos 0, by native_decide⟩
  · exact ⟨Literal.neg 0, by native_decide⟩
  · intro l hlA hlB
    have hl : l = Literal.pos 0 := by
      exact (Finset.mem_singleton _ _).mp hlA
    subst l
    exact (by native_decide : Literal.pos 0 ∉ expandedDepthAliasB) hlB

-- ========= Helper defs for Lemma 9.2.3: clause classification =========

/-- Lemma 9.2.3 (companion): The subset of clauses in a ClauseSequent
    that contain more than one literal. -/
@[blueprint "chap9__lemma_9_2_3"]
def multiLiteralClauses (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => decide (1 < C.card)) S

/-- Lemma 9.2.3 (companion): The subset of clauses in a ClauseSequent
    that consist of exactly one literal. -/
@[blueprint "chap9__lemma_9_2_3"]
def oneLiteralClauses (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => decide (C.card = 1)) S

-- ========= Combined construction: IWW + literal-only axioms =========
-- The construction uses the exact no-weakening contexts at every rule node
-- and tracks Gallier's condition that every axiom consists only of literals.





/-! ## Occurrence-preserving construction for Lemma 9.2.1 -/

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- When every clause occurrence is a literal, validity supplies a genuine
    complementary-pair axiom on the exact occurrence list. -/
theorem all_singletons_occurrence (clauses : List Clause)
    (hSingle : ∀ C ∈ clauses, ∃ L : Literal, C = Clause.single L)
    (hValid : ClauseSequent.isValid (ClauseSequent.ofList clauses)) :
    ∃ T : OccurrenceGCNFProof clauses,
      T.axiomsAllSingleLiteral := by
  have hSingleSet :
      ∀ C ∈ ClauseSequent.ofList clauses,
        ∃ L : Literal, C = Clause.single L := by
    intro C hC
    exact hSingle C
      ((Finset.mem_ofList_exp C clauses).mp hC)
  obtain ⟨P, hPos, hNeg⟩ :=
    singletons_valid_imp_trivial
      (ClauseSequent.ofList clauses) hSingleSet hValid
  exact
    ⟨.axiom_ clauses
      ⟨P,
        (Finset.mem_ofList_exp
          (Clause.single (Literal.pos P)) clauses).mp hPos,
        (Finset.mem_ofList_exp
          (Clause.single (Literal.neg P)) clauses).mp hNeg⟩,
      hSingle⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Exact unary occurrence step: the same `pre` and `suf` lists surround the
    selected clause in the conclusion and both premises. -/
theorem ofList_occurrence_step
    (pre suf : List Clause) (A : Clause) (B : Literal)
    (ihLeft :
      ∃ T : OccurrenceGCNFProof (pre ++ A :: suf),
        T.axiomsAllSingleLiteral)
    (ihRight :
      ∃ T : OccurrenceGCNFProof
        (pre ++ Clause.single B :: suf),
        T.axiomsAllSingleLiteral) :
    ∃ T : OccurrenceGCNFProof
      (pre ++ clauseWithLiteral A B :: suf),
      T.axiomsAllSingleLiteral := by
  obtain ⟨left, hLeft⟩ := ihLeft
  obtain ⟨right, hRight⟩ := ihRight
  exact
    ⟨.rule pre suf A B left right, ⟨hLeft, hRight⟩⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- The well-founded literal-list construction for Lemma 9.2.1, retaining
    every clause occurrence until the final root erasure. -/
theorem gcnf_occurrence_of_lit_lists :
    ∀ (ll : List (List Literal)),
    (∀ ls ∈ ll, ls ≠ []) →
    ClauseSequent.isValid (litListsToClauseSeq ll) →
    ∃ T : OccurrenceGCNFProof (ll.map Clause.ofList),
      T.axiomsAllSingleLiteral := by
  suffices hwf : ∀ (n : Nat) (ll : List (List Literal)),
      totalLitCount ll ≤ n →
      (∀ ls ∈ ll, ls ≠ []) →
      ClauseSequent.isValid (litListsToClauseSeq ll) →
      ∃ T : OccurrenceGCNFProof (ll.map Clause.ofList),
        T.axiomsAllSingleLiteral from
    fun ll hNe hValid =>
      hwf (totalLitCount ll) ll (Nat.le_refl _) hNe hValid
  intro n
  induction n with
  | zero =>
    intro ll hBound hNe hValid
    have hEmpty : ll = [] := by
      cases ll with
      | nil => rfl
      | cons hd tl =>
        have hhdNe := hNe hd
          (List.mem_cons.mpr (Or.inl rfl))
        rw [totalLitCount_cons] at hBound
        have : hd.length ≥ 1 := by
          cases hd with
          | nil => exact absurd rfl hhdNe
          | cons _ _ => simp
        omega
    subst hEmpty
    exfalso
    apply hValid
    exact
      ⟨fun _ => true, fun C hC =>
        absurd ((Finset.mem_ofList_exp C []).mp hC)
          List.not_mem_nil⟩
  | succ n ih =>
    intro ll hBound hNe hValid
    by_cases hAllSingle :
        ∀ ls ∈ ll, ∃ L, ls = [L]
    · have hSingleList :
          ∀ C ∈ ll.map Clause.ofList,
            ∃ L : Literal, C = Clause.single L := by
        intro C hC
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hC
        obtain ⟨L, rfl⟩ := hAllSingle ls hls
        exact ⟨L, ofList_singleton_eq L⟩
      exact
        all_singletons_occurrence
          (ll.map Clause.ofList) hSingleList
          (by
            simpa [litListsToClauseSeq,
              ClauseSequent.ofList] using hValid)
    · have ⟨ls, hlsMem, hlsNotSingle⟩ :
          ∃ ls ∈ ll, ∀ L, ls ≠ [L] :=
        Classical.byContradiction fun hAll =>
          hAllSingle fun ls hls =>
            Classical.byContradiction fun hNo =>
              hAll
                ⟨ls, hls, fun L hEq =>
                  hNo ⟨L, hEq⟩⟩
      have hlsNe := hNe ls hlsMem
      obtain ⟨L, rest, rfl⟩ :
          ∃ L rest, ls = L :: rest := by
        cases ls with
        | nil => exact absurd rfl hlsNe
        | cons hd tl => exact ⟨hd, tl, rfl⟩
      have hrestNe : rest ≠ [] := by
        intro h
        subst h
        exact hlsNotSingle L rfl
      have memSplit :
          ∀ (xs : List (List Literal))
            (x : List Literal),
            x ∈ xs →
            ∃ pre suf, xs = pre ++ x :: suf := by
        intro xs x hx
        induction xs with
        | nil => exact absurd hx List.not_mem_nil
        | cons hd tl ihSplit =>
          rw [List.mem_cons] at hx
          rcases hx with rfl | htl
          · exact ⟨[], tl, by simp⟩
          · obtain ⟨pre', suf', heq'⟩ :=
              ihSplit htl
            exact
              ⟨hd :: pre', suf',
                by rw [heq', List.cons_append]⟩
      obtain ⟨pre, suf, hllEq⟩ :=
        memSplit ll (L :: rest) hlsMem
      have hClauseEq :
          Clause.ofList (L :: rest) =
            clauseWithLiteral (Clause.ofList rest) L :=
        (clauseWithLiteral_ofList_cons L rest).symm
      have hMapEq :
          ll.map Clause.ofList =
            pre.map Clause.ofList ++
              clauseWithLiteral (Clause.ofList rest) L ::
                suf.map Clause.ofList := by
        rw [hllEq, List.map_append, List.map_cons,
          hClauseEq]
      have hSeqEq :
          litListsToClauseSeq ll =
            Finset.ofList
              (pre.map Clause.ofList ++
                clauseWithLiteral (Clause.ofList rest) L ::
                  suf.map Clause.ofList) := by
        show Finset.ofList (ll.map Clause.ofList) = _
        rw [hMapEq]
      rw [hSeqEq] at hValid
      have hLeftValid :=
        ofList_left_valid
          (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hRightValid :=
        ofList_right_valid
          (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L hValid
      have hLeftEq :
          Finset.ofList
              (pre.map Clause.ofList ++
                Clause.ofList rest :: suf.map Clause.ofList) =
            litListsToClauseSeq (pre ++ rest :: suf) := by
        simp only [litListsToClauseSeq,
          List.map_append, List.map_cons]
      have hRightEq :
          Finset.ofList
              (pre.map Clause.ofList ++
                Clause.single L :: suf.map Clause.ofList) =
            litListsToClauseSeq (pre ++ [L] :: suf) := by
        unfold litListsToClauseSeq
        simp only [List.map_append, List.map_cons]
        rw [ofList_singleton_eq]
      have hLeftSize :
          totalLitCount (pre ++ rest :: suf) <
            totalLitCount ll := by
        rw [hllEq]
        exact
          totalLitCount_replace_lt
            pre (L :: rest) suf rest (by simp)
      have hRightSize :
          totalLitCount (pre ++ [L] :: suf) <
            totalLitCount ll := by
        rw [hllEq]
        apply
          totalLitCount_replace_lt
            pre (L :: rest) suf [L]
        cases rest with
        | nil => exact absurd rfl hrestNe
        | cons _ _ => simp
      have hNe' :
          ∀ ls ∈ pre ++ (L :: rest) :: suf,
            ls ≠ [] :=
        hllEq ▸ hNe
      have hLeftNe :
          ∀ ls ∈ pre ++ rest :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact
            hNe' ls'
              (List.mem_append.mpr (Or.inl hPre))
        · exact hrestNe
        · exact
            hNe' ls'
              (List.mem_append.mpr
                (Or.inr
                  (List.mem_cons.mpr (Or.inr hSuf))))
      have hRightNe :
          ∀ ls ∈ pre ++ [L] :: suf, ls ≠ [] := by
        intro ls' hls'
        rw [List.mem_append, List.mem_cons] at hls'
        rcases hls' with hPre | (rfl | hSuf)
        · exact
            hNe' ls'
              (List.mem_append.mpr (Or.inl hPre))
        · exact List.cons_ne_nil L []
        · exact
            hNe' ls'
              (List.mem_append.mpr
                (Or.inr
                  (List.mem_cons.mpr (Or.inr hSuf))))
      have ihLeft :=
        ih (pre ++ rest :: suf) (by omega)
          hLeftNe (hLeftEq ▸ hLeftValid)
      have ihRight :=
        ih (pre ++ [L] :: suf) (by omega)
          hRightNe (hRightEq ▸ hRightValid)
      have hLeftIndex :
          (pre ++ rest :: suf).map Clause.ofList =
            pre.map Clause.ofList ++
              Clause.ofList rest :: suf.map Clause.ofList := by
        rw [List.map_append]
        rfl
      have hRightIndex :
          (pre ++ [L] :: suf).map Clause.ofList =
            pre.map Clause.ofList ++
              Clause.single L :: suf.map Clause.ofList := by
        rw [List.map_append]
        simp only [List.map_cons, ofList_singleton_eq]
      rw [hLeftIndex] at ihLeft
      rw [hRightIndex] at ihRight
      have ihLeft' :
          ∃ T : OccurrenceGCNFProof
              (pre.map Clause.ofList ++
                Clause.ofList rest :: suf.map Clause.ofList),
            T.axiomsAllSingleLiteral := by
        exact ihLeft
      have ihRight' :
          ∃ T : OccurrenceGCNFProof
              (pre.map Clause.ofList ++
                Clause.single L :: suf.map Clause.ofList),
            T.axiomsAllSingleLiteral := by
        exact ihRight
      rw [hMapEq]
      exact
        ofList_occurrence_step
          (pre.map Clause.ofList) (suf.map Clause.ofList)
          (Clause.ofList rest) L ihLeft' ihRight'
-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
noncomputable def clauseToLitList (C : Clause) : List Literal := C.toList

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
theorem clauseToLitList_ofList (C : Clause) :
    Clause.ofList (clauseToLitList C) = C := by
-- BEGIN PROOF
  unfold clauseToLitList Clause.ofList
  apply Finset.ext; intro a
  rw [Finset.mem_ofList]; exact Finset.mem_toList C a

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
theorem map_ofList_map_toList (l : List Clause) :
    (l.map clauseToLitList).map Clause.ofList = l := by
-- BEGIN PROOF
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    rw [clauseToLitList_ofList hd, ih]

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Lift the occurrence construction from literal lists back to an exact list
    of clauses. -/
theorem gcnf_occurrence_of_list (l : List Clause)
    (hNe : ∀ C ∈ l, C ≠ Clause.empty)
    (hValid :
      ClauseSequent.isValid (ClauseSequent.ofList l)) :
    ∃ T : OccurrenceGCNFProof l,
      T.axiomsAllSingleLiteral := by
  let ll := l.map clauseToLitList
  have hMapEq :
      ll.map Clause.ofList = l :=
    map_ofList_map_toList l
  have hSeqEq :
      litListsToClauseSeq ll =
        ClauseSequent.ofList l := by
    unfold litListsToClauseSeq ClauseSequent.ofList
    rw [hMapEq]
  have hllNe : ∀ ls ∈ ll, ls ≠ [] := by
    intro ls hls
    show ls ≠ []
    obtain ⟨C, hC, rfl⟩ :=
      List.mem_map.mp hls
    intro hEmpty
    apply hNe C hC
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have haToList :
          a ∈ clauseToLitList C :=
        (Finset.mem_toList C a).mpr ha
      rw [hEmpty] at haToList
      exact absurd haToList List.not_mem_nil
    · intro ha
      exact ((Finset.mem_empty a).mp ha).elim
  have hOccurrence :=
    gcnf_occurrence_of_lit_lists ll hllNe
      (hSeqEq ▸ hValid)
  rw [hMapEq] at hOccurrence
  exact hOccurrence



-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
theorem finset_ofList_toList_eq (S : ClauseSequent) :
    Finset.ofList S.toList = S := by
-- BEGIN PROOF
  apply Finset.ext; intro C
  rw [Finset.mem_ofList]; exact Finset.mem_toList S C

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Wrap the exact proof on `S.toList` as an occurrence derivation of the
    original extensional root. Root duplication is excluded only here. -/
theorem gcnf_occurrence_from_normal_form
    (S : ClauseSequent)
    (hValid : ClauseSequent.isValid S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    ∃ D : OccurrenceGCNFDerivation S,
      D.tree.axiomsAllSingleLiteral := by
  have hErase :
      ClauseSequent.ofList S.toList = S :=
    eraseOccurrences_toList S
  have hListNe :
      ∀ C ∈ S.toList, C ≠ Clause.empty := by
    intro C hC
    exact hNe C ((Finset.mem_toList S C).mp hC)
  have hListValid :
      ClauseSequent.isValid
        (ClauseSequent.ofList S.toList) := by
    rw [hErase]
    exact hValid
  obtain ⟨tree, hLeaves⟩ :=
    gcnf_occurrence_of_list S.toList hListNe
      hListValid
  exact
    ⟨{
      occurrences := S.toList
      nodupRoot := clauseSequent_toList_nodup S
      erase_eq := eraseOccurrences_toList S
      tree := tree
    }, hLeaves⟩



-- ========= Admissible weakening for GCNF' =========

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Finset union right-commutativity: (a ∪ b) ∪ c = (a ∪ c) ∪ b. -/
theorem finset_union_right_comm (a b c : ClauseSequent) :
    Finset.union (Finset.union a b) c = Finset.union (Finset.union a c) b := by
-- BEGIN PROOF
  apply Finset.ext; intro x; simp [Finset.mem_union]
  constructor
  · intro h; rcases h with (ha | hb) | hc
    all_goals first | exact Or.inl (Or.inl ‹_›) | exact Or.inl (Or.inr ‹_›) | exact Or.inr ‹_›
  · intro h; rcases h with (ha | hc) | hb
    all_goals first | exact Or.inl (Or.inl ‹_›) | exact Or.inl (Or.inr ‹_›) | exact Or.inr ‹_›

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- If Gamma1 ⊆ Gamma ∪ M, then Gamma1 ∪ D ⊆ (Gamma ∪ D) ∪ M. -/
theorem subset_weaken_union (Gamma1 Gamma D M : ClauseSequent)
    (h : Finset.Subset Gamma1 (Finset.union Gamma M)) :
    Finset.Subset (Finset.union Gamma1 D) (Finset.union (Finset.union Gamma D) M) := by
-- BEGIN PROOF
  intro x hx; rw [Finset.mem_union] at hx ⊢
  rcases hx with hG1 | hD
  · rcases (Finset.mem_union_exp x Gamma M).mp (h x hG1) with hG | hM
    · exact Or.inl ((Finset.mem_union_exp x Gamma D).mpr (Or.inl hG))
    · exact Or.inr hM
  · exact Or.inl ((Finset.mem_union_exp x Gamma D).mpr (Or.inr hD))







-- ========= Helper lemmas for empty clause removal =========

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton clause is nonempty. -/
theorem single_ne_empty (L : Literal) : Clause.single L ≠ Clause.empty := by
-- BEGIN PROOF
  intro h; have h1 : L ∈ Clause.single L := (Finset.mem_singleton L L).mpr rfl
  rw [h] at h1; exact (Finset.mem_empty L).mp h1

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- clauseWithLiteral always produces a nonempty clause. -/
theorem cwl_ne_empty (A : Clause) (B : Literal) : clauseWithLiteral A B ≠ Clause.empty := by
-- BEGIN PROOF
  intro h; have h1 : B ∈ clauseWithLiteral A B := (Finset.mem_insert_exp B B A).mpr (Or.inl rfl)
  rw [h] at h1; exact (Finset.mem_empty B).mp h1





-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Removing empty clause from a proof tree: if T proves S, then S.erase ∅ is provable. -/
theorem gcnf_provable_erase_empty {S : ClauseSequent} (T : GCNFProofTree S) :
    GCNFProvable (Finset.erase S Clause.empty) := by
-- BEGIN PROOF
  have hEq : Finset.erase S Clause.empty = S := by
    apply Finset.ext
    intro C
    simp only [Finset.mem_erase]
    exact ⟨And.left, fun hC => ⟨hC, T.ordinary C hC⟩⟩
  rw [hEq]
  exact ⟨T⟩



-- ========= Lemma 9.2.1: Proof without weakenings =========

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Lemma 9.2.1 (occurrence carrier): construct the weakening-free proof
    before erasing clause-occurrence provenance. -/
theorem gcnf_occurrence_proof_without_weakenings
    (S : ClauseSequent)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty)
    (hProv : GCNFProvable S) :
    ∃ D : OccurrenceGCNFDerivation S,
      D.tree.axiomsAllSingleLiteral := by
  exact
    gcnf_occurrence_from_normal_form S
      (gcnf_soundness S hProv) hNe

end LCS.SLD.SLDForm.Completeness
end

