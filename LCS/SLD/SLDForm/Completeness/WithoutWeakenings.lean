import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import Attach
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings.ProofsStamp

/-! # Proofs without weakenings (Definition 9.2.3, Lemma 9.2.1)

Section 9.2.3: GCNF'-proofs without weakenings, and the construction of a weakening-free proof with literal-only axioms for every GCNF'-provable set of clauses. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

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

/-- Lemma 9.2.1: If a set S of clauses is GCNF'-provable, then a GCNF'-proof
    without weakenings and in which all axioms contain only literals can be
    constructed. The `hNe` guard records Gallier's nonempty clause grammar in
    Lean's unrestricted finite-set representation. -/
@[blueprint "chap9__lemma_9_2_1" (main := true)]
theorem gcnf_proof_without_weakenings (S : ClauseSequent)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty)
    (hProv : GCNFProvable S) :
    ∃ T : GCNFProofTree S, IsWithoutWeakenings T ∧ T.axiomsAllSingleLiteral 

end LCS.SLD.SLDForm.Completeness
end
