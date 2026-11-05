import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.OccurrenceNormalization
import Attach
import LCS.SLD.SLDForm.Completeness.RootPartition.ProofsStamp

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

/-- Lemma 9.2.1: If a set S of clauses is GCNF'-provable, then a GCNF'-proof
    without weakenings and in which all axioms contain only literals can be
    constructed. The `hNe` guard records Gallier's nonempty clause grammar in
    Lean's unrestricted finite-set representation. -/
@[blueprint "chap9__lemma_9_2_1" (main := true)]
theorem gcnf_proof_without_weakenings (S : ClauseSequent)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty)
    (hProv : GCNFProvable S) :
    ∃ T : GCNFProofTree S, IsWithoutWeakenings T ∧ T.axiomsAllSingleLiteral 

-- ========= StrictIWW + axiomsAllSingleLiteral construction =========
-- Parallel construction retained under the compatibility name IsStrictIWW.
-- Key insight: the all-singletons base case uses a single axiom_ node
-- (vacuously StrictIWW), and the inductive step (ofList_strict_step)
-- always sets Gamma1 = Gamma2 = Gamma.













-- ========= Internal encoding of an arbitrary root partition =========

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The derived root macro for a partition `A ∪ B`. An order enumerating `B`
    is peeled by genuine GCNF' rule nodes along the left spine. At each node,
    the residual clause `A ∪ remaining(B)` must occur in that rule's selected
    left-premise clauses `Cs`. -/
def rootPartitionMacro (A : Clause) :
    {S : ClauseSequent} → GCNFProofTree S → List Literal → Prop
  | _, .axiom_ _ hOrd _, _ => False
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd _ _ _ _ _ _, [] => False
  | _, .rule _ _ pivot Cs _ _ hGammaOrd hAsOrd _ _ _ _ _ _, [b] =>
      pivot = b ∧ A ∈ Cs
  | _, .rule _ _ pivot Cs _ _ hGammaOrd hAsOrd left _ _ _ _ _, b :: b' :: bs =>
      pivot = b ∧
      Clause.union A (Clause.ofList (b' :: bs)) ∈ Cs ∧
      rootPartitionMacro A left (b' :: bs)

-- ATTACH-BLOCKER: unsupported untagged structure
/-- Structural certificate that `T` begins with the derived GCNF' root macro
    for an arbitrary nonempty disjoint partition `C = A ∪ B`. The duplicate-free
    order covers exactly `B`, and every peel is checked against an actual rule
    node by `rootPartitionMacro`. -/
@[blueprint "chap9__lemma_9_2_2"]
structure RootPartitionCertificate {S : ClauseSequent}
    (T : GCNFProofTree S) (C A B : Clause) : Prop where
  leftNonempty : ∃ a, a ∈ A
  rightNonempty : ∃ b, b ∈ B
  disjoint : ∀ l, l ∈ A → l ∉ B
  unionEq : C = Clause.union A B
  rootedMacro : ∃ order : List Literal,
    order.Nodup ∧
    Clause.ofList order = B ∧
    rootPartitionMacro A T order

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A root-partition certificate is structurally tied to the indexed root
    sequent: its target clause really occurs in that sequent. -/
theorem RootPartitionCertificate.target_mem {S : ClauseSequent}
    {T : GCNFProofTree S} {C A B : Clause}
    (h : RootPartitionCertificate T C A B) : C ∈ S := by
  rcases h.rootedMacro with ⟨order, _hNodup, hOrder, hMacro⟩
  cases T with
  | axiom_ _ hOrd _ =>
      exact False.elim hMacro
  | rule Gamma As pivot Cs Gamma1 Gamma2 hGammaOrd hAsOrd left right hCsNonempty hCsSub hG1Sub hG2Sub =>
      cases order with
      | nil => exact False.elim hMacro
      | cons b bs =>
          have hPivot : pivot = b := by
            cases bs with
            | nil => exact hMacro.1
            | cons b' bs' => exact hMacro.1
          have hResidual : Clause.union A (Clause.ofList bs) ∈ Cs := by
            cases bs with
            | nil =>
                have hA : A ∈ Cs := hMacro.2
                have hEmpty : Clause.union A (Clause.ofList []) = A := by
                  apply Finset.ext
                  intro l
                  simp [Clause.union, Clause.ofList]
                rw [hEmpty]
                exact hA
            | cons b' bs' => exact hMacro.2.1
          have hCeq :
              C = clauseWithLiteral (Clause.union A (Clause.ofList bs)) pivot := by
            rw [h.unionEq, ← hOrder, hPivot]
            apply Finset.ext
            intro l
            simp only [Clause.union, Clause.ofList, clauseWithLiteral,
              Finset.mem_union, Finset.mem_ofList, Finset.mem_insert, List.mem_cons]
            constructor
            · rintro (hA | rfl | hbs)
              · exact Or.inr (Or.inl hA)
              · exact Or.inl rfl
              · exact Or.inr (Or.inr hbs)
            · rintro (rfl | hA | hbs)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl hA
              · exact Or.inr (Or.inr hbs)
          rw [hCeq]
          exact (Finset.mem_union_exp _ _ _).mpr
            (Or.inr ((mem_image_iff _ _ _).mpr
              ⟨Clause.union A (Clause.ofList bs), hCsSub _ hResidual, rfl⟩))

-- ========= Lemma 9.2.2: Permutation at root =========

/-- The normalized pair identified with a supplied occurrence root plan is
related by the plan's finite inference interchanges. The equalities identify
these particular compressed trees; genuineness of both endpoints is explicit
pair admissibility. Automatic normalization, plan synthesis and identification
of the book's pair are separate construction obligations. -/
@[blueprint "chap9__lemma_9_2_2"]
theorem rootPlan_selectedPair_permutation
    {clauses : List Clause} (source : OccurrenceGCNFProof clauses)
    {A : Clause} {order : List Literal}
    {target : RootOccurrence clauses (OccurrenceGCNFProof.partitionResidual A order)}
    (plan : OccurrenceGCNFProof.RootPartitionPlan A source order target)
    (hMin : source.axiomsAllSingleLiteral)
    (T T' : GCNFProofTree (eraseOccurrences clauses))
    (hT : T = Occurrence.compress source hMin)
    (hT' : T' = Occurrence.compress plan.execute.tree
      (plan.execute.axiomsAllSingleLiteral_iff.mpr hMin))
    (hGen : GenuineDecompositions T) (hGen' : GenuineDecompositions T') :
    Nonempty (OccurrenceGCNFProof.InferencePermutationCertificate source plan.execute.tree) ∧
    IsStrictIWW T ∧ IsStrictIWW T' ∧
    T.axiomsAllSingleLiteral ∧ T'.axiomsAllSingleLiteral ∧
    GenuineDecompositions T ∧ GenuineDecompositions T' 

/-- Lemma 9.2.2: For any multi-literal clause C in S and any partition C = (A lor B),
    there is a GCNF'-proof T' of S in which the lor:left rule is applied to (A lor B)
    at the root. Furthermore, if T is without weakenings and all its axioms contain
    only literals, T' has exactly the same depth as T. -/
@[attach_debt, blueprint "chap9__lemma_9_2_2" (main := true)]
theorem gcnf_permutation_at_root (S : ClauseSequent)
    (T : GCNFProofTree S)
    (C : Clause) (hC : C ∈ S) (hLen : ∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂)
    (A B : Clause)
    (hA : ∃ a, a ∈ A)
    (hB : ∃ b, b ∈ B)
    (hDisjoint : ∀ l, l ∈ A → l ∉ B)
    (hPart : C = Clause.union A B) :
    ∃ T' : GCNFProofTree S,
      RootPartitionCertificate T' C A B ∧
      (IsWithoutWeakenings T ∧ T.axiomsAllSingleLiteral →
        proofDepth T' = proofDepth T) 

/-- The concrete data used by the regression probe below satisfy every
    non-proof-tree hypothesis of `gcnf_permutation_at_root`. -/
example :
    let pos0 := Clause.single (Literal.pos 0)
    let pos1 := Clause.single (Literal.pos 1)
    let neg1 := Clause.single (Literal.neg 1)
    let Gamma : ClauseSequent := ClauseSequent.single pos0
    let As : ClauseSequent := Finset.ofList [pos1, neg1]
    let pivot := Literal.neg 0
    let S := Finset.union Gamma
      (ClauseSequent.mapSet As (fun D => clauseWithLiteral D pivot))
    let C := clauseWithLiteral pos1 pivot
    let A := Clause.single pivot
    let B := Clause.single (Literal.pos 1)
    C ∈ S ∧
      (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂) ∧
      (∃ a, a ∈ A) ∧
      (∃ b, b ∈ B) ∧
      (∀ l, l ∈ A → l ∉ B) ∧
      C = Clause.union A B := by
  dsimp only
  refine ⟨by native_decide, ?_, ?_, ?_, ?_, by native_decide⟩
  · exact ⟨Literal.pos 1, Literal.neg 0, by native_decide,
      by native_decide, by native_decide⟩
  · exact ⟨Literal.neg 0, by native_decide⟩
  · exact ⟨Literal.pos 1, by native_decide⟩
  · intro l hlA hlB
    have hlA' : l = Literal.neg 0 :=
      (Finset.mem_singleton _ _).mp hlA
    have hlB' : l = Literal.pos 1 :=
      (Finset.mem_singleton _ _).mp hlB
    rw [hlA'] at hlB'
    exact Literal.noConfusion hlB'

/-- Regression probe for the exact-depth clause-partition contract. A single
    GCNF' inference may split several clauses sharing one pivot. Re-rooting on
    the other literal of one of those clauses cannot in general preserve
    depth, even when the source tree is exactly weakening-free and all axiom
    labels contain only singleton clauses. -/
example :
    let pos0 := Clause.single (Literal.pos 0)
    let pos1 := Clause.single (Literal.pos 1)
    let neg1 := Clause.single (Literal.neg 1)
    let Gamma : ClauseSequent := ClauseSequent.single pos0
    let As : ClauseSequent := Finset.ofList [pos1, neg1]
    let pivot := Literal.neg 0
    let S := Finset.union Gamma
      (ClauseSequent.mapSet As (fun D => clauseWithLiteral D pivot))
    let T : GCNFProofTree S :=
      .rule Gamma As pivot As Gamma Gamma
        (by simp [Gamma, pos0, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_singleton])
        (by simp [As, pos1, neg1, ClauseSequent.isOrdinary, Finset.mem_ofList])
        (.axiom_ _ (by simp [Gamma, As, pos0, pos1, neg1, pivot, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton]) ⟨1, by native_decide, by native_decide⟩)
        (.axiom_ _ (by simp [Gamma, As, pos0, pos1, neg1, pivot, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton]) ⟨0, by native_decide, by native_decide⟩)
        ⟨pos1, by native_decide⟩
        (fun _ h => h)
        (fun _ h => (Finset.mem_union_exp _ _ _).mpr (Or.inl h))
        (fun _ h => (Finset.mem_union_exp _ _ _).mpr (Or.inl h))
    let C := clauseWithLiteral pos1 pivot
    let A := Clause.single pivot
    let B := Clause.single (Literal.pos 1)
    ¬ ∃ T' : GCNFProofTree S,
        RootPartitionCertificate T' C A B ∧
        (IsWithoutWeakenings T ∧ T.axiomsAllSingleLiteral →
          proofDepth T' = proofDepth T) := by
  dsimp only
  let pos0 := Clause.single (Literal.pos 0)
  let pos1 := Clause.single (Literal.pos 1)
  let neg1 := Clause.single (Literal.neg 1)
  let Gamma : ClauseSequent := ClauseSequent.single pos0
  let As : ClauseSequent := Finset.ofList [pos1, neg1]
  let pivot := Literal.neg 0
  let S := Finset.union Gamma
    (ClauseSequent.mapSet As (fun D => clauseWithLiteral D pivot))
  let T : GCNFProofTree S :=
    .rule Gamma As pivot As Gamma Gamma
        (by simp [Gamma, pos0, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_singleton])
        (by simp [As, pos1, neg1, ClauseSequent.isOrdinary, Finset.mem_ofList])
      (.axiom_ _ (by simp [Gamma, As, pos0, pos1, neg1, pivot, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton]) ⟨1, by native_decide, by native_decide⟩)
      (.axiom_ _ (by simp [Gamma, As, pos0, pos1, neg1, pivot, ClauseSequent.isOrdinary, ClauseSequent.single, Finset.mem_union, Finset.mem_ofList, Finset.mem_singleton]) ⟨0, by native_decide, by native_decide⟩)
      ⟨pos1, by native_decide⟩
      (fun _ h => h)
      (fun _ h => (Finset.mem_union_exp _ _ _).mpr (Or.inl h))
      (fun _ h => (Finset.mem_union_exp _ _ _).mpr (Or.inl h))
  let C := clauseWithLiteral pos1 pivot
  let A := Clause.single pivot
  let B := Clause.single (Literal.pos 1)
  have hIWW : IsWithoutWeakenings T := by
    exact ⟨rfl, rfl, rfl, trivial, trivial⟩
  have hLiterals : T.axiomsAllSingleLiteral := by
    constructor
    · intro D hD
      rw [Finset.mem_union] at hD
      rcases hD with hD | hD
      · exact ⟨Literal.pos 0, (mem_csingle D pos0).mp hD⟩
      · rw [Finset.mem_ofList] at hD
        rcases List.mem_cons.mp hD with hD | hD
        · exact ⟨Literal.pos 1, hD⟩
        · exact ⟨Literal.neg 1, List.mem_singleton.mp hD⟩
    · intro D hD
      rw [Finset.mem_union] at hD
      rcases hD with hD | hD
      · exact ⟨Literal.pos 0, (mem_csingle D pos0).mp hD⟩
      · exact ⟨pivot, (mem_csingle D (Clause.single pivot)).mp hD⟩
  have hNoNegUnit : ∀ P : Nat, Clause.single (Literal.neg P) ∉ S := by
    intro P hP
    rw [Finset.mem_union] at hP
    rcases hP with hGamma | hMap
    · have hEq := (mem_csingle _ pos0).mp hGamma
      have hLit := single_eq_implies_lit_eq _ _ hEq
      exact Literal.noConfusion hLit
    · obtain ⟨D, hD, hEq⟩ := (mem_image_iff _ _ _).mp hMap
      rw [Finset.mem_ofList] at hD
      rcases List.mem_cons.mp hD with hD | hD
      · subst hD
        have hPos1 : Literal.pos 1 ∈ Clause.single (Literal.neg P) := by
          rw [← hEq]
          exact (Finset.mem_insert_exp _ _ _).mpr
            (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
        exact Literal.noConfusion ((Finset.mem_singleton _ _).mp hPos1)
      · have hD' := List.mem_singleton.mp hD
        subst hD'
        have hNeg0 : Literal.neg 0 ∈ Clause.single (Literal.neg P) := by
          rw [← hEq]
          exact (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
        have hNeg1 : Literal.neg 1 ∈ Clause.single (Literal.neg P) := by
          rw [← hEq]
          exact (Finset.mem_insert_exp _ _ _).mpr
            (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
        have h0 := (Finset.mem_singleton _ _).mp hNeg0
        have h1 := (Finset.mem_singleton _ _).mp hNeg1
        injection h0 with h0'
        injection h1 with h1'
        omega
  rintro ⟨T', hCert, hDepth⟩
  have hDepth' : proofDepth T' = 1 := by
    rw [hDepth ⟨hIWW, hLiterals⟩]
    rfl
  have hImpossible :
      ∀ (S₀ : ClauseSequent) (T₀ : GCNFProofTree S₀),
        S₀ = S →
        RootPartitionCertificate T₀ C A B →
        proofDepth T₀ = 1 →
        False := by
    intro S₀ T₀ hS₀ hCert₀ hDepth₀
    rcases hCert₀.rootedMacro with ⟨order, _hNodup, hOrder, hMacro⟩
    cases T₀ with
    | axiom_ _ hOrd _ =>
        exact False.elim hMacro
    | rule G As' p Cs G1 G2 hGammaOrd hAsOrd left right hCsNe hCsSub hG1Sub hG2Sub =>
        cases order with
        | nil =>
            have hPos1B : Literal.pos 1 ∈ B :=
              (Finset.mem_singleton _ _).mpr rfl
            rw [← hOrder] at hPos1B
            exact (Finset.mem_empty _).mp hPos1B
        | cons b bs =>
            have hbOrder : b ∈ Clause.ofList (b :: bs) :=
              (Finset.mem_ofList_exp _ _).mpr
                (List.mem_cons.mpr (Or.inl rfl))
            rw [hOrder] at hbOrder
            have hb : b = Literal.pos 1 :=
              (Finset.mem_singleton _ _).mp hbOrder
            have hp : p = Literal.pos 1 := by
              cases bs with
              | nil => exact hMacro.1.trans hb
              | cons b' bs' => exact hMacro.1.trans hb
            have hRightZero : proofDepth right = 0 := by
              simp only [proofDepth] at hDepth₀
              omega
            have hRightImpossible :
                ∀ (R : ClauseSequent) (right₀ : GCNFProofTree R),
                  R = Finset.union G2
                    (ClauseSequent.single (Clause.single p)) →
                  proofDepth right₀ = 0 →
                  False := by
              intro R right₀ hR hRightZero₀
              cases right₀ with
              | axiom_ _ hOrd hTriv =>
                  obtain ⟨P, _hPos, hNeg⟩ := hTriv
                  rw [hR, Finset.mem_union] at hNeg
                  rcases hNeg with hNegG2 | hNegPivot
                  · have hNegS₀ := hG2Sub _ hNegG2
                    rw [hS₀] at hNegS₀
                    exact hNoNegUnit P hNegS₀
                  · have hClauseEq :=
                      (mem_csingle _ (Clause.single p)).mp hNegPivot
                    have hLitEq :=
                      single_eq_implies_lit_eq _ _ hClauseEq
                    rw [hp] at hLitEq
                    exact Literal.noConfusion hLitEq
              | rule _ _ _ _ _ _ hGammaOrd hAsOrd _ _ _ _ _ _ =>
                  simp [proofDepth] at hRightZero₀
            exact hRightImpossible _ right rfl hRightZero
  exact hImpossible S T' rfl hCert hDepth'

-- ========= Helper: collect axiom leaves of a proof tree =========

/-- Lemma 9.2.3 (required helper): Collects the list of axiom leaf sequents
    from a GCNFProofTree by recursion on the tree structure. -/
@[blueprint "chap9__lemma_9_2_3"]
def axiomLeaves : {S : ClauseSequent} → GCNFProofTree S → List ClauseSequent
  | _, .axiom_ S hOrd _ => [S]
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd leftTree rightTree _ _ _ _ =>
    axiomLeaves leftTree ++ axiomLeaves rightTree

-- ========= Helper lemmas for Lemma 9.2.3 =========

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- If a Finset of literals has card 1, then any two elements are equal. -/
theorem finset_card_one_eq {S : Finset Literal} (hCard : S.card = 1) (a b : Literal)
    (ha : a ∈ S) (hb : b ∈ S) : a = b := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hCard ha hb
  induction v using Multiset.ind with
  | _ l =>
    intro hnd hCard ha hb
    have hLen : l.length = 1 := by
      show l.length = 1; exact hCard
    have ha' : a ∈ l := ha; have hb' : b ∈ l := hb
    cases hv : l with
    | nil => rw [hv] at hLen; simp at hLen
    | cons x xs =>
      rw [hv] at hLen ha' hb'
      have hxs : xs = [] := by cases xs with | nil => rfl | cons _ _ => simp at hLen
      rw [hxs] at ha' hb'
      exact (by rw [List.mem_cons] at ha'; rcases ha' with rfl | h; rfl
                exact absurd h List.not_mem_nil : a = x).trans
            (by rw [List.mem_cons] at hb'; rcases hb' with rfl | h; rfl
                exact absurd h List.not_mem_nil : x = b)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Generic form of `finset_card_one_eq`, used for finite sets of clauses. -/
theorem finset_card_one_elements_eq {α : Type} {S : Finset α}
    (hCard : S.card = 1) (a b : α)
    (ha : a ∈ S) (hb : b ∈ S) : a = b := by
  cases S with | mk v nd =>
  revert nd hCard ha hb
  induction v using Multiset.ind with
  | _ l =>
    intro hnd hCard ha hb
    have hLen : l.length = 1 := by
      show l.length = 1
      exact hCard
    have ha' : a ∈ l := ha
    have hb' : b ∈ l := hb
    cases hv : l with
    | nil =>
        rw [hv] at hLen
        simp at hLen
    | cons x xs =>
        rw [hv] at hLen ha' hb'
        have hxs : xs = [] := by
          cases xs with
          | nil => rfl
          | cons _ _ => simp at hLen
        rw [hxs] at ha' hb'
        exact
          (by
            rw [List.mem_cons] at ha'
            rcases ha' with rfl | h
            · rfl
            · exact absurd h List.not_mem_nil : a = x).trans
          (by
            rw [List.mem_cons] at hb'
            rcases hb' with rfl | h
            · rfl
            · exact absurd h List.not_mem_nil : x = b)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A finite set containing an element has positive cardinality. -/
theorem finset_card_pos_of_mem {α : Type} {S : Finset α} {a : α}
    (ha : a ∈ S) : 0 < S.card := by
  cases S with | mk v nd =>
  revert nd ha
  induction v using Multiset.ind with
  | _ l =>
    intro hnd ha
    change 0 < l.length
    have ha' : a ∈ l := ha
    cases l with
    | nil => exact absurd ha' List.not_mem_nil
    | cons _ _ => simp

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A negative singleton clause cannot equal a positive singleton clause. -/
theorem singleton_neg_ne_singleton_pos (P Q : Nat) :
    Clause.single (Literal.neg P) ≠ Clause.single (Literal.pos Q) := by
  intro hEq
  have hMem :
      Literal.neg P ∈ Clause.single (Literal.pos Q) := by
    rw [← hEq]
    exact (Finset.mem_singleton _ _).mpr rfl
  have hLit : Literal.neg P = Literal.pos Q :=
    (Finset.mem_singleton _ _).mp hMem
  exact Literal.noConfusion hLit

/-- The two-negative-literal side of the aliasing partition is not a
    singleton negative clause. -/
theorem singleton_neg_ne_expandedDepthAliasB (P : Nat) :
    Clause.single (Literal.neg P) ≠ expandedDepthAliasB := by
  intro hEq
  have hCard := congrArg (fun C : Clause => C.card) hEq
  have hSingleCard :
      (Clause.single (Literal.neg P)).card = 1 := by
    rfl
  have hBCard : expandedDepthAliasB.card = 2 := by
    native_decide
  omega

/-- The three-literal target is not a singleton negative clause. -/
theorem singleton_neg_ne_expandedDepthAliasTarget (P : Nat) :
    Clause.single (Literal.neg P) ≠ expandedDepthAliasTarget := by
  intro hEq
  have hCard := congrArg (fun C : Clause => C.card) hEq
  have hSingleCard :
      (Clause.single (Literal.neg P)).card = 1 := by
    rfl
  have hTargetCard : expandedDepthAliasTarget.card = 3 := by
    native_decide
  omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- No negative singleton clause occurs in the aliasing root sequent. -/
theorem singleton_neg_not_mem_expandedDepthAliasSequent (P : Nat) :
    Clause.single (Literal.neg P) ∉ expandedDepthAliasSequent := by
  intro hMem
  have hRoot :
      Clause.single (Literal.neg P) ∈ expandedDepthAliasGamma ∨
        Clause.single (Literal.neg P) ∈
          ClauseSequent.single expandedDepthAliasTarget :=
    (Finset.mem_union_exp _ _ _).mp hMem
  rcases hRoot with hGamma | hTarget
  · have hList :
        Clause.single (Literal.neg P) ∈
          [Clause.single (Literal.pos 1),
            Clause.single (Literal.pos 0),
            expandedDepthAliasB] := by
      exact (Finset.mem_ofList_exp _ _).mp hGamma
    rcases List.mem_cons.mp hList with hEq | hList
    · exact singleton_neg_ne_singleton_pos P 1 hEq
    · rcases List.mem_cons.mp hList with hEq | hList
      · exact singleton_neg_ne_singleton_pos P 0 hEq
      · have hEq : Clause.single (Literal.neg P) =
            expandedDepthAliasB :=
          List.mem_singleton.mp hList
        exact singleton_neg_ne_expandedDepthAliasB P hEq
  · have hEq : Clause.single (Literal.neg P) =
        expandedDepthAliasTarget :=
      (Finset.mem_singleton _ _).mp hTarget
    exact singleton_neg_ne_expandedDepthAliasTarget P hEq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A clause containing `+0` cannot be a negative singleton. -/
theorem union_aliasA_ne_singleton_neg (D : Clause) (P : Nat) :
    Clause.union expandedDepthAliasA D ≠
      Clause.single (Literal.neg P) := by
  intro hEq
  have hPos :
      Literal.pos 0 ∈ Clause.union expandedDepthAliasA D :=
    (Finset.mem_union_exp _ _ _).mpr
      (Or.inl ((Finset.mem_singleton _ _).mpr rfl))
  rw [hEq] at hPos
  have hLit : Literal.pos 0 = Literal.neg P :=
    (Finset.mem_singleton _ _).mp hPos
  exact Literal.noConfusion hLit

/-- The finite-set encoding loses enough occurrence information that charging
    a simultaneous node by `As.card` still cannot preserve the exact depth
    asserted by Lemma 9.2.2.  This is stronger than a failure of a particular
    permutation algorithm: no depth-two proof of this sequent can carry the
    requested two-literal root macro, even if the output proof uses weakening. -/
theorem expandedDepthAlias_no_root_partition_at_depth_two :
    ¬ ∃ T' : GCNFProofTree expandedDepthAliasSequent,
      RootPartitionCertificate T' expandedDepthAliasTarget
        expandedDepthAliasA expandedDepthAliasB ∧
      expandedDepth T' = 2 := by
  rintro ⟨T', hCertificate, hDepth⟩
  rcases hCertificate.rootedMacro with
    ⟨order, hOrderNodup, hOrder, hMacro⟩
  have hMembers :
      ∀ l, l ∈ order ↔
        l ∈ [Literal.neg 0, Literal.neg 1] := by
    intro l
    constructor
    · intro hl
      have hlClause : l ∈ Clause.ofList order :=
        (Finset.mem_ofList_exp _ _).mpr hl
      rw [hOrder] at hlClause
      exact (Finset.mem_ofList_exp _ _).mp hlClause
    · intro hl
      have hlClause :
          l ∈ Clause.ofList [Literal.neg 0, Literal.neg 1] :=
        (Finset.mem_ofList_exp _ _).mpr hl
      change l ∈ expandedDepthAliasB at hlClause
      rw [← hOrder] at hlClause
      exact (Finset.mem_ofList_exp _ _).mp hlClause
  have hPairNodup :
      [Literal.neg 0, Literal.neg 1].Nodup := by
    native_decide
  have hOrderPerm :
      order.Perm [Literal.neg 0, Literal.neg 1] :=
    list_perm_of_nodup_of_mem_iff
      hOrderNodup hPairNodup hMembers
  have hOrderLength : order.length = 2 := by
    simpa using hOrderPerm.length_eq
  cases order with
  | nil =>
      simp at hOrderLength
  | cons b bs =>
      cases bs with
      | nil =>
          simp at hOrderLength
      | cons b' bs' =>
          have hTailLength : bs'.length = 0 := by
            simp only [List.length_cons] at hOrderLength
            omega
          have hTailNil : bs' = [] :=
            List.length_eq_zero_iff.mp hTailLength
          subst bs'
          generalize hIndex : expandedDepthAliasSequent = S at T' hMacro hDepth
          cases T' with
          | axiom_ _ hOrd _ =>
              exact hMacro
          | rule G As pivot Cs G1 G2 hGammaOrd hAsOrd lT rT
              hCsNonempty hCsSub hG1Sub hG2Sub =>
              have hResidual :
                  Clause.union expandedDepthAliasA
                    (Clause.ofList [b']) ∈ Cs :=
                hMacro.2.1
              have hLeftMacro :
                  rootPartitionMacro expandedDepthAliasA lT [b'] :=
                hMacro.2.2
              clear hCertificate hMacro
              simp only [expandedDepth] at hDepth
              generalize hLeftIndex : Finset.union G1 Cs = SLeft at lT hLeftMacro hDepth
              cases lT with
              | axiom_ _ hOrd _ =>
                  exact hLeftMacro
              | rule G' As' pivot' Cs' G1' G2' hGammaOrd hAsOrd llT lrT
                  hCsNonempty' hCsSub' hG1Sub' hG2Sub' =>
                  have hASelected : expandedDepthAliasA ∈ Cs' :=
                    hLeftMacro.2
                  clear hLeftMacro
                  rcases hCsNonempty with ⟨D, hD⟩
                  have hAsPos : 0 < As.card :=
                    finset_card_pos_of_mem (hCsSub D hD)
                  rcases hCsNonempty' with ⟨D', hD'⟩
                  have hAsPos' : 0 < As'.card :=
                    finset_card_pos_of_mem (hCsSub' D' hD')
                  simp only [expandedDepth] at hDepth
                  have hInnerLe :
                      As'.card +
                          max (expandedDepth llT) (expandedDepth lrT) ≤
                        max
                          (As'.card +
                            max (expandedDepth llT) (expandedDepth lrT))
                          (expandedDepth rT) :=
                    Nat.le_max_left _ _
                  have hLLLe :
                      expandedDepth llT ≤
                        max (expandedDepth llT) (expandedDepth lrT) :=
                    Nat.le_max_left _ _
                  have hAsCard : As.card = 1 := by
                    omega
                  have hAsCard' : As'.card = 1 := by
                    omega
                  have hLLDepth : expandedDepth llT = 0 := by
                    omega
                  generalize hLLIndex : Finset.union G1' Cs' = SLL at llT hLLDepth
                  cases llT with
                  | rule G'' As'' pivot'' Cs'' G1'' G2'' hGammaOrd hAsOrd lllT llrT
                      hCsNonempty'' hCsSub'' hG1Sub'' hG2Sub'' =>
                      rcases hCsNonempty'' with ⟨D'', hD''⟩
                      have hAsPos'' : 0 < As''.card :=
                        finset_card_pos_of_mem (hCsSub'' D'' hD'')
                      simp only [expandedDepth] at hLLDepth
                      omega
                  | axiom_ _ hOrd hTrivial =>
                      rcases hTrivial with
                        ⟨P, _hPositive, hNegative⟩
                      have hNegativeLeftPremise :
                          Clause.single (Literal.neg P) ∈
                            Finset.union G1' Cs' := by
                        rw [hLLIndex]
                        exact hNegative
                      have hNegativeSplit :
                          Clause.single (Literal.neg P) ∈ G1' ∨
                            Clause.single (Literal.neg P) ∈ Cs' :=
                        (Finset.mem_union_exp _ _ _).mp
                          hNegativeLeftPremise
                      rcases hNegativeSplit with
                        hNegativeG1' | hNegativeCs'
                      · have hNegativeInnerConclusion :=
                          hG1Sub'
                            (Clause.single (Literal.neg P))
                            hNegativeG1'
                        have hNegativeRootLeftPremise :
                            Clause.single (Literal.neg P) ∈
                              Finset.union G1 Cs := by
                          rw [hLeftIndex]
                          exact hNegativeInnerConclusion
                        have hNegativeRootLeft :
                            Clause.single (Literal.neg P) ∈ G1 ∨
                              Clause.single (Literal.neg P) ∈ Cs :=
                          (Finset.mem_union_exp _ _ _).mp
                            hNegativeRootLeftPremise
                        rcases hNegativeRootLeft with
                          hNegativeG1 | hNegativeCs
                        · have hNegativeRoot :=
                            hG1Sub
                              (Clause.single (Literal.neg P))
                              hNegativeG1
                          have hNegativeAliasRoot :
                              Clause.single (Literal.neg P) ∈
                                expandedDepthAliasSequent := by
                            rw [hIndex]
                            exact hNegativeRoot
                          exact
                            singleton_neg_not_mem_expandedDepthAliasSequent
                              P hNegativeAliasRoot
                        · have hNegativeAs :=
                            hCsSub
                              (Clause.single (Literal.neg P))
                              hNegativeCs
                          have hResidualAs :=
                            hCsSub _ hResidual
                          have hEq :
                              Clause.single (Literal.neg P) =
                                Clause.union expandedDepthAliasA
                                  (Clause.ofList [b']) :=
                            finset_card_one_elements_eq hAsCard _ _
                              hNegativeAs hResidualAs
                          exact
                            union_aliasA_ne_singleton_neg
                              (Clause.ofList [b']) P hEq.symm
                      · have hNegativeAs' :=
                          hCsSub'
                            (Clause.single (Literal.neg P))
                            hNegativeCs'
                        have hAAs' :=
                          hCsSub' _ hASelected
                        have hEq :
                            Clause.single (Literal.neg P) =
                              expandedDepthAliasA :=
                          finset_card_one_elements_eq hAsCard' _ _
                            hNegativeAs' hAAs'
                        exact singleton_neg_ne_singleton_pos P 0
                          (by simpa [expandedDepthAliasA] using hEq)
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Under IsStrictIWW and axiomsAllSingleLiteral, every clause in the root
    sequent is nonempty. This is because empty clauses propagate through
    Gamma (which equals Gamma1 = Gamma2 in IsStrictIWW) all the way to
    axiom leaves, contradicting axiomsAllSingleLiteral. -/
theorem root_clauses_nonempty {S : ClauseSequent} (T : GCNFProofTree S)
    (hWk : IsStrictIWW T) (hMin : T.axiomsAllSingleLiteral) :
    ∀ C ∈ S, ∃ L : Literal, L ∈ C := by
-- BEGIN PROOF
  induction T with
  | axiom_ S' hOrd hTriv =>
    intro C hC; obtain ⟨L, rfl⟩ := hMin C hC
    exact ⟨L, (Finset.mem_singleton L L).mpr rfl⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGammaOrd hAsOrd leftTree rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
    intro C hC; rw [Finset.mem_union] at hC
    rcases hC with hG | hMap
    · exact ihL hWk.2.2.2.1 hMin.1 C
        ((Finset.mem_union_exp C _ _).mpr (Or.inl (hWk.2.1 ▸ hG)))
    · obtain ⟨A, _, rfl⟩ := (mem_image_iff _ _ _).mp hMap
      exact ⟨B, (Finset.mem_insert_exp B B A).mpr (Or.inl rfl)⟩

-- ========= Lemma 9.2.3: Axiom labeling structure =========




/-- Lemma 9.2.3: Each actual leaf of a weakening-free, genuine GCNF' proof
    with literal axioms is exactly the selected singleton clauses together
    with the unit clauses J. One literal is selected from each nonunit root
    clause; the finite-set image collapses repeated selections. -/
@[blueprint "chap9__lemma_9_2_3" (main := true)]
theorem axiom_labeling_structure (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hWk : IsStrictIWW T)
    (hGen : GenuineDecompositions T)
    (hMin : T.axiomsAllSingleLiteral) :
    let multiClauses := multiLiteralClauses S
    let J := oneLiteralClauses S
    ∀ (leaf : ClauseSequent), leaf ∈ axiomLeaves T →
      ∃ select : Clause → Literal,
        (∀ C ∈ multiClauses, select C ∈ C) ∧
        leaf = Finset.union
          (ClauseSequent.mapSet multiClauses (fun C => Clause.single (select C))) J 


-- ========= Lemma 9.2.4: Horn provable requires positive and goal =========

/-- Lemma 9.2.4: If a Horn clause set S is GCNF'-provable, then S contains at least one
    single positive literal clause and at least one goal (negative) clause. -/
@[blueprint "chap9__lemma_9_2_4" (main := true)]
theorem horn_provable_has_positive_and_goal (S : ClauseSequent)
    (hHorn : ∀ C ∈ S, isHornClause C)
    (hProv : GCNFProvable S) :
    (∃ P : Nat, Clause.single (Literal.pos P) ∈ S) ∧
    (∃ goal ∈ S, isGoalClause goal) 

-- ========= Helpers for Lemma 9.2.5: Horn clause model combination =========

-- Intersection of models preserves definite clause satisfaction.
-- Uses the Horn property: at most one positive literal.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem definite_clause_and (C : Clause) (hDef : isDefiniteClause C)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy C v) (hw : Clause.satisfiedBy C w) :
    Clause.satisfiedBy C (fun n => v n && w n) := by
-- BEGIN PROOF
  obtain ⟨Lv, hLv, hSatLv⟩ := hv
  cases Lv with
  | neg Pv => exact ⟨_, hLv, by simp [Literal.satisfiedBy] at hSatLv ⊢; rw [hSatLv]; simp⟩
  | pos Pv =>
    obtain ⟨Lw, hLw, hSatLw⟩ := hw
    cases Lw with
    | neg Pw => exact ⟨_, hLw, by simp [Literal.satisfiedBy] at hSatLw ⊢; rw [hSatLw]; simp⟩
    | pos Pw =>
      rw [hDef.1.2 Pv Pw hLv hLw] at hSatLv
      exact ⟨_, hLw, by simp [Literal.satisfiedBy] at *; rw [hSatLv, hSatLw]; simp⟩

-- Goal clause satisfaction is antimonotone under valuation intersection:
-- if v satisfies goal N, then (v AND w) also satisfies N.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem goal_and_sat (N : Clause) (hGoal : isGoalClause N)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy N v) :
    Clause.satisfiedBy N (fun n => v n && w n) := by
-- BEGIN PROOF
  obtain ⟨L, hL, hSat⟩ := hv
  cases L with
  | pos _ => exact absurd (hGoal.2 _ hL) (by simp)
  | neg P => exact ⟨_, hL, by simp [Literal.satisfiedBy] at hSat ⊢; rw [hSat]; simp⟩

-- Symmetric version: (w AND v) also satisfies N.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem goal_and_sat_right (N : Clause) (hGoal : isGoalClause N)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy N v) :
    Clause.satisfiedBy N (fun n => w n && v n) := by
-- BEGIN PROOF
  obtain ⟨L, hL, hSat⟩ := hv
  cases L with
  | pos _ => exact absurd (hGoal.2 _ hL) (by simp)
  | neg P => exact ⟨_, hL, by simp [Literal.satisfiedBy] at hSat ⊢; rw [hSat]; simp⟩

-- Valuation intersection preserves satisfaction of JD = J ∪ defs
-- (positive singletons and definite clauses).
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem jd_and_sat (JD : ClauseSequent)
    (hJD : ∀ C ∈ JD, (∃ P : Nat, C = Clause.single (Literal.pos P)) ∨ isDefiniteClause C)
    (v w : Nat → Bool) (hv : ClauseSequent.satisfiedBy JD v) (hw : ClauseSequent.satisfiedBy JD w) :
    ClauseSequent.satisfiedBy JD (fun n => v n && w n) := by
-- BEGIN PROOF
  intro C hC
  rcases hJD C hC with ⟨P, rfl⟩ | hDef
  · have hvC := hv _ hC; have hwC := hw _ hC
    obtain ⟨L, hL, hSat⟩ := hvC; have := (Finset.mem_singleton L _).mp hL; subst this
    obtain ⟨L', hL', hSat'⟩ := hwC; have := (Finset.mem_singleton L' _).mp hL'; subst this
    exact ⟨_, (Finset.mem_singleton _ _).mpr rfl,
      by simp [Literal.satisfiedBy] at *; rw [hSat, hSat']; simp⟩
  · exact definite_clause_and C hDef v w (hv C hC) (hw C hC)

-- If each single-goal subset is satisfiable, then JD ∪ (all goals) is satisfiable.
-- Proved by iterated model combination (binary AND of valuations).
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem horn_all_goals_sat_of_each_sat
    (JD : ClauseSequent) (goals : List Clause)
    (hJD : ∀ C ∈ JD, (∃ P : Nat, C = Clause.single (Literal.pos P)) ∨ isDefiniteClause C)
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNe : goals ≠ [])
    (hEach : ∀ i : Fin goals.length, ∃ v : Nat → Bool,
      ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (goals.get i) v) :
    ∃ v : Nat → Bool, ClauseSequent.satisfiedBy JD v ∧ ∀ g ∈ goals, Clause.satisfiedBy g v := by
-- BEGIN PROOF
  induction goals with
  | nil => exact absurd rfl hGoalsNe
  | cons g gs ih =>
    have hv0 := hEach ⟨0, by simp⟩; simp at hv0
    obtain ⟨v0, hv0JD, hv0g⟩ := hv0
    by_cases hgs : gs = []
    · subst hgs
      refine ⟨v0, hv0JD, fun g' hg' => ?_⟩
      rw [List.mem_cons] at hg'; rcases hg' with rfl | h
      · exact hv0g
      · exact absurd h List.not_mem_nil
    · have hGoalsGS : ∀ C ∈ gs, isGoalClause C :=
        fun C hC => hGoals C (List.mem_cons.mpr (Or.inr hC))
      have hSatGS : ∀ i : Fin gs.length, ∃ v,
          ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (gs.get i) v := by
        intro ⟨i, hi⟩
        have h := hEach ⟨i + 1, by simp; exact hi⟩
        simpa using h
      obtain ⟨vc, hvcJD, hvcgs⟩ := ih hGoalsGS hgs hSatGS
      refine ⟨fun n => vc n && v0 n, jd_and_sat JD hJD vc v0 hvcJD hv0JD, fun g' hg' => ?_⟩
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hgs'
      · exact goal_and_sat_right g' (hGoals g' (List.mem_cons.mpr (Or.inl rfl))) v0 vc hv0g
      · exact goal_and_sat g' (hGoalsGS g' hgs') vc v0 (hvcgs g' hgs')

-- ========= Helpers for Lemma 9.2.5 Part (b): depth-preserving weakening =========

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- proofDepth is invariant under Eq.rec transport of the ClauseSequent index. -/
theorem proofDepth_eq_transport {S S' : ClauseSequent} (h : S = S') (T : GCNFProofTree S) :
    proofDepth (h ▸ T : GCNFProofTree S') = proofDepth T := by
-- BEGIN PROOF
  cases h; rfl

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Depth-preserving weakening: if T proves S with depth ≤ n, then S ∪ D has a proof
    with depth ≤ n. This is the structural version of gcnf_admissible_weakening that
    preserves the depth bound. -/
theorem gcnf_weakening_bounded (n : Nat) :
    ∀ (S : ClauseSequent) (T : GCNFProofTree S) (D : ClauseSequent),
    D.isOrdinary → proofDepth T ≤ n →
    ∃ T' : GCNFProofTree (Finset.union S D), proofDepth T' ≤ n := by
-- BEGIN PROOF
  induction n with
  | zero =>
    intro S T D hD hd
    match T, hd with
    | .axiom_ S hOrd hTriv, _ =>
      obtain ⟨P, hP, hN⟩ := hTriv
      exact ⟨.axiom_ _ (ClauseSequent.ordinary_union hOrd hD) ⟨P, (Finset.mem_union_exp _ S D).mpr (Or.inl hP),
        (Finset.mem_union_exp _ S D).mpr (Or.inl hN)⟩, by simp [proofDepth]⟩
    | .rule _ _ _ _ _ _ hGammaOrd hAsOrd _ _ _ _ _ _, hd => simp [proofDepth] at hd
  | succ n ih =>
    intro S T D hD hd
    match T, hd with
    | .axiom_ S hOrd hTriv, _ =>
      obtain ⟨P, hP, hN⟩ := hTriv
      exact ⟨.axiom_ _ (ClauseSequent.ordinary_union hOrd hD) ⟨P, (Finset.mem_union_exp _ S D).mpr (Or.inl hP),
        (Finset.mem_union_exp _ S D).mpr (Or.inl hN)⟩, by simp [proofDepth]⟩
    | .rule G As B Cs G1 G2 hGammaOrd hAsOrd lT rT hNe hSub hG1 hG2, hd =>
      have hlT : proofDepth lT ≤ n := by simp [proofDepth] at hd; omega
      have hrT : proofDepth rT ≤ n := by simp [proofDepth] at hd; omega
      obtain ⟨lT', hlD⟩ := ih _ lT D hD hlT
      obtain ⟨rT', hrD⟩ := ih _ rT D hD hrT
      have hEqL := finset_union_right_comm G1 Cs D
      have hEqR := finset_union_right_comm G2 (ClauseSequent.single (Clause.single B)) D
      have hEqC := finset_union_right_comm G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) D
      refine ⟨hEqC.symm ▸
        (.rule (Finset.union G D) As B Cs (Finset.union G1 D) (Finset.union G2 D)
          (ClauseSequent.ordinary_union hGammaOrd hD) hAsOrd
          (hEqL ▸ lT') (hEqR ▸ rT')
          hNe hSub (subset_weaken_union G1 G D _ hG1) (subset_weaken_union G2 G D _ hG2)), ?_⟩
      rw [proofDepth_eq_transport hEqC.symm, proofDepth,
          proofDepth_eq_transport hEqL, proofDepth_eq_transport hEqR]
      omega

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Depth-preserving superset weakening: if T proves S with depth ≤ n and S ⊆ S',
    then S' has a proof with depth ≤ n. -/
theorem gcnf_superset_bounded (S S' : ClauseSequent)
    (hSub : ∀ C, C ∈ S → C ∈ S')
    (T : GCNFProofTree S) (n : Nat) (hd : proofDepth T ≤ n) (hOrd : S'.isOrdinary) :
    ∃ T' : GCNFProofTree S', proofDepth T' ≤ n := by
-- BEGIN PROOF
  have hEq : S' = Finset.union S S' := by
    apply Finset.ext; intro C; rw [Finset.mem_union]
    exact ⟨fun hC => Or.inr hC, fun h => h.elim (hSub C) id⟩
  obtain ⟨T', hd'⟩ := gcnf_weakening_bounded n S T S' hOrd hd
  exact ⟨hEq ▸ T', by rw [proofDepth_eq_transport]; exact hd'⟩

-- ========= Helpers for Lemma 9.2.5 Part (b): Horn clause partition =========

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- IsStrictIWW is preserved by Eq.rec transport. -/
theorem IsStrictIWW_transport {S S' : ClauseSequent} (h : S = S') (T : GCNFProofTree S)
    (hIWW : IsStrictIWW T) : IsStrictIWW (h ▸ T) := by cases h; exact hIWW

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Occurrence.Part1, LCS.SLD.SLDForm.Occurrence.Part2
/-- axiomsAllSingleLiteral is preserved by Eq.rec transport. -/
theorem axiomsAllSingleLiteral_transport {S S' : ClauseSequent} (h : S = S') (T : GCNFProofTree S)
    (hLit : T.axiomsAllSingleLiteral) : (h ▸ T).axiomsAllSingleLiteral := by cases h; exact hLit

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton negative clause is a goal clause. -/
theorem singleton_neg_is_goal (P : Nat) : isGoalClause (Clause.single (Literal.neg P)) := by
  constructor
  · refine ⟨Clause.single_ordinary _, ?_⟩
    intro Q R hQ hR
    exact absurd ((Finset.mem_singleton _ _).mp hQ) Literal.noConfusion
  · intro l hl
    have := (Finset.mem_singleton _ _).mp hl; subst this; trivial

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Bool-valued test: is C ordinary and all-negative? -/
def isGoalClauseB (C : Clause) : Bool :=
  decide (C ≠ Clause.empty) && allNegativeB C

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- isGoalClauseB is sound for isGoalClause. -/
theorem isGoalClauseB_sound (C : Clause) (h : isGoalClauseB C = true) : isGoalClause C := by
  simp only [isGoalClauseB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hOrd, hNeg⟩ := h
  have hn := allNegativeB_spec C hNeg
  exact ⟨⟨hOrd, fun P Q hP _ => False.elim (hn _ hP)⟩, hn⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The ordinary goal test accepts every goal clause. -/
theorem isGoalClauseB_complete (C : Clause) (h : isGoalClause C) : isGoalClauseB C = true := by
  simp only [isGoalClauseB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1.1, allNegativeB_of_goal h⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of goal clauses (Bool filter). -/
def goalFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter isGoalClauseB S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of non-goal clauses with card > 1. -/
def defFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => !isGoalClauseB C && decide (1 < C.card)) S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of non-goal clauses with card ≤ 1. -/
def jFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => !isGoalClauseB C && !decide (1 < C.card)) S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Every clause in S belongs to exactly one of goalFilter, defFilter, jFilter. -/
theorem filter_trichotomy (S : ClauseSequent) (C : Clause) (hC : C ∈ S) :
    C ∈ goalFilter S ∨ C ∈ defFilter S ∨ C ∈ jFilter S := by
-- BEGIN PROOF
  by_cases hG : isGoalClauseB C = true
  · exact Or.inl ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, hG⟩)
  · by_cases hD : decide (1 < C.card) = true
    · exact Or.inr (Or.inl ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, by simp [hG, hD]⟩))
    · exact Or.inr (Or.inr ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, by simp [hG, hD]⟩))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The three filters cover S. -/
theorem filter_covers (S : ClauseSequent) :
    S = Finset.union (Finset.union (jFilter S) (defFilter S)) (goalFilter S) := by
-- BEGIN PROOF
  apply Finset.ext; intro C
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · intro hC
    rcases filter_trichotomy S C hC with hG | hD | hJ
    · exact Or.inr hG
    · exact Or.inl (Or.inr hD)
    · exact Or.inl (Or.inl hJ)
  · intro hC
    rcases hC with (hJ | hD) | hG
    · exact ((Finset.mem_filter_exp _ _ _).mp hJ).1
    · exact ((Finset.mem_filter_exp _ _ _).mp hD).1
    · exact ((Finset.mem_filter_exp _ _ _).mp hG).1

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Helper: if a Finset has card 1, all elements are equal to any given member. -/
theorem card_one_all_eq (C : Clause) (hCard : C.card = 1) (a b : Literal)
    (ha : a ∈ C) (hb : b ∈ C) : a = b :=
-- BEGIN PROOF
  finset_card_one_eq hCard a b ha hb

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Clauses in jFilter are unit positive literals (for nonempty Horn clauses). -/
theorem jFilter_unit_pos (S : ClauseSequent)
    (hHorn : ∀ C ∈ S, isHornClause C) (hNe : ∀ C ∈ S, ∃ L : Literal, L ∈ C) :
    ∀ C ∈ jFilter S, ∃ P : Nat, C = Clause.single (Literal.pos P) := by
-- BEGIN PROOF
  intro C hC
  have ⟨hCS, hPred⟩ := (Finset.mem_filter_exp _ _ _).mp hC
  have hNotGoal : isGoalClauseB C = false := by
    cases hv : isGoalClauseB C
    · rfl
    · simp [hv] at hPred
  have hSmall : ¬(1 < C.card) := by
    cases hv : decide (1 < C.card) with
    | true => simp [hNotGoal, hv] at hPred
    | false => exact of_decide_eq_false hv
  obtain ⟨L, hL⟩ := hNe C hCS
  have hCard1 : C.card = 1 := by
    have hPos : 1 ≤ C.card := by
      show 1 ≤ C.val.card
      cases C with | mk v nd =>
      induction v using Multiset.ind with
      | _ lst =>
        have hL' : L ∈ lst := hL
        show 1 ≤ lst.length
        cases hv : lst with
        | nil => rw [hv] at hL'; exact absurd hL' List.not_mem_nil
        | cons _ _ => simp [List.length]
    omega
  match L with
  | .neg P =>
    exfalso
    have hGoalB : isGoalClauseB C = true := by
      rw [isGoalClauseB, Bool.and_eq_true]
      refine ⟨decide_eq_true (hHorn C hCS).1, ?_⟩
      apply Multiset.all_eq_true.mpr; intro l hl
      have := card_one_all_eq C hCard1 l (Literal.neg P) hl hL
      subst this; rfl
    rw [hGoalB] at hNotGoal; exact absurd hNotGoal (by decide)
  | .pos P =>
    refine ⟨P, ?_⟩
    apply Finset.ext; intro l; constructor
    · intro hl
      exact (Finset.mem_singleton _ _).mpr (card_one_all_eq C hCard1 l (Literal.pos P) hl hL)
    · intro hl; rw [(Finset.mem_singleton _ _).mp hl]; exact hL

end LCS.SLD.SLDForm.Completeness
end


attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Completeness.rootPartitionMacro
