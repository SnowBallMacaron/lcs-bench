import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings
import Attach
import LCS.SLD.SLDForm.Completeness.PermutationLemma.ProofsStamp

/-! # The permutation lemma (Lemma 9.2.2)

Section 9.2.3: proof depth, the derived root macro for a clause partition `C = A ∪ B`, permuting the inferences for a multi-literal clause to the root, the depth-preserving weakening facts, and the occurrence-aliasing regression showing why exact expanded depth is not preserved. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- ========= Helper defs for Lemma 9.2.2: proof depth =========

/-- Lemma 9.2.2 (companion): The depth of a GCNFProofTree, defined as
    the maximum number of rule applications on any root-to-leaf path.
    Axioms have depth 0; the rule node has depth 1 + max of subtrees. -/
@[blueprint "chap9__lemma_9_2_2"]
def proofDepth : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ hOrd _ => 0
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd leftTree rightTree _ _ _ _ =>
    1 + max (proofDepth leftTree) (proofDepth rightTree)

-- ========= StrictIWW + axiomsAllSingleLiteral construction =========
-- Parallel construction retained under the compatibility name IsStrictIWW.
-- Key insight: the all-singletons base case uses a single axiom_ node
-- (vacuously StrictIWW), and the inductive step (ofList_strict_step)
-- always sets Gamma1 = Gamma2 = Gamma.













-- ========= Internal encoding of an arbitrary root partition =========

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

-- ========= Lemma 9.2.2: Permutation at root =========

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

end LCS.SLD.SLDForm.Completeness
end

attribute [blueprint "chap9__lemma_9_2_2"] LCS.SLD.SLDForm.Completeness.rootPartitionMacro

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

/-- Lemma 9.2.2 (companion, ∨:left invertibility for GCNF'): If S is
    GCNF'-provable and contains a clause of the form `clauseWithLiteral B'' Q`
    (i.e., B'' ∨ Q), then both sub-sequents obtained by replacing that clause
    with B'' (the left premise) or with {Q} (the right premise) are
    GCNF'-provable. Requires the non-emptiness side conditions needed for
    completeness: B'' is non-empty, and every clause in
    S.erase(clauseWithLiteral B'' Q) is non-empty. -/
@[blueprint "chap9__lemma_9_2_2"]
theorem gcnf_provable_clause_split
    (S : ClauseSequent)
    (B'' : Clause) (Q : Literal)
    (hCwlMem : clauseWithLiteral B'' Q ∈ S)
    (hB''ne : B'' ≠ Clause.empty)
    (hGammaNe : ∀ C ∈ Finset.erase S (clauseWithLiteral B'' Q), C ≠ Clause.empty)
    (hProv : GCNFProvable S) :
    GCNFProvable
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B'')) ∧
    GCNFProvable
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q))) 

end LCS.SLD.SLDForm.Completeness
end
