import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF
import Attach
import LCS.SLD.SLDForm.Occurrence.Compression.ProofsStamp

/-! # Compression to finite-set GCNF' proofs

Derivations rooted at extensional clause sequents, finite-set erasure of occurrences, and the one-way compression of occurrence proofs to `GCNFProofTree` with its depth and axiom invariants. -/

section
namespace LCS.SLD.SLDForm.Occurrence
open LCS.Resolution.GCNF

/-- An occurrence-preserving derivation of an extensional clause sequent.
The root list is duplicate-free, so it contains exactly one occurrence for
each clause in `S`; internal rule premises may contain equal clauses at
different positions and intentionally retain that multiplicity. -/
structure OccurrenceGCNFDerivation (S : ClauseSequent) where
  occurrences : List Clause
  nodupRoot : occurrences.Nodup
  erase_eq : ClauseSequent.ofList occurrences = S
  tree : OccurrenceGCNFProof occurrences

/-- Erase occurrence multiplicity from a clause list. -/
@[blueprint "chap9__lemma_9_2_2"]
def eraseOccurrences (clauses : List Clause) : ClauseSequent :=
  ClauseSequent.ofList clauses

/-- Erasure preserves exactly list membership, while forgetting duplicate
occurrences. -/
theorem mem_eraseOccurrences_iff (clauses : List Clause) (C : Clause) :
    C ∈ eraseOccurrences clauses ↔ C ∈ clauses :=
  LCS.Finset.mem_ofList_exp C clauses

/-- The chosen list representative of a finite set is duplicate-free. -/
theorem clauseSequent_toList_nodup (S : ClauseSequent) :
    S.toList.Nodup := by
  have hNodup : S.val.Nodup := S.nodup
  rw [← S.toList_ofList_eq] at hNodup
  exact hNodup

/-- Erasing the chosen list representative recovers the original finite set. -/
theorem eraseOccurrences_toList (S : ClauseSequent) :
    eraseOccurrences S.toList = S := by
  apply LCS.Finset.ext
  intro C
  rw [mem_eraseOccurrences_iff, LCS.Finset.mem_toList]

/-! ## One-way compression to the existing GCNF' carrier -/

/-- Transport a finite-set GCNF' proof along equality of its indexed root.
Keeping this operation local makes the casts inserted by compression explicit. -/
def transportGCNFProofTree {S S' : ClauseSequent}
    (h : S = S') (T : GCNFProofTree S) :
    GCNFProofTree S' :=
  h ▸ T

/-- The image of a singleton principal set is the singleton containing the
corresponding extended clause. -/
theorem mapSet_singleton_clauseWithLiteral
    (A : Clause) (B : Literal) :
    ClauseSequent.mapSet (ClauseSequent.single A)
        (fun C => clauseWithLiteral C B) =
      ClauseSequent.single (clauseWithLiteral A B) := by
  apply LCS.Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨A', hA', hEq⟩ :=
      (mem_image_iff
        (fun X => clauseWithLiteral X B)
        (ClauseSequent.single A) C).mp hC
    have hAeq : A' = A :=
      (mem_csingle A' A).mp hA'
    subst A'
    exact (mem_csingle C (clauseWithLiteral A B)).mpr hEq.symm
  · intro hC
    have hEq : C = clauseWithLiteral A B :=
      (mem_csingle C (clauseWithLiteral A B)).mp hC
    exact
      (mem_image_iff
        (fun X => clauseWithLiteral X B)
        (ClauseSequent.single A) C).mpr
        ⟨A, (mem_csingle A A).mpr rfl, hEq.symm⟩

/-- Compress an occurrence proof to the existing finite-set GCNF' proof tree.
Literal-only axiom leaves certify ordinariness of every clause used in the
compressed tree. Every occurrence rule becomes a singleton-`As`, singleton-`Cs`
rule with the same context in both premises. -/
@[blueprint "chap9__lemma_9_2_2"]
def compress :
    {clauses : List Clause} →
    (T : OccurrenceGCNFProof clauses) →
    T.axiomsAllSingleLiteral →
    GCNFProofTree (eraseOccurrences clauses)
  | _, .axiom_ clauses hTriv, hLeaves => by
      exact
        .axiom_ (eraseOccurrences clauses)
          (by
            intro C hC
            obtain ⟨L, rfl⟩ := hLeaves C ((mem_eraseOccurrences_iff clauses C).mp hC)
            exact Clause.single_ordinary L)
          (by
            rcases hTriv with ⟨P, hPos, hNeg⟩
            exact
              ⟨P,
                (mem_eraseOccurrences_iff clauses
                  (Clause.single (Literal.pos P))).mpr hPos,
                (mem_eraseOccurrences_iff clauses
                  (Clause.single (Literal.neg P))).mpr hNeg⟩)
  | _, .rule pre post A B left right, hLeaves => by
      let Gamma : ClauseSequent :=
        eraseOccurrences (pre ++ post)
      have hLeft :
          eraseOccurrences (pre ++ A :: post) =
            LCS.Finset.union Gamma (ClauseSequent.single A) :=
        ofList_replace_eq_union pre post A
      have hRight :
          eraseOccurrences (pre ++ Clause.single B :: post) =
            LCS.Finset.union Gamma
              (ClauseSequent.single (Clause.single B)) :=
        ofList_replace_eq_union pre post (Clause.single B)
      have hConclusion :
          eraseOccurrences
              (pre ++ clauseWithLiteral A B :: post) =
            LCS.Finset.union Gamma
              (ClauseSequent.mapSet (ClauseSequent.single A)
                (fun C => clauseWithLiteral C B)) := by
        rw [mapSet_singleton_clauseWithLiteral]
        exact ofList_replace_eq_union pre post
          (clauseWithLiteral A B)
      let leftTree :
          GCNFProofTree
            (LCS.Finset.union Gamma (ClauseSequent.single A)) :=
        transportGCNFProofTree hLeft (compress left hLeaves.1)
      let rightTree :
          GCNFProofTree
            (LCS.Finset.union Gamma
              (ClauseSequent.single (Clause.single B))) :=
        transportGCNFProofTree hRight (compress right hLeaves.2)
      let ruleTree :
          GCNFProofTree
            (LCS.Finset.union Gamma
              (ClauseSequent.mapSet (ClauseSequent.single A)
                (fun C => clauseWithLiteral C B))) :=
        .rule Gamma (ClauseSequent.single A) B
          (ClauseSequent.single A) Gamma Gamma
          (ClauseSequent.ordinary_subset leftTree.ordinary
            (fun C hC => LCS.Finset.mem_union.mpr (Or.inl hC)))
          (ClauseSequent.ordinary_subset leftTree.ordinary
            (fun C hC => LCS.Finset.mem_union.mpr (Or.inr hC)))
          leftTree rightTree
          ⟨A, (mem_csingle A A).mpr rfl⟩
          (fun _ hC => hC)
          (fun _ hC =>
            (LCS.Finset.mem_union_exp _ Gamma _).mpr
              (Or.inl hC))
          (fun _ hC =>
            (LCS.Finset.mem_union_exp _ Gamma _).mpr
              (Or.inl hC))
      exact transportGCNFProofTree hConclusion.symm ruleTree

/-! ## Compression invariants available below `Completeness` -/

/-- Chapter-9-local structural predicate saying that every compressed rule is
unary and uses exactly the same context in both premises.  Axiom nodes have no
rule-shape obligation. -/
def IsUnaryOccurrenceCompression :
    {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _ _ => True
  | _, .rule Gamma As _B Cs Gamma1 Gamma2 _ _ left right _ _ _ _ =>
      (∃ A : Clause,
        As = ClauseSequent.single A ∧
        Cs = ClauseSequent.single A) ∧
      Gamma1 = Gamma ∧
      Gamma2 = Gamma ∧
      IsUnaryOccurrenceCompression left ∧
      IsUnaryOccurrenceCompression right

theorem isUnaryOccurrenceCompression_transport
    {S S' : ClauseSequent} (h : S = S')
    (T : GCNFProofTree S) :
    IsUnaryOccurrenceCompression
        (transportGCNFProofTree h T) ↔
      IsUnaryOccurrenceCompression T := by
  subst S'
  rfl

theorem axiomsAllSingleLiteral_transport
    {S S' : ClauseSequent} (h : S = S')
    (T : GCNFProofTree S) :
    GCNFProofTree.axiomsAllSingleLiteral
        (transportGCNFProofTree h T) ↔
      GCNFProofTree.axiomsAllSingleLiteral T := by
  subst S'
  rfl

/-- Compression always has the exact singleton/no-weakening rule shape. -/
theorem compress_isUnaryOccurrenceCompression
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    (hLeaves : T.axiomsAllSingleLiteral) :
    IsUnaryOccurrenceCompression (compress T hLeaves) := by
  revert hLeaves
  induction T with
  | axiom_ =>
      intro hLeaves
      simp [compress, IsUnaryOccurrenceCompression]
  | rule pre post A B left right ihLeft ihRight =>
      intro hLeaves
      simp only [compress]
      rw [isUnaryOccurrenceCompression_transport]
      simp only [IsUnaryOccurrenceCompression]
      refine
        ⟨⟨A, rfl, rfl⟩, trivial, trivial, ?_, ?_⟩
      · exact
          (isUnaryOccurrenceCompression_transport
            (ofList_replace_eq_union pre post A)
            (compress left hLeaves.1)).2 (ihLeft hLeaves.1)
      · exact
          (isUnaryOccurrenceCompression_transport
            (ofList_replace_eq_union pre post
              (Clause.single B))
            (compress right hLeaves.2)).2 (ihRight hLeaves.2)

/-- Compression preserves the literal-only axiom condition. -/
theorem compress_axiomsAllSingleLiteral
    {clauses : List Clause}
    (T : OccurrenceGCNFProof clauses)
    (hLeaves : T.axiomsAllSingleLiteral) :
    GCNFProofTree.axiomsAllSingleLiteral (compress T hLeaves) := by
  revert hLeaves
  induction T with
  | axiom_ root hTriv =>
      intro hLeaves
      intro C hC
      exact
        hLeaves C
          ((mem_eraseOccurrences_iff root C).mp hC)
  | rule pre post A B left right ihLeft ihRight =>
      intro hLeaves
      simp only [OccurrenceGCNFProof.axiomsAllSingleLiteral] at hLeaves
      simp only [compress]
      rw [axiomsAllSingleLiteral_transport]
      simp only [GCNFProofTree.axiomsAllSingleLiteral]
      constructor
      · apply
          (axiomsAllSingleLiteral_transport
            (ofList_replace_eq_union pre post A)
            (compress left hLeaves.1)).2
        exact ihLeft hLeaves.1
      · apply
          (axiomsAllSingleLiteral_transport
            (ofList_replace_eq_union pre post
              (Clause.single B))
            (compress right hLeaves.2)).2
        exact ihRight hLeaves.2

namespace OccurrenceGCNFDerivation

/-- Compress a root derivation to a finite-set GCNF' proof of the same
extensional sequent. -/
def compress {S : ClauseSequent}
    (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    GCNFProofTree S :=
  transportGCNFProofTree D.erase_eq
    (Occurrence.compress D.tree hD)

theorem compress_isUnaryOccurrenceCompression
    {S : ClauseSequent} (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    IsUnaryOccurrenceCompression (D.compress hD) :=
  (isUnaryOccurrenceCompression_transport D.erase_eq
    (Occurrence.compress D.tree hD)).2
    (Occurrence.compress_isUnaryOccurrenceCompression D.tree hD)

theorem compress_axiomsAllSingleLiteral
    {S : ClauseSequent} (D : OccurrenceGCNFDerivation S)
    (hD : D.tree.axiomsAllSingleLiteral) :
    GCNFProofTree.axiomsAllSingleLiteral (D.compress hD) :=
  (Occurrence.axiomsAllSingleLiteral_transport D.erase_eq
    (Occurrence.compress D.tree hD)).2
    (Occurrence.compress_axiomsAllSingleLiteral D.tree hD)

end OccurrenceGCNFDerivation
end LCS.SLD.SLDForm.Occurrence
end
