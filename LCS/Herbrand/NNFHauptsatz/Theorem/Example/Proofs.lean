import LCS.Herbrand.NNFHauptsatz.Theorem.Example

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

helper theorem nnfHauptExMidFinsetQuantifierFree :
    (∀ A, A ∈ nnfHauptExMidGamma →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, A ∈ nnfHauptExDelta →
      FirstOrder.SemanticsN.isQuantifierFree A) := by
  constructor
  · intro A hA
    change A ∈ LCS.Finset.insert nnfHauptEx_midAnt1
      (LCS.Finset.insert nnfHauptEx_midAnt2
        LCS.Finset.empty) at hA
    rcases LCS.Finset.mem_insert.mp hA with rfl | hA
    · exact ⟨trivial, ⟨trivial, trivial⟩⟩
    · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
      · exact ⟨trivial, ⟨trivial, trivial⟩⟩
      · exact (LCS.Finset.not_mem_empty hA).elim
  · intro A hA
    change A ∈ LCS.Finset.insert nnfHauptEx_Pa
      (LCS.Finset.insert nnfHauptEx_Qa
        (LCS.Finset.insert nnfHauptEx_RfaAndRfb
          LCS.Finset.empty)) at hA
    rcases LCS.Finset.mem_insert.mp hA with rfl | hA
    · trivial
    · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
      · trivial
      · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
        · exact ⟨trivial, trivial⟩
        · exact (LCS.Finset.not_mem_empty hA).elim

-- BEGIN PROOF
proof_of nnfHauptsatzExIsMidsequent := by
  let occurrence :
      G2nnfProofTree.NodeOccurrence nnfHauptsatzExNormalTree
        nnfHauptExMidGamma nnfHauptExDelta :=
    ⟨nnfHauptExNormalConstruction.node,
      nnfHauptExNormalConstruction.path⟩
  exact
    ⟨nnfHauptExMidFinsetQuantifierFree,
      ⟨occurrence, nnfHauptExNormalConstruction.above,
        nnfHauptExNormalConstruction.below⟩⟩
end LCS.Herbrand.NNFHauptsatz.Theorem
end
