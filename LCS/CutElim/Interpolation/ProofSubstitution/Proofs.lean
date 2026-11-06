import LCS.CutElim.Interpolation.ProofSubstitution

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

proof_of folkProofSubst_6_5_1 := by
  constructor
  · constructor
    · intro hL s T hp y z hNB hNO
      obtain ⟨hProof, _⟩ := T.substVar_proof_image z y hNB hNO hp
      exact hProof
    · intro hL s T hp z hNO c
      obtain ⟨hProof, _⟩ := T.substConst_proof_image z c hNO hp
      exact hProof
  · constructor
    · intro hEq s T hp y z hNB hNO
      exact T.substVar_isProof z y hNB hNO hp
    · intro hEq s T hp z hNO c
      exact T.substConst_isProof z c hNO hp

end LCS.CutElim.Interpolation
end
