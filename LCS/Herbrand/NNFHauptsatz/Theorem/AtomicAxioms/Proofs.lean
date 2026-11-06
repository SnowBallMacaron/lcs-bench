import LCS.Herbrand.NNFHauptsatz.Theorem.AtomicAxioms

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

proof_of g2nnf_hasBareAtomicLeaves := by
  induction T with
  | leaf Γ Δ hOpen hNNF hRect => exact hOpen.elim
  | extraAxiom Γ Δ hExtra hNNF hRect => exact hExtra.elim
  | axiom_ rule hAdmit hAx hSC =>
    change IsBareAtomicLeafSequent hL rule.conclusion
    cases rule with
    | axiomPosId A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inl rfl⟩
    | axiomNegId A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inr (Or.inr rfl))⟩
    | axiomCompRight A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inl rfl)⟩
    | axiomCompLeft A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inr (Or.inl rfl))⟩
    | _ => simp [G2nnfRuleCore.premises] at hAx
  | onePremise rule hAdmit hPrem hSC sub ih => exact ih
  | twoPremise rule hAdmit hPrem hSC left right ihLeft ihRight =>
    exact ⟨ihLeft, ihRight⟩

end LCS.Herbrand.NNFHauptsatz.Theorem
end
