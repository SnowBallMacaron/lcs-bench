import LCS.Herbrand.SHGTheorem.Herbrand.HalfHerbrand

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

proof_of herbrand_half_lemma := ⟨fun hL hProv => herbrand_half_lemma_G1nnf hL spec A hSource hConst hProv,
  -- BEGIN PROOF
     fun hL hProv =>
       herbrand_half_lemma_G1nnfEq hL spec A hSource hConst hProv⟩

end LCS.Herbrand.SHGTheorem.Herbrand
end
