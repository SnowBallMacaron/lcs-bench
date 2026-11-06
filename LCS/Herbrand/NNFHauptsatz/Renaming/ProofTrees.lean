import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming.Formulae
import LCS.Herbrand.NNFHauptsatz.Renaming.Sequents
import LCS.Herbrand.NNFHauptsatz.Renaming.Occurrences

/-! # Herbrand.NNFHauptsatz.Renaming.ProofTrees

Uniform variable renaming of G2nnf rule instances and proof trees.
-/

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz
namespace G2nnfProofTree

/-- Transport an indexed G2nnf proof tree across equal conclusion indices. -/
noncomputable def castTree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    G2nnfProofTree hL Gamma' Delta' :=
  hGamma ▸ hDelta ▸ T

end G2nnfProofTree
end LCS.Herbrand.NNFHauptsatz
end
