import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

theorem G1nnfProofTree.depth_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).depth = T.depth := by
  subst Γ'
  subst Δ'
  rfl

theorem G1nnfProofTree.cutRank_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).cutRank = T.cutRank := by
  subst Γ'
  subst Δ'
  rfl

theorem G1nnfProofTree.eigenvariables_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ)
    (v : Nat) :
    (hΓ ▸ hΔ ▸ T).eigenvariables v = T.eigenvariables v := by
  subst Γ'
  subst Δ'
  rfl

noncomputable def G1nnfProofTree.castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    G1nnfProofTree hL Γ' Δ' :=
  hΓ ▸ hΔ ▸ T

namespace G1nnfProofTree

theorem allFormulae_transport {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).allFormulae = T.allFormulae := by
  subst Γ'
  subst Δ'
  rfl

theorem depth_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    (T.castTree hΓ hΔ).depth = T.depth := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.depth_cast hΓ hΔ T

theorem cutRank_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    (T.castTree hΓ hΔ).cutRank = T.cutRank := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.cutRank_cast hΓ hΔ T

theorem eigenvariables_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Nat) :
    (T.castTree hΓ hΔ).eigenvariables w =
      T.eigenvariables w := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.eigenvariables_cast hΓ hΔ T w

theorem notBoundIn_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Nat) :
    (T.castTree hΓ hΔ).notBoundIn w ↔ T.notBoundIn w := by
  subst Γ'
  subst Δ'
  rfl

end G1nnfProofTree

end LCS.CutElim.Hauptsatz
end
