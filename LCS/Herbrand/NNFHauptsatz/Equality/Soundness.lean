import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.Soundness.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.Soundness

Definition 7.4.4: the system G2nnf= is sound.
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

/-- Definition 7.4.4 (soundness, provability form): existence of a legal
G2nnf= proof implies validity in identity semantics. -/
@[blueprint "chap7__definition_7_4_4" (main := true)]
theorem g2nnfEq_provable_implies_valid {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (Γ Δ : LCS.Finset (FormulaN L)) :
    g2nnfEqProvable hL Γ Δ → Soundness.setSequentValid Γ Δ 
end LCS.Herbrand.NNFHauptsatz.Equality
end
