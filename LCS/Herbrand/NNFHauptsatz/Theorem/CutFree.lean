import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.CutFree.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.CutFree

Lemma 7.4.2: cut-free G2nnf proof trees.
-/

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
namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

/-- Lemma 7.4.2 (required def): Predicate asserting that an (indexed) G2nnf proof tree contains no applications of the cut rule. Defined recursively: axiom leaves are vacuously cut-free, and internal nodes require that the rule is not a cut and all subtrees are cut-free. Since `G2nnfProofTree` is indexed by its conclusion sequent in `LCS.Finset (FormulaN L)`, the predicate is defined by structural recursion on the proof tree. -/
@[blueprint "chap7__lemma_7_4_2"]
def isCutFree {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    (match rule with
     | .cut _ _ _ _ _ => False
     | _ => True) ∧
    isCutFree (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (match rule with
     | .cut _ _ _ _ _ => False
     | _ => True) ∧
    isCutFree (hL := hL) sub1 ∧ isCutFree (hL := hL) sub2

end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
end
