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
import LCS.Herbrand.NNFHauptsatz.Theorem.AtomicAxioms.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.AtomicAxioms

Definition 7.4.3: G2nnf axioms have atomic formulae; proofs with bare atomic leaves.
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Definition 7.4.3: the four bare axiom sequents on an atomic A.
The negated identity and complementary-literal schemes retain their literal
negations; there are no additional antecedent or succedent contexts. -/
@[blueprint "chap7__definition_7_4_3"]
def IsBareAtomicLeafSequent {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)]
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  ∃ A : FormulaN L, A.isAtomic ∧
    (seq = (LCS.Finset.insert A LCS.Finset.empty,
            LCS.Finset.insert A LCS.Finset.empty) ∨
     seq = (LCS.Finset.empty,
            LCS.Finset.insert A (LCS.Finset.insert (.neg A) LCS.Finset.empty)) ∨
     seq = (LCS.Finset.insert A (LCS.Finset.insert (.neg A) LCS.Finset.empty),
            LCS.Finset.empty) ∨
     seq = (LCS.Finset.insert (.neg A) LCS.Finset.empty,
            LCS.Finset.insert (.neg A) LCS.Finset.empty))

/-- Definition 7.4.3 (atomic-leaf extension): every terminal sequent is one
of the four bare atomic schemes. Both branches of a binary inference are
checked; open leaves and extra axioms do not satisfy this predicate. -/
@[blueprint "chap7__definition_7_4_3"]
def HasBareAtomicLeaves {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf .. => False
  | _, _, .extraAxiom .. => False
  | _, _, .axiom_ rule _ _ _ => IsBareAtomicLeafSequent hL rule.conclusion
  | _, _, .onePremise _ _ _ _ sub => HasBareAtomicLeaves (hL := hL) sub
  | _, _, .twoPremise _ _ _ _ left right =>
    HasBareAtomicLeaves (hL := hL) left ∧ HasBareAtomicLeaves (hL := hL) right

/-- Section 7.4.3 extends the atomic-leaf lemma to G2nnf. In Definition
7.4.3's corrected calculus, every proof already has bare atomic leaves,
including proofs with cuts and proofs not assumed pure-variable. -/
@[blueprint "chap7__definition_7_4_3"]
theorem g2nnf_hasBareAtomicLeaves {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) : HasBareAtomicLeaves (hL := hL) T 
end LCS.Herbrand.NNFHauptsatz.Theorem
end
