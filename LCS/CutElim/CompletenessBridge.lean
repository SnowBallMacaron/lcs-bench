import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality.Completeness

/-! # Completeness for finite sequents under the free/bound convention

Completeness bridges for G and G= with no variable occurring free and bound
anywhere in the end sequent.
-/

namespace LCS.CutElim.CompletenessBridge

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality

/-- A valid finite sequent over a language without equality is provable in G
with the extended quantifier rules, under the sequent-level free/bound convention. -/
theorem completenessG_cross {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) (seq : Sequent L) (hCross : crossNoFreeBound seq) :
    sequentValid seq → sequentProvableExt seq := by
  -- DEBT(Theorem 6.2.1 bridge: completeness of G with the extended quantifier rules under the sequent-level free/bound convention; proof pending, chapter 6 proof-closing phase Q17)
  sorry

/-- A valid finite sequent over a language with equality is provable in G=
under the sequent-level free/bound convention. -/
theorem completenessGEq_cross {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) (hCross : crossNoFreeBound seq) :
    sequentValid seq → sequentProvableEq hL seq := by
  -- REPAIR(T6-03): proof pending; chapter 5 T120
  sorry

end LCS.CutElim.CompletenessBridge
