import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import Attach
import LCS.Herbrand.HerbrandTheorem.Preliminaries.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Preliminaries
    Chapter 7, Section 5.1: Preliminaries for Herbrand's theorem.

    Lemma 7.5.1 (a rectified formula is provable iff its universal closure
    is provable) and the reduction of a sequent to one sentence: a sequent is
    provable iff the disjunction of its negated antecedents and its succedents
    is provable, so the input may be taken as distinct rectified sentences on
    the right of the arrow.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

/-- The right-hand Herbrand sequent consists of distinct rectified sentences,
with distinct names at every binder occurrence across the sequent.
The list represents the succedent of a sequent with empty antecedent. -/
@[blueprint "chap7__definition_7_5_1"]
def HerbrandInputConvention {L : Language} (Γ : List (FormulaN L)) : Prop :=
  Γ.Nodup ∧
  (∀ A ∈ Γ, formulaFVN A = ∅) ∧
  (Γ.flatMap formulaBoundVarIndices).Nodup

-- ===================================================================
-- Lemma 7.5.1 (required helper): universalClosure
-- ===================================================================

/-- Lemma 7.5.1 (required helper): Constructs the universal closure of a formula A by wrapping universal quantifiers forall y_1 ... forall y_n around A, where the list of variables [y_1, ..., y_n] is given explicitly. universalClosure A [y_1, ..., y_n] = forall y_1 (forall y_2 (... (forall y_n A) ...)). -/
@[blueprint "chap7__lemma_7_5_1"]
def universalClosure {L : Language}
    (A : FormulaN L) (vars : List Nat) : FormulaN L :=
  vars.foldr (fun v body => FormulaN.all v body) A

-- ===================================================================
-- Lemma 7.5.1 (helper): folkProvable_allRight
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (helper): folkProvable_allLeft_cut
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (helper): universalClosure_iff_folkProvable
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (LK variant): universal_closure_provability_iff_LK
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (LKe variant): universal_closure_provability_iff_LKe
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1: lemma_7_5_1
-- ===================================================================

/-- Lemma 7.5.1: Let A be a rectified formula, and let FV(A) = {y_1, ..., y_n} be its set of free variables. The sequent -> A is (LK or LKe)-provable iff the sequent -> forall y_1 ... forall y_n A is (LK or LKe)-provable. This is the textbook's unified "(LK or LK_e) provable" statement. The first conjunct gives the LK reading (§6.2, without equality); the second gives the LKe reading (§6.3, with equality). STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded by `hRect`. -/
@[blueprint "chap7__lemma_7_5_1" (main := true)]
theorem lemma_7_5_1 {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) :
    (∀ (_hNoEq : L.withoutEquality),
       folkProvable (Sequent.mk [] [A]) ↔
       folkProvable (Sequent.mk [] [universalClosure A fvs])) ∧
    (lkeProvable (Sequent.mk [] [A]) ↔
     lkeProvable (Sequent.mk [] [universalClosure A fvs]))

end LCS.Herbrand.HerbrandTheorem
