import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.Theorem.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Main.Theorem
    Chapter 7, Section 5.4: Theorem 7.5.1 (Herbrand's theorem for prenex
    formulae) in LK and LKe, with its forward direction (from a proof given by
    the sharpened Hauptsatz to a provable Herbrand disjunction), its converse
    (proof reconstruction along the subterm ordering of the Herbrand terms),
    and the constant-free counterexample behind the special constant #.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

-- ===================================================================
-- Theorem 7.5.1: the printed constant-free counterexample (CN26)
-- ===================================================================

































-- ===================================================================
-- Theorem 7.5.1 (forward direction, required companion):
--   herbrand_substitution_pairs_LK
-- ===================================================================











/-- The normalized sequent is obtained by NNF conversion and fresh binder
renaming of each source occurrence, followed by deletion of duplicate sentences.
The intermediate list preserves source order and occurrences; the sublist and
coverage clauses permit only duplicate deletion. Global binder distinction is
certified on the output by its Skolem allocation. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsHerbrandNormalization {L : Language}
    (Gamma Delta : List (FormulaN L)) : Prop :=
  ∃ starts : Fin Gamma.length → Nat,
    let renamed := List.ofFn fun i =>
      (rectifyAux (Gamma.get i).toNNF id (starts i)).1
    Delta.Sublist renamed ∧ (∀ B ∈ renamed, B ∈ Delta)

/-- Theorem 7.5.1 (forward direction): An LK-provable prenex sentence
sequent over an equality-free language has a normalized representative with
sequent-wide distinct binders and a provable Herbrand disjunction. Each witness
occurrence retains its normalized source and the complete ground tuple, including
vacuous existential binders, in the common constant-completed Skolem signature. -/
theorem herbrandTheorem_forward_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup)
    (hProv : folkProvable (Sequent.mk [] Gamma)) :
    ∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps) := by
  -- REPAIR(T7-58): proof pending
  sorry

/-- Theorem 7.5.1 (converse direction): A provable Herbrand disjunction
built from a normalized representative of the source yields LK provability of
the original sequent. The allocation certifies the output binder convention;
finite fresh names for reconstruction are chosen within the proof. -/
theorem herbrandTheorem_converse_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup)
    (hHerbrand : ∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps)) :
    folkProvable (Sequent.mk [] Gamma) := by
  -- REPAIR(T7-58): proof pending
  sorry

/-- Theorem 7.5.1: A prenex sentence sequent over an equality-free language
is LK-provable iff a normalized representative admits a finite source-associated
sequence of ground substitution pairs with provable Herbrand disjunction.
Normalization uses NNF conversion, binder renaming and duplicate deletion;
its Skolem allocation certifies sequent-wide binder distinction. The witness
signature, occurring-symbol restriction, grounding constant and full-prefix
assignments are those of IsConstructibleFromFunctionalForm. -/
@[blueprint "chap7__theorem_7_5_1" (main := true)]
theorem herbrandTheorem_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup) :
    folkProvable (Sequent.mk [] Gamma) ↔
    (∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps))

-- ===================================================================
-- Theorem 7.5.1 (LKe variant, required companion):
--   herbrand_substitution_pairs_LKe
-- ===================================================================











-- ===================================================================
-- Theorem 7.5.1: herbrandTheorem_LKe (LKe variant)
-- ===================================================================

/-- Theorem 7.5.1 (LKₑ): A prenex sentence sequent over a language with
equality is LKₑ-provable iff a normalized representative admits a finite
source-associated sequence of ground substitution pairs with LKₑ-provable
Herbrand disjunction. Equality retains its identity interpretation. Normalization
uses NNF conversion, binder renaming and duplicate deletion; the output's Skolem
allocation certifies sequent-wide binder distinction. Full-prefix ground tuples,
occurring-symbol restrictions and the ambient/adjoined grounding constant are
those of IsConstructibleFromFunctionalForm. Fresh names for reconstruction are
chosen within the proof. -/
@[attach_debt, blueprint "chap7__theorem_7_5_1" (main := true)]
theorem herbrandTheorem_LKe {L : Language}
    (hL : L.hasEquality = true)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup) :
    lkeProvable (Sequent.mk [] Gamma) ↔
    (∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      lkeProvable (HerbrandDisjunction sd sps))

end LCS.Herbrand.HerbrandTheorem.Main
