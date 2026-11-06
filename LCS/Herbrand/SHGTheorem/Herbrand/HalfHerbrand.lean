import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemNormalForm
import Attach
import LCS.Herbrand.SHGTheorem.Herbrand.HalfHerbrand.ProofsStamp

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

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): emptySuccedentFromImpl
-- ===================================================================

/-- Internal closed-seed core of the G1nnf branch of Lemma 7.6.2.
    The seed is the exact capability needed by the universal
    c-instance case; the public Chapter 7 wrapper obtains it from the
    section's standing constant-symbol assumption. -/
theorem herbrand_half_lemma_G1nnf_seed {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hProv : G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      Nonempty (G2nnfProofTree (show spec.language.withoutEquality from hL)
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language))) := by
  have hClosed : FormulaN.isClosed A := hSource ▸ spec.hSentence
  have hCross : LCS.CutElim.Hauptsatz.finsetCrossNoFreeBound
      ({A} : LCS.Finset (FormulaN L)) ∅ := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := hx
    rcases hF with hF | hF
    · have hFA := (LCS.Finset.mem_singleton F A).1 hF
      subst F
      rw [hClosed] at hxF
      exact hxF.elim
    · exact (LCS.Finset.not_mem_empty hF).elim
  have hNNF : allSequentFormulaeAreNNF
      (({A} : LCS.Finset (FormulaN L)), ∅) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ (hSource ▸ spec.hNNF)
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  have hRect : AllRectified (({A} : LCS.Finset (FormulaN L)), ∅) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ (hSource ▸ spec.hRect)
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  obtain ⟨T, mid, hCutFree, hPure, hMid⟩ :=
    sharpenedHauptsatz_G2nnf hL _ hNNF hRect hCross hProv
  -- REPAIR(T6-21d): proof pending
  sorry

/-- Lemma 7.6.2, equality-free branch: from a G1nnf proof of the
original sequent A ->, obtain a quantifier-free c-instance C of SK spec
with a G1nnf proof of C -> over spec.language. The exact source equality
retains the rectified-NNF sentence domain; no prenex conversion is assumed.
This is the existence specification; effective extraction is deferred. -/
theorem herbrand_half_lemma_G1nnf {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hProv : G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      Nonempty (G1nnfProofTree (show spec.language.withoutEquality from hL)
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language))) := by
  -- REPAIR(T7-80): proof pending (G1 output over the exact Skolem extension).
  sorry

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): herbrand_half_lemma_G1nnfEq
-- ===================================================================

/-- Closed-seed form of the equality branch of Lemma 7.6.2. -/
theorem herbrand_half_lemma_G1nnfEq_seed {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hProv : G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      (haveI hL' : spec.language.hasEquality = true := hL
       Nonempty (G2nnfEqProofTree hL'
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language)))) := by
  -- REPAIR(T6-21d): proof pending
  sorry

/-- Lemma 7.6.2, equality branch: from a G1nnf= proof of the original
sequent A ->, obtain a quantifier-free c-instance C of SK spec with a
G1nnf= proof of C -> over the same Skolem extension. The source is the
specified rectified NNF sentence. Effective extraction remains deferred. -/
theorem herbrand_half_lemma_G1nnfEq {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hProv : G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L)))) :
    ∃ (C : FormulaN spec.language),
      isCInstanceOf C (SK spec) ∧
      FirstOrder.SemanticsN.isQuantifierFree C ∧
      (haveI hL' : spec.language.hasEquality = true := hL
       Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hL'
        ({C} : LCS.Finset (FormulaN spec.language))
        (∅ : LCS.Finset (FormulaN spec.language)))) := by
  -- REPAIR(T7-80): proof pending (G1 output over the exact Skolem extension).
  sorry

-- ===================================================================
-- Lemma 7.6.2: herbrand_half_lemma
-- ===================================================================

/-- Lemma 7.6.2, existence specification for a rectified NNF sentence A
and its fixed Skolem form SK spec. Each original proof of A -> yields a
quantifier-free c-instance C with a proof of C ->, representing provability
of not C in NNF. Both input and output use G1nnf without equality and
G1nnf= with equality; the output lives in spec.language. The conjunction
keeps the two language branches separate. Effective extraction is deferred. -/
@[blueprint "chap7__lemma_7_6_2" (main := true)]
theorem herbrand_half_lemma {L : Language}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    (∀ hL : L.withoutEquality, G1nnfProvableSet hL
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        Nonempty (G1nnfProofTree (show spec.language.withoutEquality from hL)
          ({C} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language)))) ∧
    (∀ (hL : L.hasEquality = true),
      G1nnfEqProvable_Set hL
          (({A} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        (haveI hL' : spec.language.hasEquality = true := hL
         Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hL'
          ({C} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language))))) 

end LCS.Herbrand.SHGTheorem.Herbrand
end
