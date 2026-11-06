import LCS.Herbrand.SHGTheorem.Main.SkolemHerbrandGodel

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Theorem 7.6.1(b), result specification: from provability of the
original A ->, there exists a quantifier-free c-instance C of the fixed
Skolem form such that not C is provable, represented in NNF by C ->.
Input and output use G1nnf without equality and G1nnf= with equality; C
lives in spec.language. The conclusion is a provability proposition.
Effective production of C from an input proof remains deferred under OD-A17;
this Prop-valued specification does not implement that algorithm. -/
theorem shgTheorem_effective {L : Language}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    (∀ hL : L.withoutEquality,
      LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hL
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        G1nnfProvableSet (L := spec.language)
          (show spec.language.withoutEquality from hL)
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) ∧
    (∀ (hL : L.hasEquality = true),
      LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set hL
          (({A} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set
          (L := spec.language) hL
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) := by
-- BEGIN PROOF
  exact herbrand_half_lemma spec A hSource hConst

proof_of shgTheorem := ⟨shgTheorem_unsat spec A hSource hConst,
  -- BEGIN PROOF
     (shgTheorem_effective spec A hSource hConst).1,
     (shgTheorem_effective spec A hSource hConst).2⟩

end LCS.Herbrand.SHGTheorem.Main
end
