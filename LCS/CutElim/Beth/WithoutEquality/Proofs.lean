import LCS.CutElim.Beth.WithoutEquality

section
namespace LCS.CutElim.Beth
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

helper /-- Theorem 6.6.1 (companion, part a): If some predicate symbol
occurs in the axiom formula, implicit definability implies explicit
definability (witnessed by a formula defining Q from the same
axioms of implDef).

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
theorem beth_without_equality_part_a
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    ∃ D : FormulaN L, ExplicitDefinabilityWitness implDef D :=
-- BEGIN PROOF
  ⟨beth_explicit_definer L hNoEq implDef hOccurs,
    beth_explicit_definer_spec L hNoEq implDef hOccurs⟩

proof_of beth_definability_without_equality := by
  -- BEGIN PROOF
    exact ⟨fun hOccurs => beth_without_equality_part_a L hNoEq implDef hOccurs,
      fun hNone => beth_without_equality_part_b L hNoEq implDef hNone⟩

end LCS.CutElim.Beth
end
