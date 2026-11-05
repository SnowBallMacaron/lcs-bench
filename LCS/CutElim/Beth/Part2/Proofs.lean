import LCS.CutElim.Beth.Part2

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

helper /-- Proof of Example 6.6.1 (companion): The standard-order structure on ℕ
satisfies the five arithmetic axioms. -/
theorem bethExample_standardOrder_valid :
    validInN bethExample_standardOrderStructure bethExample_fiveAxioms := by
-- BEGIN PROOF
  intro s
  simp [bethExample_fiveAxioms, bethExample_succNonZeroAxiom,
    bethExample_succInjectiveAxiom, bethExample_addZeroAxiom,
    bethExample_addSuccAxiom, bethExample_zeroLtSuccAxiom,
    bethExampleSucc, bethExamplePlus, bethExampleZero,
    formulaEvalN, termEval, assignUpdate, vec1, vec2,
    bethExample_standardOrderStructure, Nat.add_assoc]

helper /-- Proof of Example 6.6.1 (companion): The nonstandard-order structure on ℕ
satisfies the same five arithmetic axioms. -/
theorem bethExample_nonstandardOrder_valid :
    validInN bethExample_nonstandardOrderStructure bethExample_fiveAxioms := by
-- BEGIN PROOF
  intro s
  simp [bethExample_fiveAxioms, bethExample_succNonZeroAxiom,
    bethExample_succInjectiveAxiom, bethExample_addZeroAxiom,
    bethExample_addSuccAxiom, bethExample_zeroLtSuccAxiom,
    bethExampleSucc, bethExamplePlus, bethExampleZero,
    formulaEvalN, termEval, assignUpdate, vec1, vec2,
    bethExample_nonstandardOrderStructure, Nat.add_assoc]

helper /-- Example 6.6.1 (companion): The two structures on ℕ agree on 0, S, +
(same `interpFunc`, `interpConst`), both satisfy the five axioms, but
differ on <. This is the concrete non-implicit-definability witness. -/
theorem bethExample_nonImplicitDef :
    ∃ (M1 M2 : Structure bethExample_arithWithOrder),
      M1.carrier = Nat ∧ M2.carrier = Nat ∧
      HEq M1.interpFunc M2.interpFunc ∧
      HEq M1.interpConst M2.interpConst ∧
      validInN M1 bethExample_fiveAxioms ∧
      validInN M2 bethExample_fiveAxioms ∧
      ¬ (HEq M1.interpPred M2.interpPred) :=
-- BEGIN PROOF
by
  refine ⟨bethExample_standardOrderStructure,
    bethExample_nonstandardOrderStructure, rfl, rfl, ?_, ?_,
    bethExample_standardOrder_valid, bethExample_nonstandardOrder_valid, ?_⟩
  · rfl
  · rfl
  · intro hPred
    have hPredEq :
        bethExample_standardOrderStructure.interpPred =
          bethExample_nonstandardOrderStructure.interpPred :=
      eq_of_heq hPred
    have hAtOneTwo :=
      congrFun (congrFun hPredEq BethExamplePred.lt)
        (vec2 (1 : Nat) (2 : Nat))
    have hStandard :
        bethExample_standardOrderStructure.interpPred BethExamplePred.lt
          (vec2 (1 : Nat) (2 : Nat)) := by
      simp [bethExample_standardOrderStructure, vec2]
    have hNonstandard :
        ¬ bethExample_nonstandardOrderStructure.interpPred BethExamplePred.lt
          (vec2 (1 : Nat) (2 : Nat)) := by
      simp [bethExample_nonstandardOrderStructure, vec2]
    exact hNonstandard (hAtOneTwo ▸ hStandard)

proof_of bethExample_fiveAxioms_notImplicitlyDefinesLt := by
  -- BEGIN PROOF
    exact bethExample_nonImplicitDef


proof_of bethExample_sixAxioms_explicitlyDefinesLt := by
  -- BEGIN PROOF
    have hApplied :
        bethPredApplied BethExamplePred.lt =
          FormulaN.predN (L := bethExample_arithWithOrder) BethExamplePred.lt
            (vec2 (Term.var 0) (Term.var 1)) := by
      apply congrArg
        (FormulaN.predN (L := bethExample_arithWithOrder) BethExamplePred.lt)
      funext ⟨i, hi⟩
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
    have hConsequent :
        bethUniversalPrefix 2
            (FormulaN.equiv
              (bethPredApplied BethExamplePred.lt)
              bethExample_explicitDefOfOrder) =
          bethExample_orderCharAxiom := by
      rw [hApplied]
      rfl
    intro M s hSix
    have hOrder : formulaEvalN M bethExample_orderCharAxiom s :=
      (show
        formulaEvalN M bethExample_fiveAxioms s ∧
          formulaEvalN M bethExample_orderCharAxiom s
        from hSix).2
    rw [hConsequent]
    exact hOrder


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


proof_of beth_definability_with_equality := by
  -- BEGIN PROOF
    exact ⟨fun implDef => beth_with_equality_part_a L hEq implDef,
      fun implDef => beth_with_equality_part_b L hEq implDef⟩


end LCS.CutElim.Beth

end
