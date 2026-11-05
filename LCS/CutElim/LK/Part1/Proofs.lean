import LCS.CutElim.LK.Part1

section

namespace LCS.CutElim.LK

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.CutElim.CompletenessBridge

namespace FOLKProofTree

helper @[simp]
theorem FOLKProofTree.conclusion_eq {L : Language} {s : Sequent L}
    (t : FOLKProofTree s) : t.conclusion = s := rfl

end FOLKProofTree

end LCS.CutElim.LK

end

section

namespace LCS.CutElim.LK

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.CutElim.CompletenessBridge

namespace FOLKDeductionTree

helper @[simp]
theorem FOLKDeductionTree.conclusion_eq {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (t : FOLKDeductionTree hL s) : t.conclusion = s := rfl

end FOLKDeductionTree

end LCS.CutElim.LK

end

section

namespace LCS.CutElim.LK

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.CutElim.CompletenessBridge

helper /-- Definition 6.2.1 (companion): Provability of a multiset sequent is
provability of any representative sequent. -/
theorem folkProvableMS_mk {L : Language} (hL : L.withoutEquality) (s : Sequent L) :
    folkProvableMS hL (Quotient.mk (Sequent.permSetoid L) s) ↔ folkProvable s :=
  Iff.rfl











helper /-- Lemma 6.2.1: Every axiom of LK is valid. For every rule of LK,
if the premises of the rule are valid, then the conclusion of the
rule is valid. Every LK-provable sequent is valid. -/
theorem lemma_6_2_1 {L : Language} :
    (∀ s : Sequent L, isFOLKAxiom s → sequentValid s) ∧
    (∀ {prem conc : Sequent L}, (rule : FOLKStep1 prem conc) →
      sequentValid prem → sequentValid conc) ∧
    (∀ {prem1 prem2 conc : Sequent L}, (rule : FOLKStep2 prem1 prem2 conc) →
      sequentValid prem1 → sequentValid prem2 → sequentValid conc) ∧
    (∀ seq : Sequent L, folkProvable seq → sequentValid seq) :=
-- BEGIN PROOF
  ⟨lemma_6_2_1_axioms_valid,
   fun rule hp => lemma_6_2_1_rules1_preserve_validity rule hp,
   fun rule hp1 hp2 => lemma_6_2_1_rules2_preserve_validity rule hp1 hp2,
   soundness_FOLK⟩

helper /-- Lemma 6.2.1 (axioms valid): Every LK axiom over a language without
equality is valid. -/
theorem lemma_6_2_1_axioms_validNoEq {L : Language} (hL : L.withoutEquality)
    (s : Sequent L) (h : isFOLKAxiomNoEq hL s) : sequentValid s :=
  lemma_6_2_1_axioms_valid s h

helper /-- Lemma 6.2.1 (one-premise rules preserve validity): Over a language without
equality, every one-premise LK rule preserves validity. -/
theorem lemma_6_2_1_rules1_preserve_validityNoEq {L : Language}
    (hL : L.withoutEquality) {prem conc : Sequent L}
    (rule : FOLKStep1NoEq hL prem conc)
    (hprem : sequentValid prem) : sequentValid conc :=
  lemma_6_2_1_rules1_preserve_validity rule hprem

helper /-- Lemma 6.2.1 (two-premise rules preserve validity): Over a language without
equality, every two-premise LK rule, including cut, preserves validity. -/
theorem lemma_6_2_1_rules2_preserve_validityNoEq {L : Language}
    (hL : L.withoutEquality) {prem1 prem2 conc : Sequent L}
    (rule : FOLKStep2NoEq hL prem1 prem2 conc)
    (hprem1 : sequentValid prem1) (hprem2 : sequentValid prem2) :
    sequentValid conc :=
  lemma_6_2_1_rules2_preserve_validity rule hprem1 hprem2

helper /-- Lemma 6.2.1 (provable sequent valid): Every LK-provable sequent over a
language without equality is valid. -/
theorem soundness_FOLKNoEq {L : Language} (hL : L.withoutEquality)
    (seq : Sequent L) (h : folkProvableNoEq hL seq) : sequentValid seq :=
  soundness_FOLK seq h

proof_of lemma_6_2_1NoEq := lemma_6_2_1


helper /-- Lemma 6.2.1 (companion): Right weakening from the empty sequent to
`→ A ⊃ A` has a valid conclusion and an invalid premise. -/
theorem lk_weakening_not_invertible_witness {L : Language}
    (hL : L.withoutEquality) (A : FormulaN L) :
    ∃ _ : FOLKStep1NoEq hL (Sequent.mk [] [])
        (Sequent.mk [] [FormulaN.impl A A]),
      sequentValid (Sequent.mk [] [FormulaN.impl A A]) ∧
      ¬ sequentValid (Sequent.mk ([] : List (FormulaN L)) []) := by
  refine ⟨FOLKStep1.weakenRight (FormulaN.impl A A) [] [], ?_, ?_⟩
  · intro M val _
    exact ⟨FormulaN.impl A A, by simp, fun h => h⟩
  · let M : Structure L :=
      { carrier := Unit
        carrierNonempty := ⟨()⟩
        interpFunc := fun _ _ => ()
        interpConst := fun _ => ()
        interpPred := fun _ _ => False }
    intro hValid
    obtain ⟨B, hB, _⟩ := hValid M (fun _ => ()) (by intro A hA; cases hA)
    exact nomatch hB

proof_of lk_rules_not_invertible := by
  intro hInvertible
  let L : Language :=
    { funSymbols := Empty
      funArity := fun f => nomatch f
      constSymbols := Empty
      predSymbols := Unit
      predArity := fun _ => 0
      hasEquality := false }
  have hL : L.withoutEquality := rfl
  obtain ⟨r, hConc, hPrem⟩ :=
    lk_weakening_not_invertible_witness hL (FormulaN.predN () (fun i => nomatch i))
  exact hPrem (hInvertible L hL r hConc)






















end LCS.CutElim.LK

end
