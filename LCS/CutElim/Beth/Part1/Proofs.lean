import LCS.CutElim.Beth.Part1

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

helper /-- A sequent is LKe-provable if there exists an LKeProofTree with
that sequent as conclusion (type index).
(Defined locally pending restoration of LKe/Equivalence.lean.) -/
def CutElim.Beth.lkeProvable {L : Language} (s : Sequent L) : Prop :=
  Nonempty (LKeProofTree s)

proof_of explicit_implies_implicit := open LCS.CutElim.Beth.Part1.Proofs.CutElim.Beth in
  explicit_implies_implicit_validity e.axiomFormula e.definingFormula
      e.preds e.predQ e.predQ_not_in_P e.provabilityCondition
      e.definingFormula_predSyms_in


proof_of padoa_method := by
  rintro ⟨e, hA, hQ, hP⟩
  have hTwo := bethImplicitValidity_twoStructure e.axiomFormula e.preds e.predQ
    (explicit_implies_implicit e)
  rw [hA, hQ, hP] at hTwo
  have hNotQ : some Q ∉ preds.syms := by
    simpa only [hQ, hP] using e.predQ_not_in_P
  have hListed : ∀ P, some P ∈ preds.syms →
      ∀ a, I.interpPred P a ↔ J.interpPred P a := by
    intro P hp
    apply hPred P
    intro heq
    subst P
    exact hNotQ hp
  obtain ⟨a, ha⟩ := hDiff
  exact ha (hTwo M hM I J hListed hFunc hConst hPred hAI hAJ a)

end LCS.CutElim.Beth

end
