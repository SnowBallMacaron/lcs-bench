import LCS.Herbrand.NNFHauptsatz.QuantifierPolarity

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
section QuantifierPolarity

proof_of quantifierOccurrence_ruleKind := set_option backward.isDefEq.respectTransparency false in
  by
    rcases o.normalization true with ⟨q, ha, hs⟩
    refine ⟨q, ha, ?_, ?_⟩
    · cases negative <;> simpa using hs
    · rw [hs]
      cases side <;> cases k <;> cases negative <;> rfl

proof_of quantifierPolarityEx_ruleKind := set_option backward.isDefEq.respectTransparency false in
  by
    refine ⟨rfl, ?_⟩
    exact quantifierOccurrence_ruleKind (L := qPolExLang) rfl quantifierPolarityExOccurrence .antecedent

proof_of quantifierPolarityEx_equiv := set_option backward.isDefEq.respectTransparency false in
  FormulaN.toNNF_equiv quantifierPolarityExFormula
end QuantifierPolarity
end LCS.Herbrand.NNFHauptsatz
end
