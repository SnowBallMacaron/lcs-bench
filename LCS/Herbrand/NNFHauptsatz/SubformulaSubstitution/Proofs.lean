import LCS.Herbrand.NNFHauptsatz.SubformulaSubstitution

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

proof_of replaceExResult := by
  -- BEGIN PROOF
    unfold replaceMaxQuantSub replaceExFormula replaceExTarget replaceExReplacement
    simp only [replaceMaxQuantSubCore]
    have hne_disj : ∀ x B,
        FormulaN.disj
          (FormulaN.all 0 (FormulaN.predN NnfExPred.P (replExVec1 (Term.var 0))))
          ((FormulaN.predN NnfExPred.Q
              (replExVec1 (Term.const ReplExConst.b))).conj
            (FormulaN.all 1
              ((FormulaN.predN NnfExPred.P (replExVec1 (Term.var 1))).neg.disj
                (FormulaN.all 2
                  (FormulaN.predN NnfExPred.R
                    (replExVec2 (Term.var 1) (Term.var 2))))))) ≠
        @FormulaN.all replExLang x B := by
      intro x B h; cases h
    simp only [show ∀ x B, _ from hne_disj, if_false]
    split
    · rename_i h; cases h
    · split
      · rename_i h h'; cases h'
      · simp only [ite_true]
end LCS.Herbrand.NNFHauptsatz
end
