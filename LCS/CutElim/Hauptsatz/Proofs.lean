import LCS.CutElim.Hauptsatz

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN.Substitution



end LCS.FirstOrder.SyntaxN

namespace LCS.CutElim.Hauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Equivalence

namespace G1nnfFinsetSequent

namespace IsNNF



end IsNNF

end G1nnfFinsetSequent

proof_of nnfEx_subNnf1_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl


proof_of nnfEx_subNnf2_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl


proof_of nnfEx_formulaA_nnf_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl

proof_of nnf_equivalence := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  -- BEGIN PROOF
    ⟨A.toNNF, A.toNNF_isNNF, A.toNNF_equiv⟩


end LCS.CutElim.Hauptsatz
