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

helper /-- Definition 6.4.2 (helper): Convert a list of formulae to a set.
Used to bridge between the list-based proof tree representation
and the set-based sequent type from Definition 6.4.2. -/
def CutElim.Hauptsatz.listAsSet {L : Language} (l : List (FormulaN L)) : Set (FormulaN L) :=
  fun x => x ∈ l

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
