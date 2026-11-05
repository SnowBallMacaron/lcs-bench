import LCS.CutElim.Hauptsatz.FolkToG1nnf

namespace LCS.CutElim.Hauptsatz.FolkToG1nnf

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.CutElim.LK

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

proof_of g1nnf_completeness_full := by
  apply g1nnfProofTree_of_setDerivable
    (g1nnf_completeness hNoEq s hValid hNoFreeBound) hΓ hΔ
  constructor
  · intro F hF
    exact s.ante_nnf F ((hΓ F).1 hF)
  · intro F hF
    exact s.succ_nnf F ((hΔ F).1 hF)


end LCS.CutElim.Hauptsatz.FolkToG1nnf
