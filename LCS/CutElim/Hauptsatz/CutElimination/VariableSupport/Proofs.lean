import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfProofTree













end G1nnfProofTree

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz









end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfRule

helper /-- A cut formula's complete formula support is retained as hidden rule
data even when the cut is absent from the rule conclusion. -/
theorem CutElim.Hauptsatz.G1nnfRule.variableSupport_cut_formula {L : Language}
    (A : FormulaN L) (Lam Theta : LCS.Finset (FormulaN L))
    (v : Nat) (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G1nnfRule.cut A Lam Theta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl hv)

























end G1nnfRule

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfProofTree















helper /-- The tree-only fresh selector is outside the complete finite support,
rather than merely outside the root's free variables. -/
theorem CutElim.Hauptsatz.G1nnfProofTree.freshVariable_not_mem_variableSupport {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) :
    T.freshVariable ∉ T.variableSupport := by
  simpa only [freshVariable] using
    T.freshVariableAvoiding_not_mem_variableSupport LCS.Finset.empty

helper /-- Tree-only specialization of `freshVariableAvoiding_notBoundIn`. -/
theorem CutElim.Hauptsatz.G1nnfProofTree.freshVariable_notBoundIn {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) :
    T.notBoundIn T.freshVariable := by
  simpa only [freshVariable] using
    T.freshVariableAvoiding_notBoundIn LCS.Finset.empty

end G1nnfProofTree

end LCS.CutElim.Hauptsatz

end
