import LCS.CutElim.Interpolation.VariableSubstitution

section

namespace LCS.CutElim.Interpolation

open Classical

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen.Hintikka

helper /-- Internal convenience wrapper for applying both LK substitutions to one
proof and one selected occurring constant. This is not the unified statement
of Lemma 6.5.1; see `folkProofSubst_6_5_1`. -/
noncomputable def Interpolation.folkProofSubstVarAndConst {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (z y : Nat) (c : L.constSymbols)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z)
    (hConstOccurs : T.constOccurs c) :
    LCS.CutElim.LK.FOLKProofTree (sequentSubstVar s z y) ×
    LCS.CutElim.LK.FOLKProofTree (sequentSubstConst s z c) :=
  ⟨folkProofSubstVar T z y hNotBound hNotOccurs,
    folkProofSubstConst T z c hNotOccurs⟩



















helper theorem Interpolation.folk_var_subst_preservation {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s)
    (y z : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    folkProvable (sequentSubstVar s z y) :=
  ⟨folkProofSubstVar T z y hNotBound hNotOccurs⟩

helper /-- Provability-level consequences of variable and constant substitution
on LK proof trees. -/
theorem Interpolation.folk_subst_preservation {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (y z : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    (folkProvable (sequentSubstVar s z y)) ∧
    (∀ c : L.constSymbols, T.constOccurs c →
      folkProvable (sequentSubstConst s z c)) :=
  ⟨⟨folkProofSubstVar T z y hNotBound hNotOccurs⟩,
    fun c hConstOccurs =>
      ⟨folkProofSubstConst T z c hNotOccurs⟩⟩











end LCS.CutElim.Interpolation

end
