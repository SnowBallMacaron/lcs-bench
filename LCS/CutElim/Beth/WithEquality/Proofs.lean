import LCS.CutElim.Beth.WithEquality

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

proof_of beth_definability_with_equality := by
  -- BEGIN PROOF
    exact ⟨fun implDef => beth_with_equality_part_a L hEq implDef,
      fun implDef => beth_with_equality_part_b L hEq implDef⟩

end LCS.CutElim.Beth
end
