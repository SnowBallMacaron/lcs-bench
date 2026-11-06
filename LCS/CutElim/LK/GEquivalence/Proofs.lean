import LCS.CutElim.LK.GEquivalence

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

proof_of theorem_6_2_1_spec := fun _ t =>
  convert_g_to_folkCutFree_isCutFree t

end LCS.CutElim.LK
end
