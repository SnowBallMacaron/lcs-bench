import LCS.FirstOrder.Gentzen.Hintikka.HintikkaSets

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

proof_of hintikka_set_satisfiable := ⟨hintikkaStructure H S hHS, identityAssignment H S hHS,
  -- BEGIN PROOF
     hintikka_set_satisfiable_concrete hL H S hHS⟩

end LCS.FirstOrder.Gentzen.Hintikka
end
