import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- Rectification evidence for a singleton-to-singleton G2 sequent. -/
theorem allRectified_singletons {L : Language}
    [DecidableEq (FormulaN L)] {A B : FormulaN L}
    (hA : isRectified A) (hB : isRectified B) :
    AllRectified
      (({A} : LCS.Finset (FormulaN L)),
       ({B} : LCS.Finset (FormulaN L))) := by
  constructor
  · intro F hF
    have hFA : F = A := (LCS.Finset.mem_singleton F A).mp hF
    subst F
    exact hA
  · intro F hF
    have hFB : F = B := (LCS.Finset.mem_singleton F B).mp hF
    subst F
    exact hB

end LCS.Herbrand.SHGTheorem.Herbrand
end
