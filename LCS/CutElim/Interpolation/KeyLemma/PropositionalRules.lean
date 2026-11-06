import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions

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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

structure FormulaCover {L : Language}
    (F G : FormulaN L) : Prop where
  pred : formulaPredSymbolsN F ⊆ formulaPredSymbolsN G
  const : formulaConstSymbolsN F ⊆ formulaConstSymbolsN G
  fv : formulaFVN F ⊆ formulaFVN G
  noEq : formulaNoEq G → formulaNoEq F

theorem FormulaCover.refl {L : Language} (F : FormulaN L) :
    FormulaCover F F :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, id⟩

end LCS.CutElim.Interpolation
end
