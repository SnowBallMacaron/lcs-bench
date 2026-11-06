import LCS.Herbrand.HerbrandTheorem.Substitutions

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality
namespace Substitution

proof_of applyTerm_unique := by
  funext t
  induction t with
  | var x => exact hVar x
  | const c => exact hConst c
  | func f ts ih =>
    rw [hFunc]
    exact congrArg (Term.func f) (funext ih)

end Substitution

end LCS.Herbrand.HerbrandTheorem
