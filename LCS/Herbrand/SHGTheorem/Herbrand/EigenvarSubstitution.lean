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

-- ===================================================================
-- Lemma 7.6.2 (companion def): eigenvariableToSkolemSubst
-- ===================================================================

/-- Lemma 7.6.2 (helper): Lift a base-language term into the exact
Skolem extension. Every old constant and function symbol is embedded through
`Sum.inl`; this helper never manufactures or selects a Skolem head. -/
def liftEigenvarBaseTerm {L : Language} (spec : SkolemSpec L) :
    Term L → Term spec.language
  | .var x => .var x
  | .const c => .const (Sum.inl c)
  | .func f ts =>
    .func (Sum.inl f) (fun i => liftEigenvarBaseTerm spec (ts i))

end LCS.Herbrand.SHGTheorem.Herbrand
end
