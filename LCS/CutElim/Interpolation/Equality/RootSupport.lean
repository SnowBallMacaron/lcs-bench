import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.ClosedAxioms

section
namespace LCS.CutElim.Interpolation.Equality
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
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

/-- The nonlogical head symbol of an equality axiom is supported by
the root sequent. Reflexivity and built-in equality congruence have no
function- or named-predicate head to check. -/
def equalityAxiomSupportedBy {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) : LKeEqualityAxiom L → Prop
  | .refl _ => True
  | .funcCong f _ _ => f ∈ sequentFunSymbolsList S
  | .predCong P _ _ => P ∈ sequentPredSymbolsList S
  | .eqCong _ _ _ _ => True

/-- An indexed LKe proof whose equality leaves are certified against
a designated root support. The rule indices are the ordinary LKe
indices; only the equality-leaf constructor carries an extra local
support certificate. -/
inductive RootSupportedLKeProof {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) : Sequent L → Type where
  | axiom_ (q : Sequent L) (h : isFOLKAxiom q) :
      RootSupportedLKeProof S q
  | eqAxiom (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L)
      (hax : equalityAxiomSupportedBy S ax) :
      RootSupportedLKeProof S (ax.toSequent hL)
  | onePremise {prem conc : Sequent L}
      (rule : FOLKStep1 prem conc)
      (t : RootSupportedLKeProof S prem) :
      RootSupportedLKeProof S conc
  | twoPremise {prem₁ prem₂ conc : Sequent L}
      (rule : FOLKStep2 prem₁ prem₂ conc)
      (t₁ : RootSupportedLKeProof S prem₁)
      (t₂ : RootSupportedLKeProof S prem₂) :
      RootSupportedLKeProof S conc

end LCS.CutElim.Interpolation.Equality
end
