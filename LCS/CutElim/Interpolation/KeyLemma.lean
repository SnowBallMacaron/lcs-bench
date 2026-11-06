import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.KeyLemma.Axioms
import LCS.CutElim.Interpolation.KeyLemma.StructuralRules
import LCS.CutElim.Interpolation.KeyLemma.PropositionalRules
import LCS.CutElim.Interpolation.KeyLemma.QuantifierRules
import Attach
import LCS.CutElim.Interpolation.KeyLemma.ProofsStamp

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

-- ===================================================================
-- Lemma 6.5.2: interpolation_key_lemma
-- ===================================================================

/-- Lemma 6.5.2: Every LK⊥-provable sequent over a language without
equality has an interpolant for each partition of its formula occurrences.
The interpolant has only common predicate symbols (apart from ⊥), constants,
and free variables. There is no common-function-symbol requirement.
No free/bound-variable convention is required of the original sequent. -/
@[attach_debt, blueprint "chap6__lemma_6_5_2" (main := true)]
theorem interpolation_key_lemma {L : Language} (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : lkBotProvable botP hBotArity s)
    (p : SequentPartition s) :
    ∃ C : FormulaN L, IsInterpolant botP hBotArity p C 

/-- The LK-provability reading of Lemma 6.5.2. -/
theorem interpolation_key_lemma_lk {L : Language} (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : folkProvable s) (p : SequentPartition s) :
    ∃ C : FormulaN L, IsInterpolant botP hBotArity p C :=
  interpolation_key_lemma hL botP hBotArity s
    (folkProvable_to_lkBotProvable botP hBotArity s hProv) p

end LCS.CutElim.Interpolation
end
