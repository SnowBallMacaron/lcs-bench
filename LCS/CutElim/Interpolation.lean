import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair
import LCS.CutElim.Interpolation.QuantifierCases
import LCS.CutElim.Interpolation.KeyLemma
import LCS.CutElim.Interpolation.FreshPredicate
import LCS.CutElim.Interpolation.Craig

/-! # CutElim.Interpolation
    Formalization of Chapter 6, Sections 6.5.1-6.5.2.
    Interpolants and Craig's interpolation theorem without equality.
    Source: Logic for Computer Science, Gallier 2015
-/

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


-- ===================================================================
-- Lemma 6.5.2 (required): List.Interleaving
-- ===================================================================

namespace List


end List

-- ===================================================================
-- botFormula: language-level 0-ary predicate encoding falsum
-- ===================================================================


-- ===================================================================
-- Lemma 6.5.2 (companion def): FOLKBotProofTree.conclusion
-- ===================================================================

namespace FOLKBotProofTree

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}


end FOLKBotProofTree

-- ===================================================================
-- Lemma 6.5.4 (shared definition): lkBotProvable
-- ===================================================================


section

variable (L : Language) (z : Nat) (c : L.constSymbols)


end


section

variable (L : Language) (z y : Nat)


end


section

variable (L : Language) (hL : L.withoutEquality) (z y : Nat)


end


section

variable (L : Language) (hL : L.withoutEquality) (z : Nat) (c : L.constSymbols)


end


-- ===================================================================
-- lkBot structural rule infrastructure
-- The lkBot_* helpers construct FOLKBotProofTree nodes directly.
-- ===================================================================

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}


section

variable (L : Language) (z : Nat) (y : Nat)



end


section

variable (L : Language) (z : Nat) (c : L.constSymbols)


end


-- ===================================================================
-- Round-trip and no_const lemmas
-- ===================================================================


section

variable (L : Language) (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (z : Nat) (c : L.constSymbols)


end




-- ===================================================================
-- Internal Craig helper: adjoining a fresh nullary predicate
-- ===================================================================

namespace CraigFreshBot



section

variable (L : Language)


end


section

variable (L : Language) (P : L.predSymbols) (v : Nat)


end


end CraigFreshBot

-- ===================================================================
-- Theorem 6.5.1 (part a): craig_interpolant_common_pred
-- ===================================================================


end LCS.CutElim.Interpolation
