import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import LCS.CutElim.LK.Part1
import LCS.CutElim.LK.Part2

/-! # CutElim.LK
    Formalization of Chapter 6, Section 2.
    The Gentzen system LK and the logical equivalence of G, LK, and LK without cut.
    Source: Logic for Computer Science, Gallier 2015
-/

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


-- ===================================================================
-- Definition 6.2.1 (companion): isFOLKAxiom
-- ===================================================================


namespace FOLKStep1


end FOLKStep1

namespace FOLKStep2


end FOLKStep2

-- ===================================================================
-- Definition 6.2.1 (companion type): FOLKProofTree (indexed)
-- ===================================================================


namespace FOLKProofTree


end FOLKProofTree

-- ===================================================================
-- Definition 6.2.1 (companion type): FOLKDeductionTree (indexed)
-- ===================================================================


namespace FOLKDeductionTree


end FOLKDeductionTree

-- ===================================================================
-- Definition 6.2.1 (companion def): folkProvable / folkCutFreeProvable
-- ===================================================================


-- Float an element from inside a left list to the front

section

local notation "CutFreeTree" => (fun s => {t : FOLKProofTree s // FOLKProofTree.isCutFree t})


end



end LCS.CutElim.LK
