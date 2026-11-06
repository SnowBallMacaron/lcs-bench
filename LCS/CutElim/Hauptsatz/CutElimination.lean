import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.TreeTransport
import LCS.CutElim.Hauptsatz.CutElimination.SetDerivations
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionPreservation
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionPreparation
import LCS.CutElim.Hauptsatz.CutElimination.PreparationRegression
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionLemma
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Constructions
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Measures
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.Weakening
import LCS.CutElim.Hauptsatz.CutElimination.Inversion
import LCS.CutElim.Hauptsatz.CutElimination.Reduction
import LCS.CutElim.Hauptsatz.CutElimination.Theorem

/-! # CutElim.Hauptsatz.CutElimination
    Formalization of Chapter 6, Section 6.4.
    The cut elimination theorem for G1nnf (Tait-Schwichtenberg method).
    Source: Logic for Computer Science, Gallier 2015
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness

-- ===================================================================
-- Definition 6.4.3: FormulaN.degree
-- ===================================================================

namespace LCS.FirstOrder.SyntaxN

namespace FormulaN


end FormulaN

end LCS.FirstOrder.SyntaxN

-- ===================================================================
-- Definition 6.4.2 (companion): G1nnfProofTree (indexed by Finset)
-- ===================================================================

namespace LCS.CutElim.Hauptsatz


namespace G1nnfProofTree


end G1nnfProofTree


namespace G1nnfDeductionTree


end G1nnfDeductionTree

-- ===================================================================
-- Definition 6.4.4: G1nnfProofTree.cutRank
-- ===================================================================

namespace G1nnfRule


end G1nnfRule

end LCS.CutElim.Hauptsatz

namespace LCS.CutElim.Hauptsatz

namespace G1nnfProofTree


end G1nnfProofTree

-- ===================================================================
-- Finset.insert_comm: insert is commutative for Finset
-- (needed by weakening to permute inserted principal formulae)
-- ===================================================================


-- ===================================================================
-- G1nnfRule.SideConditions transport through context extension
-- ===================================================================

namespace G1nnfRule

-- END PROOF

end G1nnfRule

-- ===================================================================
-- Eigenvariables on the indexed Finset tree
-- ===================================================================

namespace G1nnfProofTree


end G1nnfProofTree

-- ===================================================================
-- G1nnf proof-tree side-condition regressions
-- ===================================================================


end LCS.CutElim.Hauptsatz

-- ===================================================================
-- Substitution infrastructure on the Finset-indexed G1nnf proof tree
-- ===================================================================

-- ===================================================================
-- Finset helper: image_insert
-- ===================================================================


-- ===================================================================
-- Definition 6.4.5: FormulaN.notBoundIn
-- ===================================================================

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Variables

namespace FormulaN


end FormulaN

end LCS.FirstOrder.SyntaxN

namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Definition 6.4.5 (companion): G1nnfDeductionTree.allFormulae / notBoundIn
-- ===================================================================

namespace G1nnfDeductionTree


end G1nnfDeductionTree

-- ===================================================================
-- Definition 6.4.5 (proof-tree contract): occurrence and free-for data
-- ===================================================================

namespace G1nnfProofTree


end G1nnfProofTree


namespace G1nnfRule


end G1nnfRule

namespace G1nnfProofTree


end G1nnfProofTree

-- ===================================================================
-- Definition 6.4.5 adversarial contract checks
-- ===================================================================


-- ===================================================================
-- Private substitution preparation: selective bound-variable renaming
-- ===================================================================



-- ===================================================================
-- Private substitution preparation: proof-tree bound renaming
-- ===================================================================

namespace G1nnfProofTree


end G1nnfProofTree

-- ===================================================================
-- ruleSubstOk: per-rule precondition bundle
-- ===================================================================


-- ===================================================================
-- Private substitution preparation: bound-renaming specifications
-- ===================================================================

namespace G1nnfProofTree


end G1nnfProofTree

/-! ## Set-to-indexed proof-tree bridge

`G1nnfSetDerivable` is the proposition-valued presentation used by the
completeness proof, whereas the Chapter 7 normalization results consume
the Finset-indexed `G1nnfProofTree`.  The following private utilities choose
a Finset representative of a finite set and record the elementary
membership transports used by the bridge. -/


namespace G1nnfProofTree



end G1nnfProofTree



-- ===================================================================
-- Private substitution preparation: local eigenvariable freshening
-- ===================================================================

namespace G1nnfProofTree



end G1nnfProofTree

-- ===================================================================
-- Lemma 6.4.3: substitution preservation (indexed Finset version)
-- ===================================================================

-- ===================================================================
-- Lemma 6.4.4: substitution lemma (indexed Finset version)
-- ===================================================================



namespace G1nnfDeductionTree


end G1nnfDeductionTree



namespace G1nnfDeductionTree


end G1nnfDeductionTree


end LCS.CutElim.Hauptsatz
