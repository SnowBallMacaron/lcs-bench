import LCS.SLD.FirstOrder.AdditionExample
import LCS.SLD.FirstOrder.SLDDerivations
import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.Soundness
import LCS.SLD.FirstOrder.GroundLifting
import LCS.SLD.FirstOrder.GroundInstances
import LCS.SLD.FirstOrder.GroundSemantics
import LCS.SLD.FirstOrder.PropositionalEncoding
import LCS.SLD.FirstOrder.Completeness

/-! # SLD.FirstOrder (Section 9.4)
    Source: Logic for Computer Science, Gallier 2015

    First-order SLD-resolution: Horn clauses in PROLOG notation,
    SLD-derivations with unification and separating substitutions,
    soundness and completeness via lifting.
-/

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness


-- ===================================================================
-- Definition 9.4.1 (companion defs): isDefinite, headAtom, bodyAtoms,
-- toFOClause
-- ===================================================================

namespace FOHornClause


end FOHornClause


-- ===================================================================
-- Definition 9.4.2 (companion defs): length, isRefutation,
-- selectedAtom, inputClause, resultSubstitution, firstSelectedAtom
-- ===================================================================

namespace FOSLDDerivation


end FOSLDDerivation

-- ===================================================================
-- Example 9.4.1: Addition program SLD-refutation
-- ===================================================================

-- Companion types for the addition example language


-- ===================================================================
-- Definition 9.4.1 (companion): Unsatisfiability of a Horn clause set
-- via translation to standard FOClauses
-- ===================================================================

namespace FOHornClauseSet


end FOHornClauseSet

-- ===================================================================
-- Definition 9.4.1 (companion): Horn-clause-set to FormulaN encoding
-- ===================================================================



-- ===================================================================
-- Hash-language infrastructure regressions
-- ===================================================================

namespace HashLanguageRegression


end HashLanguageRegression

-- ===================================================================
-- Horn-clause encoding: NNF / Rectification / Sentence lemmas for SkolemSpec
-- ===================================================================


-- ===================================================================
-- Lemma 9.4.1 (helpers): formulaSubstAll evaluation bridge
-- ===================================================================


namespace FOSLDDerivation


end FOSLDDerivation


namespace FOSLDDerivation


end FOSLDDerivation



-- ===================================================================
-- Direct hash-ground adapter regressions
-- ===================================================================

namespace HashGroundAdapterRegression


end HashGroundAdapterRegression

-- ===================================================================
-- Theorem 9.4.1 (helpers): SHG + lifting chain and selection independence
-- ===================================================================






namespace GroundUnsatContractRegression

open LCS.FirstOrder.SyntaxN.Variables


end GroundUnsatContractRegression


end LCS.SLD.FirstOrder
