import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.SHGTheorem.Part1
import LCS.Herbrand.SHGTheorem.Part2
import LCS.Herbrand.SHGTheorem.Part3

/-! # Herbrand.SHGTheorem
    Formalization of Chapter 7, Sections 6.1-6.3: Skolem Normal Form
    and Compound Instances.

    Covers Definitions 7.6.1-7.6.3 (universal scope, Skolem form,
    compound instances), and Examples 7.6.1-7.6.4.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

-- ===================================================================
-- Definition 7.6.1: USPair — Universal Scope derivation tree
-- ===================================================================


namespace ShgMotivProof

set_option backward.isDefEq.respectTransparency false

open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae

variable [DecidableEq F]


end ShgMotivProof

namespace ShgMotivProof

variable [DecidableEq F]


end ShgMotivProof


namespace ShgMotivTransformedProof

set_option backward.isDefEq.respectTransparency false

open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae

variable [DecidableEq F]


open ShgMotivProof (substVec1 substVec2)


end ShgMotivTransformedProof


namespace ShgMotivProof

variable [DecidableEq F]


end ShgMotivProof


-- Variables for Example 7.6.2: x = 0, y = 1, z = 2, u = 3, w = 4.

-- ===================================================================
-- Example 7.6.2: usExFormula
-- ===================================================================


-- ===================================================================
-- Definition 7.6.2 allocation regressions
-- ===================================================================

namespace SkolemAllocationRegression


end SkolemAllocationRegression

-- ===================================================================
-- Definition 7.6.2 (companion def): SkolemLanguage.symbolLookup
-- ===================================================================


namespace SkolemAllocationRegression


end SkolemAllocationRegression

-- ===================================================================
-- Definition 7.6.3 (companion def): CInstance.toFormula
-- ===================================================================

namespace CInstance


end CInstance

end LCS.Herbrand.SHGTheorem

-- ===================================================================
-- Definition 7.6.3 (companion def): CInstance.WellFormed
-- ===================================================================

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution


-- ===================================================================
-- Example 7.6.3 (companion type): SKExSkolemFunc
-- ===================================================================

section SkExComputation

set_option backward.isDefEq.respectTransparency false


end SkExComputation

-- ===================================================================
-- Example 7.6.4 (companion type): CInstExPred
-- ===================================================================


namespace CInstance


end CInstance

end LCS.Herbrand.SHGTheorem
