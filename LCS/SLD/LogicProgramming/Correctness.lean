import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.RefutationExamples
import LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
import LCS.SLD.LogicProgramming.Correctness.Correctness

/-! # SLD.LogicProgramming.Correctness (Section 9.5.3)
    Source: Logic for Computer Science, Gallier 2015

    Correctness of SLD-resolution as a computational procedure:
    Lemma 9.5.3 (unsatisfiability of substituted clause set),
    Theorem 9.5.1 (correctness of SLD-resolution), and
    Example 9.5.4 (four SLD-refutations for the logic program
    from Example 9.5.1).
-/

namespace LCS.SLD.LogicProgramming.Correctness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.LogicProgramming

-- ===================================================================
-- Finset ↔ list bridge helpers. `IsSeparatingPair` and `hStdApart`
-- reference the previous goal only via `clauseFV`, which is
-- permutation/mem-invariant. We use these bridges to transport existing
-- example hSep/hStdApart helpers (stated on concrete lists) across the
-- Finset-toList round-trip required by the new indexed SLD API.
-- ===================================================================

-- -------------------------------------------------------------------
-- Refutation (ii): decomposed step-by-step (same shape as (i) with susan).
-- -------------------------------------------------------------------


-- ===================================================================
-- Lemma 9.5.3: Unsatisfiability of substituted clause set
-- ===================================================================


end LCS.SLD.LogicProgramming.Correctness
