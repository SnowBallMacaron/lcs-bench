import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.LeafExpansion
import LCS.Propositional.Systems.G.Search.SearchRounds
import LCS.Propositional.Systems.G.Search.Validity
import LCS.Propositional.Systems.G.Search.Falsification
import LCS.Propositional.Systems.G.Search.Termination
import LCS.Propositional.Systems.G.Search.OccurrenceSchedule

/-! # Propositional.Systems.G.Search
    Formalization of Chapter 3, Sections 3.4.6-3.4.7.
    Defines the search procedure and proves completeness of G'.
-/

namespace LCS.Propositional.Systems.G.Search

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G


-- ATTACH-BLOCKER: variable
variable {mode : SearchMode}

-- ========= Definition 3.4.6: Helper predicates =========


-- List reconstruction: take i ++ [L[i]] ++ drop (i+1) = L



-- Helper: foldl (+) n L >= n


-- Helper: if foldl (+) 0 (map f L) = 0, then f a = 0 for all a in L


-- Helper: sequentComplexity 0 implies all formulas have complexity 0


-- Helper: formula with complexity 0 is a variable


-- Helper: foldl (+) n L = n + foldl (+) 0 L


-- Helper: foldl (+) 0 L = L.sum (where sum uses foldr)


-- Helper: sequentComplexity expressed via List.sum


-- Helper: valid sequent where all formulas are variables must be an axiom


-- Helper: valid sequent with all-variable formulas is provable


-- ========= Theorem 3.4.1: Backward validity helpers =========

-- Re-proved membership helpers (needed since originals in G.lean are private)










-- List splitting


-- foldl/sum conversion for complexity proofs








-- Complexity decrease for GentzenStep1


-- Complexity decrease for GentzenStep2


-- Backward validity: valid conclusion implies valid premise (GentzenStep1)

-- Backward validity: valid conclusion implies valid premises (GentzenStep2)

-- Finding a complex formula in a sequent with positive complexity


-- Classification of complex formulas


-- ========= Theorem 3.4.1: WFTree and falsification propagation =========


-- Helper: the set of variable indices occurring in a PropFormulaNormalized


-- Helper: evalExtN depends only on variables occurring in the formula


-- Helper: n ∈ formulaVarsN A → n ∈ formulaVarIndices A


-- Helper: variable indices of a formula in a sequent are in sequentVarIndices


-- Helper: allValuations covers all valuations on the given variable indices


-- Helper: checkSequentValidFor correctness



-- ========= Complexity bounds =========

-- Helper: foldl max a L = max a (foldl max 0 L)


-- Helper: element of L is ≤ foldl max 0 L


-- Helper: foldl max 0 L < bound when every element < bound and L is nonempty


-- Helper: standard unfinished leaf has positive complexity


-- ========= expandLeaf properties: helpers =========

-- findFirstNonatomic specification (auxiliary with offset k)


-- findFirstNonatomic specification (main, k=0)


-- Sequent antecedent reconstruction


-- Sequent succedent reconstruction


-- ========= Property 1: expandLeaf_conclusion =========



-- ========= Property 2: expandLeaf_wf =========



-- ========= Property 3: expandLeaf_leaves_complexity_lt =========

-- Helper: findFirstNonatomic returning none means all formulas are atomic


-- Helper: nonatomic formulas have positive complexity
























-- ========= Theorem 1: searchRound_complexity_decrease =========

-- Helper: unfinished leaf complexity is ≤ maxUnfinishedLeafComplexity


-- Helper: membership in unfinishedLeaves implies not finished


-- Helper: unfinishedLeaves is non-empty when tree is not finished


-- Helper: every unfinished leaf of searchRound dt has complexity < max


-- Helper: max unfinished leaf complexity is positive when tree is not finished


-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (findFirstNonatomic_atomic_prefix)
























-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search.Fairness

end LCS.Propositional.Systems.G.Search
