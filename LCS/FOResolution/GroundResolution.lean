/- # FOResolution.GroundResolution
    Formalization of Chapter 8, Section 8.3.
    Ground resolution method and its completeness for ground clauses.
    Source: Logic for Computer Science, Gallier 2015
    Content modules: GroundClauses (ground clauses, their satisfaction and
    ground substitution instances), ResolutionTrees (ground resolution trees and
    refutations), Example (Example 8.3.1), PropositionalTranslation and Completeness
    (Lemma 8.3.1: completeness of ground resolution via the propositional method,
    with the equality caveat), ThreeStepProcedure (the ground resolution method:
    clause form, ground instances, ground resolution), CompoundInstanceSearch
    (Section 8.1: systematic search of compound instances with a tester) and
    Undecidability (Section 8.1: Church's theorem).
-/
import LCS.FOResolution.GroundResolution.GroundClauses
import LCS.FOResolution.GroundResolution.ResolutionTrees
import LCS.FOResolution.GroundResolution.Example
import LCS.FOResolution.GroundResolution.PropositionalTranslation
import LCS.FOResolution.GroundResolution.Completeness
import LCS.FOResolution.GroundResolution.ThreeStepProcedure
import LCS.FOResolution.GroundResolution.CompoundInstanceSearch
import LCS.FOResolution.GroundResolution.Undecidability
