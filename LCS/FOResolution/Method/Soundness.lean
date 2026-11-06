/- # FOResolution.Method.Soundness
    Formalization of Chapter 8, Section 8.5.2.
    Soundness of the resolution method for first-order logic
    without equality.
    Source: Logic for Computer Science, Gallier 2015
    Content modules: ClauseSemantics (clauses as universally closed
    disjunctions: satisfaction, validity, unsatisfiability), SubstitutionLemma
    (evaluation under substitution), ResolventValidity (Lemma 8.5.1) and
    ResolutionSoundness (Lemma 8.5.2).
-/
import LCS.FOResolution.Method.Soundness.ClauseSemantics
import LCS.FOResolution.Method.Soundness.SubstitutionLemma
import LCS.FOResolution.Method.Soundness.ResolventValidity
import LCS.FOResolution.Method.Soundness.ResolutionSoundness
