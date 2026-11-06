/- # FOResolution.Unification
    Formalization of Chapter 8, Section 8.4.1.
    Substitution composition, unifiers, most general unifiers,
    and uniqueness of mgu's.
    Source: Logic for Computer Science, Gallier 2015
    Content modules: Substitutions (Definition 8.4.1), Unifiers (Definition 8.4.2),
    RobinsonStep and RobinsonSolve (Robinson unification of equation systems:
    one transformation step, then the terminating solver and existence of mgu's),
    Examples (Example 8.4.1, with solver checks on its language),
    TwoTreeReduction (Lemma 8.4.1), MGUUniqueness (Lemma 8.4.2).
-/
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers
import LCS.FOResolution.Unification.RobinsonStep
import LCS.FOResolution.Unification.RobinsonSolve
import LCS.FOResolution.Unification.Examples
import LCS.FOResolution.Unification.TwoTreeReduction
import LCS.FOResolution.Unification.MGUUniqueness
