/- # FOResolution.Method
    Formalization of Chapter 8, Section 8.5.1.
    Separating substitutions, resolvents, and resolution DAGs
    for first-order logic.
    Source: Logic for Computer Science, Gallier 2015
    Content modules: SeparatingPairs (Definition 8.5.1: separating pairs of
    substitutions, signs, conjugates and |S| of literal sets), Resolvents
    (Definition 8.5.2), ResolutionDAGs (Definition 8.5.3), ResolventExample
    (Example 8.5.1), RefutationExample (Example 8.5.2), FreshGroundLanguage and
    FreshGroundLifting (the conservative fresh-constant extension used for
    Lemma 8.5.4 and Theorem 8.5.1: syntax, then transport of separating pairs,
    unifiers, resolvents and resolution trees).
-/
import LCS.FOResolution.Method.SeparatingPairs
import LCS.FOResolution.Method.Resolvents
import LCS.FOResolution.Method.ResolutionDAGs
import LCS.FOResolution.Method.ResolventExample
import LCS.FOResolution.Method.RefutationExample
import LCS.FOResolution.Method.FreshGroundLanguage
import LCS.FOResolution.Method.FreshGroundLifting
