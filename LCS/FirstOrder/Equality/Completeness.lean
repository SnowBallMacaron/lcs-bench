import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Equality.Completeness.EqualityAxiomLists
import LCS.FirstOrder.Equality.Completeness.SearchRounds
import LCS.FirstOrder.Equality.Completeness.HintikkaConditions
import LCS.FirstOrder.Equality.Completeness.SignedLimitSet
import LCS.FirstOrder.Equality.Completeness.SearchTreePaths
import LCS.FirstOrder.Equality.Completeness.CompletenessTheorem

/-! # FirstOrder.Equality.Completeness
    Formalization of Chapter 5, Sections 5.6.4-5.6.5.
    Search procedure and completeness for languages with equality.
    Source: Logic for Computer Science, Gallier 2015

    Content modules, in book order:
    - `Completeness.EqualityAxiomLists` — Section 5.6.4, the equality lists EQⱼ,ᵢ in list form and the cycling index j = (RC mod 3) + 1
    - `Completeness.SearchRounds` — Section 5.6.4, Definition 5.6.3, search state, rounds and branch steps
    - `Completeness.HintikkaConditions` — Section 5.6.5, proof of Theorem 5.6.1, the claim's conditions H6(i)-(iii) for the search closure and falsification in the quotient
    - `Completeness.SignedLimitSet` — Section 5.6.5, the equality-aware signed limit set and its Hintikka property
    - `Completeness.SearchTreePaths` — Section 5.6.5, proof of Theorem 5.6.1, search tree data and the Hintikka properties of its paths
    - `Completeness.CompletenessTheorem` — Section 5.6.5, Theorem 5.6.1 and the corollary, via the constructed search tree
-/

namespace LCS.FirstOrder.Equality.Completeness

end LCS.FirstOrder.Equality.Completeness
