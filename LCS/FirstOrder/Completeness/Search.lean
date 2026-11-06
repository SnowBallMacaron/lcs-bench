import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.Variables
import LCS.FirstOrder.Completeness.Search.RenamingApart
import LCS.FirstOrder.Completeness.Search.TermEnumerations
import LCS.FirstOrder.Completeness.Search.SearchState
import LCS.FirstOrder.Completeness.Search.GrowLeftRight
import LCS.FirstOrder.Completeness.Search.Procedure
import LCS.FirstOrder.Completeness.Search.InfiniteTree
import LCS.FirstOrder.Completeness.Search.Examples

/-! # Input terms and variable supply for the §5.5.1 search procedure

Even indices name the input variables x₀, x₁, …; odd indices name the
reserved variables y₀, y₁, …. Input formulae use only x variables, both
free and bound. The parity renaming of `InfiniteSearch` supplies such formulae.
Admissible TERMS and AVAIL enumerations determine the initial term records
and availability streams for the occurrence language of the input.
-/

namespace LCS.FirstOrder.Completeness.Search
end LCS.FirstOrder.Completeness.Search
