import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.EqualityLists
import LCS.FirstOrder.Equality.Search.Expand
import LCS.FirstOrder.Equality.Search.Procedure
import LCS.FirstOrder.Equality.Search.CompletenessTheorem
import LCS.FirstOrder.Equality.Search.ModelExistence

/-! # Definition 5.6.3: Equality expansion and round scheduling

The grow operations use the term snapshots, activation counter and branch
records of Definition 5.5.1. At u₁, input heads precede a single equality
packet selected by the round counter and the round-start activation snapshot.

Content modules, in book order:
- `Search.EqualityLists` — Section 5.6.4, the equality lists EQ₁,ᵢ, EQ₂,ᵢ, EQ₃,ᵢ.
- `Search.Expand` — Section 5.6.4, Definition 5.6.3, procedure expand for a language with equality
  (branch records, search trees and states, variable activation, instantiation, grow-left/grow-right).
- `Search.Procedure` — Section 5.6.4, Definition 5.6.3, procedure search for a language with equality
  (rounds, halting and output, the limit tree).
- `Search.CompletenessTheorem` — Section 5.6.5, Theorem 5.6.1, the corollary (Gödel's extended
  completeness theorem for G_=), the nontermination remark and the subformula-property remark.
- `Search.ModelExistence` — Section 5.6.6, Theorem 5.6.4 remarks on consistent searches.
-/

namespace LCS.FirstOrder.Equality.Search

end LCS.FirstOrder.Equality.Search
