import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.Part1
import LCS.FirstOrder.Equality.Search.Part2

/-! # Definition 5.6.3: Equality expansion and round scheduling

The grow operations use the term snapshots, activation counter and branch
records of Definition 5.5.1. At u₁, input heads precede a single equality
packet selected by the round counter and the round-start activation snapshot.
-/

namespace LCS.FirstOrder.Equality.MetaTheorems

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen


end LCS.FirstOrder.Equality.MetaTheorems

namespace LCS.FirstOrder.Equality.Search

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search




end LCS.FirstOrder.Equality.Search
