import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
import LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
import LCS.FirstOrder.Gentzen.Search.NoFunction.Search
import LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
import LCS.FirstOrder.Gentzen.Search.NoFunction.Examples

/-! # FirstOrder.Gentzen.Search.NoFunction
    Faithful formalization of Definition 5.4.9 — the search procedure
    for first-order languages WITHOUT function symbols and WITHOUT
    equality (Gallier §5.4.7).

    State and operation names follow the textbook pseudocode verbatim.
    Procedures are organised as `search`, `expand`, `growLeft`,
    `growRight`, mirroring §5.4.9 one-to-one. `SearchTree` stores
    formula-use records at its leaves and forgets them to a
    `GDeductionTreeExt` with the same sequents and inferences.

    Because the search-state manipulation uses `List.filter` and
    `List.any` over `FormulaN`, and the ambient
    `instDecidableEqFormulaN` in `SyntaxN.lean` is `noncomputable`
    (classical-propositional), every operation that consumes TERM₀'s
    per-record FORM₀(k) usage list inherits `noncomputable`. This is a
    typeclass-level `noncomputable`, not an oracle — no `Classical.em`,
    no `Exists.choose`, no `by_cases on ¬ provability`. The algorithm
    is deterministic; the `noncomputable` annotation records only that
    the kernel cannot reduce `List.contains` on `FormulaN` values.
-/

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka


namespace SearchTree


end SearchTree

-- ===================================================================
-- Definition 5.4.9: SearchState
-- ===================================================================


namespace SearchState


end SearchState

-- ===================================================================
-- Definition 5.4.9: initial TERM₀ and AVAIL₀
-- ===================================================================


namespace SearchState


end SearchState


namespace SearchState


end SearchState




-- ===================================================================
-- Tree-level grow-left / grow-right (§5.4.9 "extend every nonaxiom leaf")
-- ===================================================================


end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka


end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka


end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction


end LCS.FirstOrder.Gentzen.Hintikka

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic LCS.FirstOrder.Gentzen


end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction


end LCS.FirstOrder.Gentzen.Hintikka
