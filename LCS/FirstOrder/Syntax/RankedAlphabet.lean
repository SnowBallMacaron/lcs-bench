import LCS.FirstOrder.Basic
import Attach
import LCS.FirstOrder.Syntax.RankedAlphabet.ProofsStamp

/-! # Many-sorted ranked alphabets

The alphabet and rank data shared by first-order syntax and labeled graphs.
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 10.6.1 (companion): An S-sorted ranked alphabet Σ of a
labeled graph. Mirrors the §10.2 ranked-alphabet shape
`(List SortType) × SortType` used by `MSLanguage.funRank`: the rank of
a symbol `f` is `r(f) = (u_1…u_n, s)`, where the first component is the
arity string `u_1…u_n ∈ S^*` (empty `[]` exactly for leaf/constant
symbols of rank `(e, s)`) and the second component is the result sort
`s ∈ S`. -/
@[blueprint "chap10__definition_10_6_1"]
structure MSRankedAlphabet : Type 1 where
  /-- The index sort set `S`. -/
  SortType : Type
  /-- The carrier of symbols Σ of the alphabet. -/
  symbols : Type
  /-- The rank function `r : Σ → S^* × S`, `r(f) = (u_1…u_n, s)`. -/
  rank : symbols → (List SortType) × SortType

namespace MSRankedAlphabet

/-- Definition 10.6.1 (companion): The result-sort component `s ∈ S` of a
symbol's rank `r(f) = (u_1…u_n, s)`. -/
@[blueprint "chap10__definition_10_6_1"]
def resultSort (A : MSRankedAlphabet) (f : A.symbols) : A.SortType :=
  (A.rank f).2

/-- Definition 10.6.1 (companion): The arity string `u_1…u_n` of a symbol
under the rank function `r(f) = (u_1…u_n, s)`. -/
@[blueprint "chap10__definition_10_6_1"]
def argSorts (A : MSRankedAlphabet) (f : A.symbols) : List A.SortType :=
  (A.rank f).1

end MSRankedAlphabet

end LCS.FirstOrder.ManySorted.CongruenceClosure
