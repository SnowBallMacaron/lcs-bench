import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Equality.Completeness.EqualityAxiomLists

section

namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch
open LCS.FirstOrder.Completeness

-- ===================================================================
-- Definition 5.6.3 (normalized): SearchStateEq
-- ===================================================================

/-- Definition 5.6.3: The search state for the equality search procedure
using FormulaN types (extends Def 5.4.9). -/
structure SearchStateEq (L : Language) where
  /-- The base normalized search state from Def 5.4.9 -/
  base : Hintikka.SearchState L
  /-- Round counter RC, incremented at the end of each round,
      used to cycle through equality formula types via
      j = (RC mod 3) + 1 -/
  roundCounter : Nat
  /-- NUMACT: counter of activated new variables -/
  numact : Nat
  /-- EQ_{1,i}: maps index i to the remaining reflexivity formulae
      (t =. t) at index i, as FormulaN -/
  eq1 : Nat → EqFormulaStream L
  /-- EQ_{2,i}: maps index i to the remaining function congruence
      formulae at index i, as FormulaN -/
  eq2 : Nat → EqFormulaStream L
  /-- EQ_{3,i}: maps index i to the remaining predicate congruence
      formulae at index i, as FormulaN -/
  eq3 : Nat → EqFormulaStream L

namespace SearchStateEq

/-- Definition 5.6.3 (normalized, companion): Returns EQ_{j,i} for
given j (1, 2, or 3) and i from the normalized equality search state.
For j=1, returns eq1 i (reflexivity formulae at index i).
For j=2, returns eq2 i (function congruence formulae at index i).
For j=3, returns eq3 i (predicate congruence formulae at index i).
For other values of j, returns the empty enumeration. -/
def eqListForIndex {L : Language} (st : SearchStateEq L)
    (j i : Nat) : EqFormulaStream L :=
  match j with
  | 1 => st.eq1 i
  | 2 => st.eq2 i
  | 3 => st.eq3 i
  | _ => .empty

/-- Definition 5.6.3 (normalized, companion): Initialize the equality
search state from a normalized sequent. The textbook says:
'let L' be the reduct of L consisting of all constant, function, and
predicate symbols occurring in formulae in Gamma0 -> Delta0' and
'Let TERM0, EQ_{1,i}, EQ_{2,i}, EQ_{3,i} and AVAIL_i, 0 ≤ i, be
initialized as explained above. NUMACT := 0; RC := 0.'
The caller provides the reduct L' via `funSyms` (function symbols in
the sequent), `predSyms` (predicate symbols), and `initialTerms`
(terms from TERM0, built from L' constants/functions and free vars).
EQ_{j,0} lazily enumerates formulae over the full function closure of
these initial generators, including y₀ when the input has no constants
or free variables.
For i >= 1, EQ_{j,i} uses AVAIL_i terms (activated during the search).
At initialization only i=0 is active (NUMACT=0). -/
def init {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (funSyms : List L.funSymbols)
    (predSyms : List L.predSymbols)
    (initialTerms : List (Term L)) :
    SearchStateEq L :=
  let baseState := Hintikka.SearchState.init seq
  { base := baseState
  , roundCounter := 0
  , numact := 0
  , eq1 := fun i =>
      if i = 0 then ⟨fun n => eqReflFormulae hL (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty
  , eq2 := fun i =>
      if i = 0 then ⟨fun n => eqFuncCongFormulae hL funSyms
        (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty
  , eq3 := fun i =>
      if i = 0 then ⟨fun n => eqPredCongFormulae hL predSyms
        (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty }

end SearchStateEq

/-- Definition 5.6.3 (companion, normalized): At the end of every expansion step,
adds the head of EQ_{j,i} for all i = 0,...,NUMACT to the antecedent
of the given leaf Sequent, where j = eqCyclingIndex(RC). The textbook
(Def 5.6.3) says: 'for i:=0 to NUMACT_0 do Gamma' := Gamma',
head(EQ_{j,i}) endfor'. Returns the augmented Sequent with equality
axiom heads appended after the rightmost antecedent formula, in increasing
index order. Empty EQ lists contribute no formula. -/
noncomputable def injectEqFormulae {L : Language} (st : SearchStateEq L)
    (seq : Sequent L) : Sequent L :=
  let j := eqCyclingIndex st.roundCounter
  let numact := st.numact
  -- Collect the head of EQ_{j,i} for i = 0, ..., numact
  let heads := (List.range (numact + 1)).filterMap fun i =>
    (st.eqListForIndex j i).head?
  { antecedent := seq.antecedent ++ heads
  , succedent := seq.succedent }

-- ===================================================================
-- Definition 5.6.3 (normalized): branchStepEqN (moved before SearchTreeDataEq)
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): One branching expansion step with
equality injection. Composes branchStep (which applies linear type-A/C/D
decomposition via searchClosureStep AND adds type-B component selection
based on the branching bit) with injectEqFormulae (which adds EQ heads
to the antecedent).

At depth n, uses terms enumerate 0..n for type-C instantiation,
var(freshBase+n) for type-D witnesses, and the branching bit for type-B
component selection. Then injects EQ_{j,i} heads from the given
SearchStateEq. This is the equality-aware analogue of branchStep. -/
noncomputable def branchStepEqN {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth : Nat) (freshBase : Nat)
    (bit : Nat) (st : SearchStateEq L)
    (rootSeq : Sequent L) : Sequent L :=
  let branched := branchStep prev depth freshBase bit rootSeq
  injectEqFormulae st branched

end LCS.FirstOrder.Equality.Completeness
end
