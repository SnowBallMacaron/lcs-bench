import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction

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

/-- Definition 5.6.3 (companion): Given the round counter RC,
returns j = (RC % 3) + 1, cycling through 1, 2, 3 to select
which type of equality formula to add during each round. -/
def eqCyclingIndex (rc : Nat) : Nat :=
  (rc % 3) + 1

end LCS.FirstOrder.Equality.Completeness

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

/-- Definition 5.6.3 (normalized, companion): Given a list of terms,
enumerates all FormulaN formulae of the form (t =. t) where t ranges
over the given term list. This is the EQ_{1,i} enumeration for the
equality search procedure. Mirrors eqReflFormulae but produces
FormulaN. -/
def eqReflFormulae {L : Language} (hL : L.hasEquality = true)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  terms.map (fun t => FormulaN.eq_ hL t t)

-- ===================================================================
-- Helper: allFinTuples (enumerate all k-tuples from a list)
-- ===================================================================

/-- Definition 5.6.3 (required helper): Enumerate all k-tuples
(Fin k -> alpha) from a list. For k=0, returns the single empty tuple.
For k+1, extends each k-tuple by prepending each element from the list.
Used by eqFuncCongFormulae and eqPredCongFormulae to enumerate all
tuple combinations as required by the textbook's EQ_{2,i} and EQ_{3,i}
(Def 5.6.3). -/
def allFinTuples (ts : List α) : (k : Nat) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 =>
    let prev := allFinTuples ts k
    prev.flatMap fun f =>
      ts.map fun t => fun i => Fin.cases t (fun j => f j) i

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqFuncCongFormulae
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Given a list of function
symbols and a list of terms, enumerates all FormulaN formulae of the
form (s1 =. t1) /\ ... /\ (sn =. tn) => (f(s1,...,sn) =. f(t1,...,tn))
for each function symbol f, where (s1,...,sn) and (t1,...,tn) range over
all n-tuples from the term list. This is the EQ_{2,i} enumeration for
the equality search procedure. Produces FormulaN via
eqCongruenceImplFunc. -/
def eqFuncCongFormulae {L : Language} (hL : L.hasEquality = true)
    (funSyms : List L.funSymbols)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  funSyms.foldl (fun acc f =>
    let tuples := allFinTuples terms (L.funArity f)
    tuples.foldl (fun acc2 ss =>
      tuples.foldl (fun acc3 ts =>
        acc3 ++ [eqCongruenceImplFunc L hL f ss ts]
      ) acc2
    ) acc
  ) []

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqPredCongFormulae
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Given a list of predicate
symbols and a list of terms, enumerates all FormulaN formulae of the
form ((s1 =. t1) /\ ... /\ (sn =. tn) /\ P(s1,...,sn)) => P(t1,...,tn)
for each predicate symbol P, where (s1,...,sn) and (t1,...,tn) range
over all n-tuples from the term list. Also includes the binary equality
predicate: for every pair of term pairs (s1,s2), (t1,t2), it adds
(s1 ≐ t1 ∧ (s2 ≐ t2 ∧ s1 ≐ s2)) ⊃ t1 ≐ t2 via `eqCongruenceImplEq`.
This is the EQ_{3,i} enumeration for the equality search procedure. -/
def eqPredCongFormulae {L : Language} (hL : L.hasEquality = true)
    (predSyms : List L.predSymbols)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  let predFormulae :=
    predSyms.foldl (fun acc P =>
      let tuples := allFinTuples terms (L.predArity P)
      tuples.foldl (fun acc2 ss =>
        tuples.foldl (fun acc3 ts =>
          acc3 ++ [eqCongruenceImplPred L hL P ss ts]
        ) acc2
      ) acc
    ) []
  let pairs := allFinTuples terms 2
  predFormulae ++ pairs.flatMap fun ss =>
    pairs.map fun ts => eqCongruenceImplEq hL (ss 0) (ss 1) (ts 0) (ts 1)

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqAxiomBatch
-- ===================================================================

/-- Definition 5.6.3 (companion): Finite stages of the term closure of the
initial generators under the functions of the input reduct. Their union
contains terms of every finite function depth. -/
def eqLevelZeroTerms {L : Language} (funSyms : List L.funSymbols)
    (generators : List (Term L)) : Nat → List (Term L)
  | 0 => generators
  | n + 1 =>
    let prev := eqLevelZeroTerms funSyms generators n
    prev ++ funSyms.flatMap fun f =>
      (allFinTuples prev (L.funArity f)).map (Term.func f)

/-- Definition 5.6.3 (companion): A lazy formula enumeration presented by
finite stages and the formulas already consumed. -/
structure EqFormulaStream (L : Language) where
  stages : Nat → List (FormulaN L)
  consumed : List (FormulaN L) := []

/-- Definition 5.6.3 (companion): Empty enumeration. -/
def EqFormulaStream.empty {L : Language} : EqFormulaStream L := ⟨fun _ => [], []⟩

/-- Definition 5.6.3 (companion): The first unconsumed formula in the least
stage containing one. Returns none exactly when the enumeration is exhausted. -/
noncomputable def EqFormulaStream.head? {L : Language} (stream : EqFormulaStream L) :
    Option (FormulaN L) := by
  classical
  let remaining := fun n => (stream.stages n).filter (fun A => A ∉ stream.consumed)
  exact if h : ∃ n, (remaining n).isEmpty = false then
    (List.range (h.choose + 1)).findSome? (fun n => (remaining n).head?)
  else none

/-- Definition 5.6.3 (companion): Delete the head from a lazy enumeration.
All occurrences of that formula are skipped in later stages. -/
noncomputable def EqFormulaStream.tail {L : Language} (stream : EqFormulaStream L) :
    EqFormulaStream L :=
  match stream.head? with
  | none => stream
  | some A => { stream with consumed := A :: stream.consumed }

end LCS.FirstOrder.Equality.Completeness
end
