import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import Attach
import LCS.CutElim.Interpolation.Symbols.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Lemma 6.5.2 (required def): formulaPredSymbolsN
-- ===================================================================

/-- Lemma 6.5.2 (required): The set of predicate symbols occurring in
a formula, extracted as the third component of formulaPredSymbolsN. -/
@[blueprint "chap6__lemma_6_5_2"]
def formulaPredSymbolsN {L : Language} : FormulaN L → Set L.predSymbols
  | .predN P _ => fun Q => Q = P
  | .eq_ _ _ _ => ∅
  | .neg A => formulaPredSymbolsN A
  | .conj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .disj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .impl A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .all _ A => formulaPredSymbolsN A
  | .ex _ A => formulaPredSymbolsN A

-- ===================================================================
-- Lemma 6.5.2 (required def): formulaConstSymbolsN
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a term, recursing through subterms. -/
@[blueprint "chap6__lemma_6_5_2"]
def termConstSymbols {L : Language} : Term L → Set L.constSymbols
  | .var _ => ∅
  | .const c => fun d => d = c
  | .func _ ts => fun c => ∃ i, termConstSymbols (ts i) c

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a formula, recursing through subformulae and
subterms. -/
@[blueprint "chap6__lemma_6_5_2"]
def formulaConstSymbolsN {L : Language} : FormulaN L → Set L.constSymbols
  | .predN _ ts => fun c => ∃ i, termConstSymbols (ts i) c
  | .eq_ _ t1 t2 => termConstSymbols t1 ∪ termConstSymbols t2
  | .neg A => formulaConstSymbolsN A
  | .conj A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .disj A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .impl A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .all _ A => formulaConstSymbolsN A
  | .ex _ A => formulaConstSymbolsN A

-- ===================================================================
-- Lemma 6.5.2 (required def): listFormulaPredSymbols
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of predicate symbols
occurring in a list of formulae. Used in `IsInterpolant` to express
that the interpolant's predicate symbols appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaPredSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.predSymbols :=
  fun P => ∃ A ∈ fs, formulaPredSymbolsN A P

-- ===================================================================
-- Lemma 6.5.2 (helper def): listFormulaConstSymbols
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a list of formulae. Used in `IsInterpolant` to express
that the interpolant's constant symbols appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaConstSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.constSymbols :=
  fun c => ∃ A ∈ fs, formulaConstSymbolsN A c

-- ===================================================================
-- Lemma 6.5.2 (helper def): listFormulaFV
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of free variables occurring
in a list of formulae. Used in `IsInterpolant` to express that the
interpolant's free variables appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaFV {L : Language}
    (fs : List (FormulaN L)) : Set Nat :=
  fun v => ∃ A ∈ fs, formulaFVN A v

-- Substitution symbol preservation lemmas

-- Remaining substitution helper lemmas





-- ===================================================================
-- Monotonicity helpers for symbol containment in interpolation
-- ===================================================================

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

end LCS.CutElim.Interpolation
end
