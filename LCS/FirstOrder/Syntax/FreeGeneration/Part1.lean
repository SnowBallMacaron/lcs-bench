import LCS.Item
import LCS.Util
import LCS.FirstOrder.Syntax
import Attach
import LCS.FirstOrder.Syntax.FreeGeneration.Part1.ProofsStamp

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

/-- Lemma 5.2.1 (companion): Individual symbols that appear in the string
representation of a term. A term, when flattened to prefix notation,
consists of variable symbols, constant symbols, and function symbols.
Required to state `symbolK`, `termK`, and Lem 5.2.1 itself. -/
@[blueprint "chap5__definition_5_2_2"]
inductive TermSymbol (L : Language) : Type where
  /-- A variable symbol v_i in the string representation -/
  | varSym : Nat → TermSymbol L
  /-- A constant symbol c in the string representation -/
  | constSym : L.constSymbols → TermSymbol L
  /-- A function symbol f in the string representation -/
  | funSym : L.funSymbols → TermSymbol L

-- ===================================================================
-- Lemma 5.2.4 (companion): FormulaSymbol
-- ===================================================================

/-- Lemma 5.2.4 (companion): Individual symbols appearing in the string
representation of a formula. Extends term symbols with parentheses,
logical connectives, quantifiers, the equality symbol, predicate
symbols, and falsum. Required to state `formulaSymbolK`, `formulaK`,
and Lem 5.2.4 itself. -/
@[blueprint "chap5__definition_5_2_3"]
inductive FormulaSymbol (L : Language) : Type where
  /-- A term-level symbol embedded in the formula string -/
  | termSym : TermSymbol L → FormulaSymbol L
  /-- Left parenthesis '(' -/
  | lParen : FormulaSymbol L
  /-- Right parenthesis ')' -/
  | rParen : FormulaSymbol L
  /-- Conjunction connective ∧ -/
  | connAnd : FormulaSymbol L
  /-- Disjunction connective ∨ -/
  | connOr : FormulaSymbol L
  /-- Implication connective ⊃ -/
  | connImpl : FormulaSymbol L
  /-- Equivalence connective ≡ -/
  | connEquiv : FormulaSymbol L
  /-- Negation connective ¬ -/
  | connNeg : FormulaSymbol L
  /-- Universal quantifier ∀ -/
  | quantAll : FormulaSymbol L
  /-- Existential quantifier ∃ -/
  | quantEx : FormulaSymbol L
  /-- Equality symbol ≐ -/
  | eqSym : FormulaSymbol L
  /-- Predicate symbol P -/
  | predSym : L.predSymbols → FormulaSymbol L
  /-- Falsum symbol ⊥ -/
  | falsumSym : FormulaSymbol L
  /-- Variable symbol (at formula level, for quantifier binding) -/
  | varSym_ : Nat → FormulaSymbol L

-- ===================================================================
-- Lemma 5.2.1 (companion): symbolK — K value of a single symbol
-- ===================================================================

/-- Lemma 5.2.1 (companion): K value of a single symbol — K(variable) = 1,
K(constant) = 1, K(function symbol f of arity n) = 1 - n. The "tail
deficiency" of a symbol is the number of terms that must follow it;
K = 1 - deficiency. -/
@[blueprint "chap5__lemma_5_2_1"]
def symbolK (L : Language) : TermSymbol L → Int
  | .varSym _   => 1
  | .constSym _ => 1
  | .funSym f   => 1 - (L.funArity f : Int)

-- ===================================================================
-- Lemma 5.2.1 (companion): termK — K extended to terms
-- ===================================================================

/-- Lemma 5.2.1 (companion): K extended to terms by structural recursion —
sum of K values of all symbols in the term's string representation.
var x maps to 1, const c maps to 1, func f ts maps to (1 - arity f) +
sum of termK(ts_i). -/
@[blueprint "chap5__lemma_5_2_1"]
def termK {L : Language} : Term L → Int
  | .var _      => 1
  | .const _    => 1
  | .func f ts  =>
    (1 - (L.funArity f : Int)) +
      (List.ofFn (fun i => termK (ts i))).foldl (· + ·) 0

end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace Term



end Term
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace TermFormationFn

/-- Definition 5.2.2 (companion): C_f prepends the function symbol f to
its argument strings concatenated in argument order. The strings may be arbitrary. -/
@[blueprint "chap5__definition_5_2_2"]
def c_f {L : Language} (f : L.funSymbols)
    (args : Fin (L.funArity f) → List (TermSymbol L)) : List (TermSymbol L) :=
  [TermSymbol.funSym f] ++ (List.ofFn args).flatten

end TermFormationFn
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace Term

/-- Lemma 5.2.2 (companion): Flattens a term AST into its linear symbol
sequence (prefix notation string representation). Used to define proper
prefix at the string level for AST terms. -/
@[blueprint "chap5__definition_5_2_2"]
def toSymbolList {L : Language} : Term L → List (TermSymbol L)
  | .var n      => [TermSymbol.varSym n]
  | .const c    => [TermSymbol.constSym c]
  | .func f ts  => TermFormationFn.c_f f (fun i => toSymbolList (ts i))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The symbol string of a function application is its function symbol
followed by the concatenated symbol strings of its arguments. -/
@[simp]
theorem toSymbolList_func {L : Language} (f : L.funSymbols)
    (ts : Fin (L.funArity f) → Term L) :
    toSymbolList (Term.func f ts) = [TermSymbol.funSym f] ++
      (List.ofFn (fun i => toSymbolList (ts i))).flatten := rfl

end Term
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

/-- Lemma 5.2.4 (companion): K value for each formula-level symbol.
K('(') = -1, K(')') = 1, K(∀) = K(∃) = -1 (each quantifier needs a
variable and a formula), K(∧) = K(∨) = K(⊃) = K(≡) = -1, K(¬) = 0,
K(≐) = -1, K(P) = 1-n for n-ary predicate P, K(⊥) = 1. Term symbols
delegate to symbolK. Bound variable symbols at formula level get K = 1
(they are atoms, like term variables). -/
@[blueprint "chap5__lemma_5_2_4"]
def formulaSymbolK (L : Language) : FormulaSymbol L → Int
  | .termSym s  => symbolK L s
  | .lParen     => -1
  | .rParen     => 1
  | .connAnd    => -1
  | .connOr     => -1
  | .connImpl   => -1
  | .connEquiv  => -1
  | .connNeg    => 0
  | .quantAll   => -1
  | .quantEx    => -1
  | .eqSym      => -1
  | .predSym P  => 1 - (L.predArity P : Int)
  | .falsumSym  => 1
  | .varSym_ _  => 1

-- ===================================================================
-- Lemma 5.2.4 (companion): formulaK — K extended to formulae
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.2.4 (companion): sum of Int values in a list. -/
def listIntSum : List Int → Int
  | []      => 0
  | x :: xs => x + listIntSum xs

/-- Lemma 5.2.4 (companion): K extended to formulae by structural recursion,
summing K values of all symbols in the formula's string representation.
Atomic cases use termK for term subexpressions; compound cases combine
connective or quantifier K values with recursive calls.
- Binary connective (A X B): K('(') + K(A) + K(X) + K(B) + K(')') =
  -1 + rec(A) + (-1) + rec(B) + 1
- Negation ¬A: K(¬) + K(A) = 0 + rec(A)
- Quantifier ∀x_i A: K(∀) + K(x_i) + K(A) = -1 + 1 + rec(A) -/
@[blueprint "chap5__lemma_5_2_4"]
def formulaK {L : Language} : Formula L → Int
  | .falsum       => 1
  | .pred0 _ _    => 1
  | .predN P _ ts   =>
    (1 - (L.predArity P : Int)) +
      listIntSum (List.ofFn (fun i => termK (ts i)))
  | .eq_ _ t1 t2 => (-1 : Int) + termK t1 + termK t2
  | .conj A B     =>
    -- ( A ∧ B ): lParen(-1) + A + connAnd(-1) + B + rParen(1)
    (-1 : Int) + formulaK A + (-1 : Int) + formulaK B + 1
  | .disj A B     =>
    -- ( A ∨ B ): lParen(-1) + A + connOr(-1) + B + rParen(1)
    (-1 : Int) + formulaK A + (-1 : Int) + formulaK B + 1
  | .impl A B     =>
    -- ( A ⊃ B ): lParen(-1) + A + connImpl(-1) + B + rParen(1)
    (-1 : Int) + formulaK A + (-1 : Int) + formulaK B + 1
  | .equiv_ A B   =>
    -- ( A ≡ B ): lParen(-1) + A + connEquiv(-1) + B + rParen(1)
    (-1 : Int) + formulaK A + (-1 : Int) + formulaK B + 1
  | .neg A        =>
    -- ¬A: connNeg(0) + A
    formulaK A
  | .all _ A      =>
    -- ∀x_i A: quantAll(-1) + varSym_(1) + A
    formulaK A
  | .ex _ A       =>
    -- ∃x_i A: quantEx(-1) + varSym_(1) + A
    formulaK A

end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace FormulaFormationFn

/-- Definition 5.2.3 (companion): C_P prefixes the predicate symbol P to
arbitrary term-symbol strings concatenated in argument order. -/
@[blueprint "chap5__definition_5_2_3"]
def c_P {L : Language} (P : L.predSymbols)
    (args : Fin (L.predArity P) → List (TermSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.predSym P] ++
    (List.ofFn (fun i => (args i).map FormulaSymbol.termSym)).flatten

/-- Definition 5.2.3 (companion): C_≐ prefixes equality to two arbitrary
term-symbol strings, embedding their letters in the formula alphabet. -/
@[blueprint "chap5__definition_5_2_3"]
def c_eq {L : Language} (s t : List (TermSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.eqSym] ++ s.map FormulaSymbol.termSym ++ t.map FormulaSymbol.termSym

/-- Definition 5.2.3 (companion): Form a parenthesized conjunction
from two arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def c_conj {L : Language} (s t : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.lParen] ++ s ++ [FormulaSymbol.connAnd] ++ t ++ [FormulaSymbol.rParen]

/-- Definition 5.2.3 (companion): Form a parenthesized disjunction
from two arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def c_disj {L : Language} (s t : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.lParen] ++ s ++ [FormulaSymbol.connOr] ++ t ++ [FormulaSymbol.rParen]

/-- Definition 5.2.3 (companion): Form a parenthesized implication
from two arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def c_impl {L : Language} (s t : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.lParen] ++ s ++ [FormulaSymbol.connImpl] ++ t ++ [FormulaSymbol.rParen]

/-- Definition 5.2.3 (companion): Form a parenthesized equivalence
from two arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def c_equiv {L : Language} (s t : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.lParen] ++ s ++ [FormulaSymbol.connEquiv] ++ t ++ [FormulaSymbol.rParen]

/-- Definition 5.2.3 (companion): Prefix negation to an arbitrary formula-symbol string. -/
@[blueprint "chap5__definition_5_2_3"]
def c_neg {L : Language} (s : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.connNeg] ++ s

/-- Definition 5.2.3 (companion): A_i prefixes universal quantification
and variable i to an arbitrary formula-symbol string. -/
@[blueprint "chap5__definition_5_2_3"]
def A_i {L : Language} (i : Nat) (s : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.quantAll, FormulaSymbol.varSym_ i] ++ s

/-- Definition 5.2.3 (companion): E_i prefixes existential quantification
and variable i to an arbitrary formula-symbol string. -/
@[blueprint "chap5__definition_5_2_3"]
def E_i {L : Language} (i : Nat) (s : List (FormulaSymbol L)) : List (FormulaSymbol L) :=
  [FormulaSymbol.quantEx, FormulaSymbol.varSym_ i] ++ s

end FormulaFormationFn
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace Formula

/-- Lemma 5.2.5 (companion): Flattens a formula AST into its linear symbol
sequence (the string representation with parentheses, connectives,
quantifiers, etc.). -/
@[blueprint "chap5__definition_5_2_3"]
def toSymbolList {L : Language} : Formula L → List (FormulaSymbol L)
  | .falsum => [FormulaSymbol.falsumSym]
  | .pred0 P _ => [FormulaSymbol.predSym P]
  | .predN P _ ts => FormulaFormationFn.c_P P (fun i => Term.toSymbolList (ts i))
  | .eq_ _ t1 t2 => FormulaFormationFn.c_eq (Term.toSymbolList t1) (Term.toSymbolList t2)
  | .conj A B => FormulaFormationFn.c_conj (toSymbolList A) (toSymbolList B)
  | .disj A B => FormulaFormationFn.c_disj (toSymbolList A) (toSymbolList B)
  | .impl A B => FormulaFormationFn.c_impl (toSymbolList A) (toSymbolList B)
  | .equiv_ A B => FormulaFormationFn.c_equiv (toSymbolList A) (toSymbolList B)
  | .neg A => FormulaFormationFn.c_neg (toSymbolList A)
  | .all i A => FormulaFormationFn.A_i i (toSymbolList A)
  | .ex i A => FormulaFormationFn.E_i i (toSymbolList A)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp]
theorem toSymbolList_falsum {L : Language} :
    toSymbolList (Formula.falsum (L := L)) = [FormulaSymbol.falsumSym] := rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp]
theorem toSymbolList_pred0 {L : Language} (P : L.predSymbols) (hP : L.predArity P = 0) :
    toSymbolList (Formula.pred0 P hP) = [FormulaSymbol.predSym P] := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_predN {L : Language} (P : L.predSymbols) (hP : 0 < L.predArity P)
    (ts : Fin (L.predArity P) → Term L) :
    toSymbolList (Formula.predN P hP ts) = [FormulaSymbol.predSym P] ++
      (List.ofFn (fun i => (Term.toSymbolList (ts i)).map FormulaSymbol.termSym)).flatten := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_eq {L : Language} (hL : L.hasEquality = true) (t1 t2 : Term L) :
    toSymbolList (Formula.eq_ hL t1 t2) = [FormulaSymbol.eqSym] ++
      (Term.toSymbolList t1).map FormulaSymbol.termSym ++
      (Term.toSymbolList t2).map FormulaSymbol.termSym := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_conj {L : Language} (A B : Formula L) :
    toSymbolList (Formula.conj A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connAnd] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_disj {L : Language} (A B : Formula L) :
    toSymbolList (Formula.disj A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connOr] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_impl {L : Language} (A B : Formula L) :
    toSymbolList (Formula.impl A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connImpl] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_equiv {L : Language} (A B : Formula L) :
    toSymbolList (Formula.equiv_ A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connEquiv] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_neg {L : Language} (A : Formula L) :
    toSymbolList (Formula.neg A) = [FormulaSymbol.connNeg] ++ toSymbolList A := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_all {L : Language} (i : Nat) (A : Formula L) :
    toSymbolList (Formula.all i A) =
      [FormulaSymbol.quantAll, FormulaSymbol.varSym_ i] ++ toSymbolList A := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp]
theorem toSymbolList_ex {L : Language} (i : Nat) (A : Formula L) :
    toSymbolList (Formula.ex i A) =
      [FormulaSymbol.quantEx, FormulaSymbol.varSym_ i] ++ toSymbolList A := rfl

end Formula
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax





/-- Lemma 5.2.1: For any term t over language L, K(t) = 1. Proved by
structural induction on Term L. Base cases (var, const) give K = 1 directly. Inductive case: K(f t1...tn) = (1-n) + n = 1 by the induction hypothesis. -/
@[blueprint "chap5__lemma_5_2_1" (main := true)]
theorem term_k_eq_one {L : Language} (t : Term L) :
    termK t = 1 

-- ===================================================================
-- Theorem 5.2.1: Free generation of TERM_L
-- ===================================================================



-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs, LCS.FirstOrder.Syntax.Parenthesized.Proofs
/-- For a fixed function symbol, equality of applications implies equality
of their argument families. -/
theorem term_func_injective {L : Language} (f : L.funSymbols)
    (ts us : Fin (L.funArity f) → Term L)
    (h : Term.func f ts = Term.func f us) :
    ts = us :=
-- BEGIN PROOF
by
  cases h; rfl

-- retained: used by LCS.FOResolution.Unification.Part1, LCS.FOResolution.Unification.Part2, LCS.FirstOrder.Gentzen.SignedFormulae
/-- Structural size of a term, counting every recursively occurring argument. -/
def termSize {L : Language} : Term L → Nat
  | .var _     => 1
  | .const _   => 1
  | .func _ ts => 1 + (List.ofFn (fun i => termSize (ts i))).foldl (· + ·) 0


-- retained: used by LCS.FirstOrder.Gentzen.SignedFormulae
theorem foldl_add_shift (l : List Nat) (init : Nat) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons]
    rw [ih (init + x), ih x]
    omega

-- retained: used by LCS.FirstOrder.Gentzen.SignedFormulae
theorem foldl_ofFn_ge_elem {L : Language} {n : Nat}
    (ts : Fin n → Term L) (i : Fin n) :
    termSize (ts i) ≤ (List.ofFn (fun j => termSize (ts j))).foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, foldl_add_shift]
    by_cases hi : i.val = 0
    · have heq : i = (0 : Fin (n + 1)) := Fin.ext hi
      rw [heq]
      omega
    · have hi' : 0 < i.val := Nat.pos_of_ne_zero hi
      have hlt : i.val - 1 < n := by omega
      let j : Fin n := ⟨i.val - 1, hlt⟩
      have heq : ts i = ts (Fin.succ j) := by
        congr 1; ext; simp [j]; omega
      rw [heq]
      have h := ih (fun k => ts k.succ) j
      omega

-- retained: used by LCS.FOResolution.Unification.Part1, LCS.FirstOrder.Gentzen.SignedFormulae
/-- Every argument of a function application has strictly smaller termSize
than the whole term. -/
theorem term_sizeOf_func_gt {L : Language}
    (f : L.funSymbols) (ts : Fin (L.funArity f) → Term L)
    (i : Fin (L.funArity f)) :
    termSize (ts i) < termSize (Term.func f ts) :=
-- BEGIN PROOF
by
  simp [termSize]
  have := foldl_ofFn_ge_elem ts i
  omega

-- ===================================================================
-- Lemma 5.2.2: Subterm closure (suffix is term concatenation)
-- ===================================================================





-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2, LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- If a ++ b = c ++ d and a.length ≤ c.length, then ∃ m, c = a ++ m ∧ m ++ d = b. -/
theorem list_split_left {α : Type} {a b c d : List α}
    (h : a ++ b = c ++ d) (hlen : a.length ≤ c.length) :
    ∃ m, c = a ++ m ∧ m ++ d = b := by
-- BEGIN PROOF
  have hsplit := (List.take_append_drop a.length c).symm
  have htak : c.take a.length = a := by
    have h1 : (a ++ b).take a.length = (c ++ d).take a.length := by rw [h]
    simp at h1
    rw [List.take_append_of_le_length (by omega)] at h1
    exact h1.symm
  rw [htak] at hsplit
  refine ⟨c.drop a.length, hsplit, ?_⟩
  have h' : a ++ b = a ++ (c.drop a.length ++ d) := by rw [← List.append_assoc, ← hsplit]; exact h
  exact (List.append_cancel_left h').symm



/-- Lemma 5.2.2: Every nonempty suffix of a term (at the string level) is a
concatenation of one or more terms. Here "suffix" means a suffix of the symbol list representation `Term.toSymbolList t`, and the decomposition gives a nonempty list of terms whose concatenated symbol lists equal the suffix. -/
@[blueprint "chap5__lemma_5_2_2" (main := true)]
theorem term_suffix_is_term_concat {L : Language} (t : Term L)
    (suffix : List (TermSymbol L))
    (hSuffix : suffix <:+ Term.toSymbolList t)
    (hNe : suffix ≠ []) :
    ∃ (terms : List (Term L)),
      terms ≠ [] ∧
      suffix = terms.flatMap Term.toSymbolList 

-- ===================================================================
-- Lemma 5.2.3: No proper prefix of a term is a term
-- ===================================================================

/-- Lemma 5.2.3 (companion): K of a list of term symbols (sum of
individual K values). Used to state string-level properties of terms. -/
@[blueprint "chap5__lemma_5_2_1"]
def termListK (L : Language) : List (TermSymbol L) → Int
  | []      => 0
  | s :: ss => symbolK L s + termListK L ss

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- termListK is additive over list concatenation. -/
theorem termListK_append (L : Language) (a b : List (TermSymbol L)) :
    termListK L (a ++ b) = termListK L a + termListK L b := by
-- BEGIN PROOF
  induction a with
  | nil => simp [termListK]
  | cons x xs ih => simp [termListK, ih]; omega

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- The list-level K value of a term's symbol list equals 1. -/
theorem termListK_toSymbolList {L : Language} (t : Term L) :
    termListK L (Term.toSymbolList t) = 1 := by
-- BEGIN PROOF
  induction t with
  | var n => simp [Term.toSymbolList, termListK, symbolK]
  | const c => simp [Term.toSymbolList, termListK, symbolK]
  | func f ts ih =>
    simp only [Term.toSymbolList_func, List.singleton_append]
    rw [termListK]; simp only [symbolK]
    suffices hsuff : termListK L ((List.ofFn (fun i => Term.toSymbolList (ts i))).flatten) = ↑(L.funArity f) by
      rw [hsuff]; omega
    -- Prove that K of the flattened args = arity
    have hgen : ∀ (n : Nat) (ts' : Fin n → Term L),
        (∀ i, termListK L (Term.toSymbolList (ts' i)) = 1) →
        termListK L ((List.ofFn (fun i => Term.toSymbolList (ts' i))).flatten) = ↑n := by
      intro n
      induction n with
      | zero => intro _ _; simp [List.ofFn, termListK]
      | succ m ihm =>
        intro ts' hts'
        rw [List.ofFn_succ, List.flatten_cons, termListK_append, hts' 0]
        have h := ihm (fun i => ts' i.succ) (fun i => hts' i.succ)
        rw [h]; push_cast; omega
    exact hgen (L.funArity f) ts ih

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- For a proper prefix of the concatenation of term symbol lists,
    the K value of the prefix is ≤ k, where k is related to the number of
    complete terms consumed. Proved using IH on individual terms. -/
theorem termListK_prefix_le {L : Language}
    (n : Nat) (ts : Fin n → Term L)
    (ih : ∀ i, ∀ (w r : List (TermSymbol L)),
      Term.toSymbolList (ts i) = w ++ r → r ≠ [] → termListK L w ≤ 0)
    (w rest : List (TermSymbol L))
    (hw : (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten = w ++ rest)
    (hne : rest ≠ []) :
    termListK L w ≤ ↑n - 1 := by
-- BEGIN PROOF
  induction n generalizing w rest with
  | zero =>
    simp [List.ofFn, List.flatten] at hw
    exact absurd (by cases w <;> simpa using hw) hne
  | succ m ihm =>
    rw [List.ofFn_succ, List.flatten_cons] at hw
    -- hw : toSymbolList (ts 0) ++ (ofFn ...).flatten = w ++ rest
    by_cases hlen : w.length < (Term.toSymbolList (ts 0)).length
    · -- w is a strict prefix of toSymbolList (ts 0)
      obtain ⟨mid, hmid_t, hmid_r⟩ := list_split_left hw.symm (by omega)
      -- hmid_t : toSymbolList (ts 0) = w ++ mid, hmid_r : mid ++ (ofFn ...).flatten = rest
      have hmid_ne : mid ≠ [] := by
        intro h; rw [h] at hmid_t; simp at hmid_t
        have := hmid_t ▸ hlen; omega
      have := ih 0 w mid hmid_t hmid_ne
      push_cast; omega
    · -- w extends past toSymbolList (ts 0)
      obtain ⟨mid, hmid_w, hmid_b⟩ := list_split_left hw (by omega)
      -- hmid_w : w = toSymbolList (ts 0) ++ mid
      -- hmid_b : mid ++ rest = (ofFn fun i => toSymbolList (ts (Fin.succ i))).flatten  ... wait
      -- Actually list_split_left gives us: the second part of c, where a.length ≤ c.length
      -- a = toSymbolList (ts 0), b = (ofFn ...).flatten, c = w, d = rest
      -- Gives: w = toSymbolList (ts 0) ++ mid, mid ++ rest = (ofFn ...).flatten
      rw [hmid_w, termListK_append]
      have hk0 := termListK_toSymbolList (ts 0)
      rw [hk0]
      have hih := ihm (fun i => ts i.succ) (fun i h_w h_r h_hw h_hne => ih i.succ h_w h_r h_hw h_hne)
        mid rest hmid_b.symm hne
      push_cast; omega

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- Every proper prefix of a term's symbol list has K ≤ 0. -/
theorem term_prefix_k_le_zero {L : Language} (t : Term L)
    (w rest : List (TermSymbol L))
    (hw : Term.toSymbolList t = w ++ rest) (hne : rest ≠ []) :
    termListK L w ≤ 0 := by
-- BEGIN PROOF
  induction t generalizing w rest with
  | var n =>
    simp [Term.toSymbolList] at hw
    cases w with
    | nil => simp [termListK]
    | cons x xs =>
      have : xs ++ rest = [] := by
        have := List.tail_eq_of_cons_eq hw; simpa using this
      exact absurd (by cases xs <;> simpa using this) hne
  | const c =>
    simp [Term.toSymbolList] at hw
    cases w with
    | nil => simp [termListK]
    | cons x xs =>
      have : xs ++ rest = [] := by
        have := List.tail_eq_of_cons_eq hw; simpa using this
      exact absurd (by cases xs <;> simpa using this) hne
  | func f ts ih =>
    simp only [Term.toSymbolList_func, List.singleton_append] at hw
    cases w with
    | nil => simp [termListK]
    | cons x xs =>
      have hx := List.head_eq_of_cons_eq hw
      have htl : (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten = xs ++ rest := by
        have := List.tail_eq_of_cons_eq hw; simpa using this
      subst hx
      rw [termListK]; simp only [symbolK]
      have hpfx := termListK_prefix_le (L.funArity f) ts ih xs rest htl hne
      omega

/-- Lemma 5.2.3: No proper prefix of a term is a term. A proper prefix of
Term.toSymbolList t, if it were also a term's toSymbolList, would have K = 1 (by term_k_eq_one) but every proper prefix of a term's symbol list has K ≤ 0. Contradiction. -/
@[blueprint "chap5__lemma_5_2_3" (main := true)]
theorem term_prefix_free {L : Language} (t : Term L)
    (w rest : List (TermSymbol L))
    (hw : Term.toSymbolList t = w ++ rest)
    (hne : rest ≠ []) :
    ¬∃ (s : Term L), Term.toSymbolList s = w 

-- ===================================================================
-- Lemma 5.2.4: For any formula A, K(A) = 1
-- ===================================================================



/-- Lemma 5.2.4: For any formula A over language L, K(A) = 1. Proved by
structural induction on Formula L. Each case reduces to showing K = 1 using term_k_eq_one for term subexpressions and the induction hypothesis for formula subexpressions. -/
@[blueprint "chap5__lemma_5_2_4" (main := true)]
theorem formula_k_eq_one {L : Language} (A : Formula L) :
    formulaK A = 1 

-- ===================================================================
-- Lemma 5.2.5: K(w) ≤ 0 for proper prefix w of formula
-- ===================================================================

/-- Lemma 5.2.5 (companion): K of a list of formula symbols (sum of
individual K values). Used to state string-level properties of formulae. -/
@[blueprint "chap5__lemma_5_2_4"]
def formulaListK (L : Language) : List (FormulaSymbol L) → Int
  | []      => 0
  | s :: ss => formulaSymbolK L s + formulaListK L ss

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- Lemma 5.2.5 (required helper): K is additive over concatenation
of formula symbol lists: K(a ++ b) = K(a) + K(b). -/
theorem formulaListK_append (L : Language) (a b : List (FormulaSymbol L)) :
    formulaListK L (a ++ b) = formulaListK L a + formulaListK L b :=
-- BEGIN PROOF
by
  induction a with
  | nil => simp [formulaListK]
  | cons x xs ih => simp [formulaListK, ih]; omega

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- Bridge: termListK on a mapped list equals the sum of termSymbol K values. -/
theorem formulaListK_map_termSym {L : Language}
    (syms : List (TermSymbol L)) :
    formulaListK L (syms.map FormulaSymbol.termSym) = termListK L syms := by
-- BEGIN PROOF
  induction syms with
  | nil => simp [formulaListK, termListK]
  | cons s ss ih =>
    simp [List.map, formulaListK, termListK, formulaSymbolK, ih]

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- The list-level K value of a formula's symbol list equals 1. -/
theorem formulaListK_toSymbolList {L : Language} (A : Formula L) :
    formulaListK L (Formula.toSymbolList A) = 1 := by
-- BEGIN PROOF
  induction A with
  | falsum => simp [formulaListK, formulaSymbolK]
  | pred0 P h => simp [formulaListK, formulaSymbolK, h]
  | predN P hP ts =>
    simp only [Formula.toSymbolList_predN, List.singleton_append]
    rw [formulaListK]; simp only [formulaSymbolK]
    -- Need: formulaListK of flatten of mapped term lists = predArity P
    suffices h : formulaListK L ((List.ofFn (fun i =>
        (Term.toSymbolList (ts i)).map FormulaSymbol.termSym)).flatten) = ↑(L.predArity P) by
      rw [h]; omega
    have hgen : ∀ (n : Nat) (ts' : Fin n → Term L),
        formulaListK L ((List.ofFn (fun i =>
          (Term.toSymbolList (ts' i)).map FormulaSymbol.termSym)).flatten) = ↑n := by
      intro n; induction n with
      | zero => intro _; simp [List.ofFn, formulaListK]
      | succ m ihm =>
        intro ts'
        rw [List.ofFn_succ, List.flatten_cons, formulaListK_append,
            formulaListK_map_termSym, termListK_toSymbolList]
        have := ihm (fun i => ts' i.succ)
        push_cast; omega
    exact hgen (L.predArity P) ts
  | eq_ _ t1 t2 =>
    simp only [Formula.toSymbolList_eq]
    rw [formulaListK_append, formulaListK_append]
    simp [formulaListK, formulaSymbolK]
    rw [formulaListK_map_termSym, formulaListK_map_termSym]
    rw [termListK_toSymbolList, termListK_toSymbolList]; omega
  | conj A B ihA ihB =>
    simp only [Formula.toSymbolList_conj]
    rw [formulaListK_append, formulaListK_append, formulaListK_append, formulaListK_append]
    rw [ihA, ihB]
    simp [formulaListK, formulaSymbolK]
  | disj A B ihA ihB =>
    simp only [Formula.toSymbolList_disj]
    rw [formulaListK_append, formulaListK_append, formulaListK_append, formulaListK_append]
    rw [ihA, ihB]
    simp [formulaListK, formulaSymbolK]
  | impl A B ihA ihB =>
    simp only [Formula.toSymbolList_impl]
    rw [formulaListK_append, formulaListK_append, formulaListK_append, formulaListK_append]
    rw [ihA, ihB]
    simp [formulaListK, formulaSymbolK]
  | equiv_ A B ihA ihB =>
    simp only [Formula.toSymbolList_equiv]
    rw [formulaListK_append, formulaListK_append, formulaListK_append, formulaListK_append]
    rw [ihA, ihB]
    simp [formulaListK, formulaSymbolK]
  | neg A ihA =>
    simp only [Formula.toSymbolList_neg]
    rw [formulaListK_append]; rw [ihA]
    simp [formulaListK, formulaSymbolK]
  | all i A ihA =>
    simp only [Formula.toSymbolList_all]
    rw [formulaListK_append]; rw [ihA]
    simp [formulaListK, formulaSymbolK]
  | ex i A ihA =>
    simp only [Formula.toSymbolList_ex]
    rw [formulaListK_append]; rw [ihA]
    simp [formulaListK, formulaSymbolK]

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
/-- Decompose a mapped list split into a split of the original list. -/
theorem list_map_append_inv {α β : Type} {f : α → β}
    (xs : List α) (w mid : List β) (h : xs.map f = w ++ mid) :
    ∃ (w' mid' : List α), xs = w' ++ mid' ∧ w'.map f = w ∧ mid'.map f = mid := by
-- BEGIN PROOF
  induction xs generalizing w mid with
  | nil =>
    simp at h
    exact ⟨[], [], by simp, by simp [h.1], by simp [h.2]⟩
  | cons x xs ih =>
    simp at h
    cases w with
    | nil =>
      simp at h
      exact ⟨[], x :: xs, by simp, rfl, by simp [h]⟩
    | cons b bs =>
      simp at h
      obtain ⟨hfxb, hrest⟩ := h
      obtain ⟨w', mid', heq, hw', hmid'⟩ := ih bs mid hrest
      refine ⟨x :: w', mid', ?_, ?_, hmid'⟩
      · simp [heq]
      · simp [hfxb, hw']

-- retained: used by LCS.FirstOrder.Syntax.FreeGeneration.Part2.Proofs
theorem formulaListK_mapped_prefix_le_zero {L : Language} (t : Term L)
    (w mid : List (FormulaSymbol L))
    (hw : (Term.toSymbolList t).map FormulaSymbol.termSym = w ++ mid)
    (hmid_ne : mid ≠ []) :
    formulaListK L w ≤ 0 := by
-- BEGIN PROOF
  obtain ⟨w', mid', hsplit, hw', hmid'⟩ := list_map_append_inv _ w mid hw
  have hmid'_ne : mid' ≠ [] := by
    intro h; subst h; simp at hmid'; exact hmid_ne hmid'
  rw [← hw', formulaListK_map_termSym]
  exact term_prefix_k_le_zero t w' mid' hsplit hmid'_ne

end LCS.FirstOrder.Syntax.FreeGeneration
end

