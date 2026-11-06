import LCS.Item
import LCS.Util
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Syntax.FreeGeneration.Terms
import Attach
import LCS.FirstOrder.Syntax.FreeGeneration.Formulae.ProofsStamp

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

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

@[simp]
theorem toSymbolList_falsum {L : Language} :
    toSymbolList (Formula.falsum (L := L)) = [FormulaSymbol.falsumSym] := rfl

@[simp]
theorem toSymbolList_pred0 {L : Language} (P : L.predSymbols) (hP : L.predArity P = 0) :
    toSymbolList (Formula.pred0 P hP) = [FormulaSymbol.predSym P] := rfl

@[simp]
theorem toSymbolList_predN {L : Language} (P : L.predSymbols) (hP : 0 < L.predArity P)
    (ts : Fin (L.predArity P) → Term L) :
    toSymbolList (Formula.predN P hP ts) = [FormulaSymbol.predSym P] ++
      (List.ofFn (fun i => (Term.toSymbolList (ts i)).map FormulaSymbol.termSym)).flatten := rfl

@[simp]
theorem toSymbolList_eq {L : Language} (hL : L.hasEquality = true) (t1 t2 : Term L) :
    toSymbolList (Formula.eq_ hL t1 t2) = [FormulaSymbol.eqSym] ++
      (Term.toSymbolList t1).map FormulaSymbol.termSym ++
      (Term.toSymbolList t2).map FormulaSymbol.termSym := rfl

@[simp]
theorem toSymbolList_conj {L : Language} (A B : Formula L) :
    toSymbolList (Formula.conj A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connAnd] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

@[simp]
theorem toSymbolList_disj {L : Language} (A B : Formula L) :
    toSymbolList (Formula.disj A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connOr] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

@[simp]
theorem toSymbolList_impl {L : Language} (A B : Formula L) :
    toSymbolList (Formula.impl A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connImpl] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

@[simp]
theorem toSymbolList_equiv {L : Language} (A B : Formula L) :
    toSymbolList (Formula.equiv_ A B) = [FormulaSymbol.lParen] ++ toSymbolList A ++
      [FormulaSymbol.connEquiv] ++ toSymbolList B ++ [FormulaSymbol.rParen] := rfl

@[simp]
theorem toSymbolList_neg {L : Language} (A : Formula L) :
    toSymbolList (Formula.neg A) = [FormulaSymbol.connNeg] ++ toSymbolList A := rfl

@[simp]
theorem toSymbolList_all {L : Language} (i : Nat) (A : Formula L) :
    toSymbolList (Formula.all i A) =
      [FormulaSymbol.quantAll, FormulaSymbol.varSym_ i] ++ toSymbolList A := rfl

@[simp]
theorem toSymbolList_ex {L : Language} (i : Nat) (A : Formula L) :
    toSymbolList (Formula.ex i A) =
      [FormulaSymbol.quantEx, FormulaSymbol.varSym_ i] ++ toSymbolList A := rfl

end Formula

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

/-- Lemma 5.2.5: For any proper prefix w of a formula A (in its
string representation), K(w) ≤ 0. -/
@[blueprint "chap5__lemma_5_2_5" (main := true)]
theorem formula_prefix_k_le_zero {L : Language} (A : Formula L)
    (w rest : List (FormulaSymbol L))
    (hw : Formula.toSymbolList A = w ++ rest)
    (hne : rest ≠ []) :
    formulaListK L w ≤ 0 

-- ===================================================================
-- Lemma 5.2.6: No proper prefix of a formula is a formula
-- ===================================================================

/-- Lemma 5.2.6: No proper prefix of a formula is a formula. If w is both a
proper prefix of A and the string representation of formula B, then K(w) = 1 (by formula_k_eq_one applied to B) but also K(w) ≤ 0 (by formula_prefix_k_le_zero). Contradiction. -/
@[blueprint "chap5__lemma_5_2_6" (main := true)]
theorem formula_prefix_free {L : Language} (A : Formula L)
    (w rest : List (FormulaSymbol L))
    (hw : Formula.toSymbolList A = w ++ rest)
    (hne : rest ≠ []) :
    ¬∃ (B : Formula L), Formula.toSymbolList B = w 

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Prefix-freeness of formulae lifted to an append-cancel principle. -/
theorem fmlaSymList_append_cancel {L : Language}
    (A B : Formula L) (rest1 rest2 : List (FormulaSymbol L))
    (h : Formula.toSymbolList A ++ rest1 = Formula.toSymbolList B ++ rest2) :
    Formula.toSymbolList A = Formula.toSymbolList B ∧ rest1 = rest2 := by
-- BEGIN PROOF
  by_cases hlen : (Formula.toSymbolList A).length < (Formula.toSymbolList B).length
  · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h (by omega)
    have hmid_ne : mid ≠ [] := by
      intro heq; subst heq; simp at hmid_eq
      have := congrArg List.length hmid_eq; omega
    exact absurd ⟨A, rfl⟩ (formula_prefix_free B _ mid hmid_eq hmid_ne)
  · by_cases hlen2 : (Formula.toSymbolList B).length < (Formula.toSymbolList A).length
    · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h.symm (by omega)
      have hmid_ne : mid ≠ [] := by
        intro heq; subst heq; simp at hmid_eq
        have := congrArg List.length hmid_eq; omega
      exact absurd ⟨B, rfl⟩ (formula_prefix_free A _ mid hmid_eq hmid_ne)
    · exact append_cancel_of_length_eq h (by omega)

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Flatten of ofFn of mapped lists equals map applied to the flattened
original lists. -/
theorem flatten_ofFn_map {α β : Type} {n : Nat} (f : α → β) (g : Fin n → List α) :
    (List.ofFn (fun i => (g i).map f)).flatten = ((List.ofFn g).flatten).map f := by
-- BEGIN PROOF
  induction n with
  | zero => simp [List.ofFn]
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons, List.map_append]
    congr 1; exact ih (fun i => g i.succ)

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Formulae with the same symbol string are equal. Predicate atoms of
rank zero and positive rank are distinguished by their predicate symbols'
arities; compound formulae are distinguished by their symbols and subformulae. -/
theorem formula_constructor_range_distinguishable {L : Language}
    (A B : Formula L)
    (h : Formula.toSymbolList A = Formula.toSymbolList B) :
    A = B :=
-- BEGIN PROOF
by
  induction A generalizing B with
  | falsum =>
    cases B with
    | falsum => rfl
    | pred0 _ _ => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | pred0 P hP =>
    cases B with
    | pred0 Q hQ =>
      have hPQ : P = Q := by simpa using h
      subst Q; rfl
    | predN Q hQ ts =>
      have hPQ : P = Q := by
        simpa using congrArg List.head? h
      subst Q; omega
    | falsum => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | predN P hP ts =>
    cases B with
    | pred0 Q hQ =>
      have hPQ : P = Q := by
        simpa using congrArg List.head? h
      subst Q; omega
    | falsum => simp at h
    | predN Q hQ us =>
      simp only [Formula.toSymbolList_predN, List.singleton_append, List.cons_eq_cons] at h
      obtain ⟨hPQ, hrest⟩ := h; cases hPQ; congr 1
      rw [flatten_ofFn_map, flatten_ofFn_map] at hrest
      have hinj : Function.Injective (FormulaSymbol.termSym (L:=L)) :=
        fun _ _ h => FormulaSymbol.termSym.inj h
      have hterm := (List.map_inj_right hinj).mp hrest
      have : ∀ (n : Nat) (ts' us' : Fin n → Term L),
          (List.ofFn (fun i => Term.toSymbolList (ts' i))).flatten =
          (List.ofFn (fun i => Term.toSymbolList (us' i))).flatten →
          ts' = us' := by
        intro n; induction n with
        | zero => intro ts' us' _; funext i; exact i.elim0
        | succ m ihm =>
          intro ts' us' hfl
          rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons] at hfl
          have hcan := termSymList_append_cancel (ts' 0) (us' 0) _ _ hfl
          funext i; match i with
          | ⟨0, _⟩ => exact term_toSymbolList_injective _ _ hcan.1
          | ⟨k + 1, hk⟩ =>
            exact congrFun (ihm (fun j => ts' j.succ) (fun j => us' j.succ) hcan.2) ⟨k, by omega⟩
      exact this _ ts us hterm
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | eq_ _ t1 t2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ u1 u2 =>
      simp only [Formula.toSymbolList_eq] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      rw [← List.map_append, ← List.map_append] at htl
      have hinj : Function.Injective (FormulaSymbol.termSym (L:=L)) :=
        fun _ _ h => FormulaSymbol.termSym.inj h
      have hterm := (List.map_inj_right hinj).mp htl
      have hcan := termSymList_append_cancel t1 u1 _ _ hterm
      have h1 := term_toSymbolList_injective t1 u1 hcan.1
      have h2 := term_toSymbolList_injective t2 u2 hcan.2
      subst h1; subst h2; rfl
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | conj A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | disj A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | impl A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | equiv_ A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | neg A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg C =>
      simp only [Formula.toSymbolList_neg] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have := ihA C htl
      subst this; rfl
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | all i A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all j C =>
      simp only [Formula.toSymbolList_all] at h
      have h2 := List.tail_eq_of_cons_eq h; simp at h2
      obtain ⟨hij, hAC⟩ := h2
      have hA := ihA C hAC
      subst hij; subst hA; rfl
    | ex _ _ => simp at h
  | ex i A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex j C =>
      simp only [Formula.toSymbolList_ex] at h
      have h2 := List.tail_eq_of_cons_eq h; simp at h2
      obtain ⟨hij, hAC⟩ := h2
      have hA := ihA C hAC
      subst hij; subst hA; rfl

namespace FormulaFormationFn

/-- Theorem 5.2.2 (companion): The connective and quantifier formation
operations, with the variable index included in each quantifier operation. -/
@[blueprint "chap5__definition_5_2_3"]
inductive Op where
  | conj | disj | impl | equiv | neg
  | all (i : Nat)
  | ex (i : Nat)

/-- Theorem 5.2.2 (companion): Number of formula-string arguments of an operation. -/
@[blueprint "chap5__definition_5_2_3"]
abbrev Op.arity : Op → Nat
  | .conj | .disj | .impl | .equiv => 2
  | .neg | .all _ | .ex _ => 1

/-- Theorem 5.2.2 (companion): Apply a connective or indexed quantifier
formation function to arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def Op.apply {L : Language} (op : Op)
    : (Fin op.arity → List (FormulaSymbol L)) → List (FormulaSymbol L) :=
  match op with
  | .conj => fun args => c_conj (args 0) (args 1)
  | .disj => fun args => c_disj (args 0) (args 1)
  | .impl => fun args => c_impl (args 0) (args 1)
  | .equiv => fun args => c_equiv (args 0) (args 1)
  | .neg => fun args => c_neg (args 0)
  | .all i => fun args => A_i i (args 0)
  | .ex i => fun args => E_i i (args 0)

end FormulaFormationFn

/-- Theorem 5.2.2: On tuples of formula strings, the connective and
quantifier formation functions are injective, have pairwise disjoint ranges,
and never produce an atomic-formula string. Quantifier operations include
their variable indices. Formula strings are the range of `Formula.toSymbolList`. -/
@[blueprint "chap5__theorem_5_2_2" (main := true)]
theorem formula_free_generation (L : Language) :
    (∀ (op : FormulaFormationFn.Op)
      (ss us : Fin op.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = us i) →
      op.apply ss = op.apply us → ss = us) ∧
    (∀ (op other : FormulaFormationFn.Op), op ≠ other →
      ∀ (ss : Fin op.arity → List (FormulaSymbol L))
        (us : Fin other.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = us i) →
      op.apply ss ≠ other.apply us) ∧
    (∀ (op : FormulaFormationFn.Op) (ss : Fin op.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      ∀ A : Formula L, A.isAtomic → op.apply ss ≠ Formula.toSymbolList A) 

end LCS.FirstOrder.Syntax.FreeGeneration
end
