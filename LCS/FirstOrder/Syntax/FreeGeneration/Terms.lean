import LCS.Item
import LCS.Util
import LCS.FirstOrder.Syntax
import Attach
import LCS.FirstOrder.Syntax.FreeGeneration.Terms.ProofsStamp

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

namespace TermFormationFn

/-- Definition 5.2.2 (companion): C_f prepends the function symbol f to
its argument strings concatenated in argument order. The strings may be arbitrary. -/
@[blueprint "chap5__definition_5_2_2"]
def c_f {L : Language} (f : L.funSymbols)
    (args : Fin (L.funArity f) → List (TermSymbol L)) : List (TermSymbol L) :=
  [TermSymbol.funSym f] ++ (List.ofFn args).flatten

end TermFormationFn

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
-- Theorem 5.2.2: Free generation of FORM_L
-- ===================================================================

-- retained: used by LCS.FirstOrder.Syntax.Parenthesized
/-- If a ++ r1 = b ++ r2 and a.length = b.length then a = b and r1 = r2. -/
theorem append_cancel_of_length_eq {α : Type} {a b rest1 rest2 : List α}
    (h : a ++ rest1 = b ++ rest2) (hlen : a.length = b.length) :
    a = b ∧ rest1 = rest2 := by
-- BEGIN PROOF
  have hab : a = b := by
    have h1 := congrArg (List.take a.length) h
    rw [List.take_append_of_le_length (by omega), List.take_length,
        List.take_append_of_le_length (by omega), show a.length = b.length from hlen,
        List.take_length] at h1; exact h1
  subst hab; exact ⟨rfl, List.append_cancel_left h⟩

-- retained: used by LCS.FirstOrder.Syntax.Parenthesized
/-- Prefix-freeness of terms lifted to an append-cancel principle:
if toSymbolList t1 ++ r1 = toSymbolList t2 ++ r2 then the two
toSymbolLists are equal and the remainders are equal. -/
theorem termSymList_append_cancel {L : Language}
    (t1 t2 : Term L) (rest1 rest2 : List (TermSymbol L))
    (h : Term.toSymbolList t1 ++ rest1 = Term.toSymbolList t2 ++ rest2) :
    Term.toSymbolList t1 = Term.toSymbolList t2 ∧ rest1 = rest2 := by
-- BEGIN PROOF
  by_cases hlen : (Term.toSymbolList t1).length < (Term.toSymbolList t2).length
  · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h (by omega)
    have hmid_ne : mid ≠ [] := by
      intro heq; subst heq; simp at hmid_eq
      have := congrArg List.length hmid_eq; omega
    exact absurd ⟨t1, rfl⟩ (term_prefix_free t2 _ mid hmid_eq hmid_ne)
  · by_cases hlen2 : (Term.toSymbolList t2).length < (Term.toSymbolList t1).length
    · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h.symm (by omega)
      have hmid_ne : mid ≠ [] := by
        intro heq; subst heq; simp at hmid_eq
        have := congrArg List.length hmid_eq; omega
      exact absurd ⟨t2, rfl⟩ (term_prefix_free t1 _ mid hmid_eq hmid_ne)
    · exact append_cancel_of_length_eq h (by omega)

-- retained: used by LCS.FirstOrder.Syntax.Algebra, LCS.FirstOrder.Syntax.Parenthesized
/-- Theorem 5.2.1 (companion): The symbol-list representation of terms is injective. -/
theorem term_toSymbolList_injective {L : Language} (t1 t2 : Term L)
    (h : Term.toSymbolList t1 = Term.toSymbolList t2) : t1 = t2 := by
-- BEGIN PROOF
  induction t1 generalizing t2 with
  | var n =>
    cases t2 with
    | var m => simp [Term.toSymbolList] at h; subst h; rfl
    | const c => simp [Term.toSymbolList] at h
    | func f ts => simp [Term.toSymbolList, TermFormationFn.c_f] at h
  | const c =>
    cases t2 with
    | var m => simp [Term.toSymbolList] at h
    | const d => simp [Term.toSymbolList] at h; subst h; rfl
    | func f ts => simp [Term.toSymbolList, TermFormationFn.c_f] at h
  | func f ts ih =>
    cases t2 with
    | var m => simp [Term.toSymbolList, TermFormationFn.c_f] at h
    | const c => simp [Term.toSymbolList, TermFormationFn.c_f] at h
    | func g us =>
      simp only [Term.toSymbolList_func, List.singleton_append, List.cons_eq_cons] at h
      obtain ⟨hfg, hrest⟩ := h; cases hfg; congr 1
      have : ∀ (n : Nat) (ts' us' : Fin n → Term L),
          (∀ i, ∀ t2, Term.toSymbolList (ts' i) = Term.toSymbolList t2 → ts' i = t2) →
          (List.ofFn (fun i => Term.toSymbolList (ts' i))).flatten =
          (List.ofFn (fun i => Term.toSymbolList (us' i))).flatten →
          ts' = us' := by
        intro n; induction n with
        | zero => intro ts' us' _ _; funext i; exact i.elim0
        | succ m ihm =>
          intro ts' us' ih' hfl
          rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons] at hfl
          have hcan := termSymList_append_cancel (ts' 0) (us' 0) _ _ hfl
          funext i; match i with
          | ⟨0, _⟩ => exact ih' 0 _ hcan.1
          | ⟨k + 1, hk⟩ =>
            have := ihm (fun j => ts' j.succ) (fun j => us' j.succ)
              (fun j t2' ht2' => ih' j.succ t2' ht2') hcan.2
            exact congrFun this ⟨k, by omega⟩
      exact this _ ts us ih hrest

/-- Theorem 5.2.1: On tuples of term strings, each formation function C_f
is injective, and distinct function symbols give disjoint ranges. No value
of C_f is a one-letter variable or constant string. Term strings are the
range of `Term.toSymbolList`. -/
@[blueprint "chap5__theorem_5_2_1" (main := true)]
theorem term_free_generation (L : Language) :
    (∀ (f : L.funSymbols) (ss us : Fin (L.funArity f) → List (TermSymbol L)),
      (∀ i, ∃ t : Term L, Term.toSymbolList t = ss i) →
      (∀ i, ∃ t : Term L, Term.toSymbolList t = us i) →
      TermFormationFn.c_f f ss = TermFormationFn.c_f f us → ss = us) ∧
    (∀ (f g : L.funSymbols), f ≠ g →
      ∀ (ss : Fin (L.funArity f) → List (TermSymbol L))
        (us : Fin (L.funArity g) → List (TermSymbol L)),
      (∀ i, ∃ t : Term L, Term.toSymbolList t = ss i) →
      (∀ i, ∃ t : Term L, Term.toSymbolList t = us i) →
      TermFormationFn.c_f f ss ≠ TermFormationFn.c_f g us) ∧
    (∀ (f : L.funSymbols) (ss : Fin (L.funArity f) → List (TermSymbol L)),
      (∀ n : Nat, TermFormationFn.c_f f ss ≠ [TermSymbol.varSym n]) ∧
      (∀ c : L.constSymbols, TermFormationFn.c_f f ss ≠ [TermSymbol.constSym c])) 

end LCS.FirstOrder.Syntax.FreeGeneration
end
