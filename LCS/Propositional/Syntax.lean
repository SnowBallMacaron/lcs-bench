import LCS.Item
import LCS.Util
import Attach
import LCS.Propositional.Syntax.ProofsStamp

/-! # Propositional Logic Syntax (Section 3.2)
    Source: Logic for Computer Science, Gallier 2015

    Defines the syntax of propositional logic: the propositional alphabet
    (Definition 3.2.1), the set PROP of propositional formulae (Definition 3.2.2),
    and the multi-layer bridge from alphabet to strings to AST.
-/

namespace LCS.Propositional.Syntax

-- ========= Definition 3.2.1: The Propositional Alphabet =========

/-- Definition 3.2.1: The alphabet for propositional formulae.
    Consists of (1) a countable set PS of proposition symbols P0, P1, P2, ...;
    (2) logical connectives: and, or, implication, not, equivalence, and falsum;
    (3) auxiliary symbols: left and right parentheses. -/
@[blueprint "chap3__definition_3_2_1" (main := true)]
inductive PropAlphabet where
  | propSym : Nat → PropAlphabet
  | connAnd : PropAlphabet
  | connOr : PropAlphabet
  | connImpl : PropAlphabet
  | connNot : PropAlphabet
  | connEquiv : PropAlphabet
  | falsum : PropAlphabet
  | lParen : PropAlphabet
  | rParen : PropAlphabet
  deriving DecidableEq, Repr

/-- A string over the propositional alphabet (Definition 3.2.1). -/
@[blueprint "chap3__definition_3_2_1" (main := true)]
abbrev PropString := List PropAlphabet

-- ========= Definition 3.2.2: Propositional Formulae (PROP) =========

/-- Syntax trees for the string grammar of Definition 3.2.2.
    Their image under `toStr` is PROP; `PropString.IsFormula` and its closure
    and minimality theorems express the textbook's set of strings. -/
@[blueprint "chap3__definition_3_2_2"]
inductive PropFormula where
  | var : Nat → PropFormula
  | fls : PropFormula
  | neg : PropFormula → PropFormula
  | conj : PropFormula → PropFormula → PropFormula
  | disj : PropFormula → PropFormula → PropFormula
  | impl : PropFormula → PropFormula → PropFormula
  | equiv_ : PropFormula → PropFormula → PropFormula
  deriving DecidableEq, Repr

-- ========= Definition 3.4.a: Normalized Propositional Formulae =========

/-- Definition 3.4.a: (Normalized propositional formulae) The subset of
    PROP using only the connectives {∧, ∨, ⊃, ¬}. Formally introduced
    in §3.4.2 after the standing assumption "In the rest of this section,
    it will be assumed that the set of connectives used is {∧, ∨, ⊃, ¬}".
    The concrete formula in Example 3.4.1 also belongs to this fragment. -/
@[blueprint "chap3__definition_3_4_a" (main := true)]
inductive PropFormulaNormalized where
  | var : Nat → PropFormulaNormalized
  | neg : PropFormulaNormalized → PropFormulaNormalized
  | conj : PropFormulaNormalized → PropFormulaNormalized → PropFormulaNormalized
  | disj : PropFormulaNormalized → PropFormulaNormalized → PropFormulaNormalized
  | impl : PropFormulaNormalized → PropFormulaNormalized → PropFormulaNormalized
  deriving DecidableEq, Repr

-- ========= Definition 3.2.2: Formation Functions (companion defs) =========

namespace FormationFn

/-- C_neg(A) = ¬A: prepend the negation connective to a string. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def c_neg (A : PropString) : PropString :=
  [.connNot] ++ A

/-- C_and(A,B) = (A ∧ B): wrap two strings in a conjunction. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def c_conj (A B : PropString) : PropString :=
  [.lParen] ++ A ++ [.connAnd] ++ B ++ [.rParen]

/-- C_or(A,B) = (A ∨ B): wrap two strings in a disjunction. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def c_disj (A B : PropString) : PropString :=
  [.lParen] ++ A ++ [.connOr] ++ B ++ [.rParen]

/-- C_impl(A,B) = (A ⊃ B): wrap two strings in an implication. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def c_impl (A B : PropString) : PropString :=
  [.lParen] ++ A ++ [.connImpl] ++ B ++ [.rParen]

/-- C_equiv(A,B) = (A ≡ B): wrap two strings in an equivalence. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def c_equiv (A B : PropString) : PropString :=
  [.lParen] ++ A ++ [.connEquiv] ++ B ++ [.rParen]

end FormationFn

namespace PropFormula

/-- Convert a PropFormula AST to its string representation over PropAlphabet.
    This bridges the AST layer back to the string layer, using the formation
    functions from Definition 3.2.2. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def toStr : PropFormula → PropString
  | .var n => [.propSym n]
  | .fls => [.falsum]
  | .neg A => FormationFn.c_neg A.toStr
  | .conj A B => FormationFn.c_conj A.toStr B.toStr
  | .disj A B => FormationFn.c_disj A.toStr B.toStr
  | .impl A B => FormationFn.c_impl A.toStr B.toStr
  | .equiv_ A B => FormationFn.c_equiv A.toStr B.toStr

end PropFormula

/-- The strings in PROP: precisely those formed from proposition symbols and
    falsum by the five formation functions, as encoded by `toStr`. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
def PropString.IsFormula (s : PropString) : Prop := ∃ A : PropFormula, A.toStr = s

/-- Definition 3.2.2: PROP contains the generators and is closed under all
    five string formation functions. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
theorem PropString.isFormula_closed :
    (∀ n, IsFormula [.propSym n]) ∧ IsFormula [.falsum] ∧
    (∀ A, IsFormula A → IsFormula (FormationFn.c_neg A)) ∧
    (∀ A B, IsFormula A → IsFormula B → IsFormula (FormationFn.c_conj A B)) ∧
    (∀ A B, IsFormula A → IsFormula B → IsFormula (FormationFn.c_disj A B)) ∧
    (∀ A B, IsFormula A → IsFormula B → IsFormula (FormationFn.c_impl A B)) ∧
    (∀ A B, IsFormula A → IsFormula B → IsFormula (FormationFn.c_equiv A B))

/-- Definition 3.2.2: PROP is the least such set of strings. -/
@[blueprint "chap3__definition_3_2_2" (main := true)]
theorem PropString.isFormula_least (S : Set PropString)
    (hvar : ∀ n, S [.propSym n]) (hfls : S [.falsum])
    (hneg : ∀ A, S A → S (FormationFn.c_neg A))
    (hconj : ∀ A B, S A → S B → S (FormationFn.c_conj A B))
    (hdisj : ∀ A B, S A → S B → S (FormationFn.c_disj A B))
    (himpl : ∀ A B, S A → S B → S (FormationFn.c_impl A B))
    (hequiv : ∀ A B, S A → S B → S (FormationFn.c_equiv A B)) :
    ∀ s, IsFormula s → S s

-- ========= Lemma 3.2.1: Helper definitions (parenthesis counting) =========

namespace PropString

/-- Lemma 3.2.1 (required helper): Count the number of left parentheses
    in a PropString. -/
@[blueprint "chap3__lemma_3_2_1"]
def leftParenCount (s : PropString) : Nat :=
  s.foldl (fun acc c => match c with | .lParen => acc + 1 | _ => acc) 0

/-- Lemma 3.2.1 (required helper): Count the number of right parentheses
    in a PropString. -/
@[blueprint "chap3__lemma_3_2_1"]
def rightParenCount (s : PropString) : Nat :=
  s.foldl (fun acc c => match c with | .rParen => acc + 1 | _ => acc) 0

end PropString

-- ========= Example 3.2.1: Concrete propositions =========

/-- Example 3.2.1: The proposition symbol P1. -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exP1 : PropFormula := PropFormula.var 1

/-- Example 3.2.1: The proposition symbol P2. -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exP2 : PropFormula := PropFormula.var 2

/-- Example 3.2.1: The disjunction (P1 ∨ P2). -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exP1orP2 : PropFormula :=
  PropFormula.disj (PropFormula.var 1) (PropFormula.var 2)

/-- Example 3.2.1: The equivalence ((P1 ⊃ P2) ≡ (¬P1 ∨ P2)). -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exImplEquiv : PropFormula :=
  PropFormula.equiv_
    (PropFormula.impl (.var 1) (.var 2))
    (PropFormula.disj (PropFormula.neg (.var 1)) (.var 2))

/-- Example 3.2.1: The equivalence (¬P1 ≡ (P1 ⊃ ⊥)). -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exNegEquivImplFls : PropFormula :=
  PropFormula.equiv_
    (PropFormula.neg (.var 1))
    (PropFormula.impl (.var 1) .fls)

/-- Example 3.2.1: Modus tollens (((P1 ⊃ P2) ∧ ¬P2) ⊃ ¬P1). -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exModusTollens : PropFormula :=
  PropFormula.impl
    (PropFormula.conj
      (PropFormula.impl (.var 1) (.var 2))
      (PropFormula.neg (.var 2)))
    (PropFormula.neg (.var 1))

/-- Example 3.2.1: Excluded middle (P1 ∨ ¬P1). -/
@[blueprint "chap3__example_3_2_1" (main := true)]
def exExcludedMiddle : PropFormula :=
  PropFormula.disj (PropFormula.var 1) (PropFormula.neg (PropFormula.var 1))

-- ========= Example 3.2.2: The symbols function =========

namespace PropFormula

/-- Example 3.2.2: The function symbols : PROP → 2^PS, returning the set of
    proposition symbol indices occurring in a formula (recursive definition). -/
@[blueprint "chap3__example_3_2_2" (main := true)]
def symbols : PropFormula → Set Nat
  | .var n => fun m => m = n
  | .fls => fun _ => False
  | .neg A => A.symbols
  | .conj A B => A.symbols ∪ B.symbols
  | .disj A B => A.symbols ∪ B.symbols
  | .impl A B => A.symbols ∪ B.symbols
  | .equiv_ A B => A.symbols ∪ B.symbols

end PropFormula

/-- Example 3.2.2 (companion): symbols(((P1 ⊃ P2) ∨ ¬P3) ∧ P1) = {P1, P2, P3}.
    Demonstrates the symbols function on a concrete formula. -/
@[blueprint "chap3__example_3_2_2"]
def exSymbolsComputation : PropFormula :=
  PropFormula.conj
    (PropFormula.disj
      (PropFormula.impl (.var 1) (.var 2))
      (PropFormula.neg (.var 3)))
    (.var 1)

/-- Example 3.2.2: The exact set of proposition indices in the displayed formula. -/
@[blueprint "chap3__example_3_2_2" (main := true)]
theorem exSymbolsComputation_eq :
    exSymbolsComputation.symbols = (fun n => n = 1 ∨ n = 2 ∨ n = 3)

-- ========= Example 3.2.3: Precedence and associativity =========

section Abbreviations

-- Object-language notation, local to these examples: ⋏, ⋎, ⟹ denote ∧, ∨, ⊃.
-- Larger priorities bind tighter; infixl implements the textbook’s left associativity.
local prefix:80 "¬" => PropFormula.neg
local infixl:70 " ⋏ " => PropFormula.conj
local infixl:65 " ⋎ " => PropFormula.disj
local infixl:60 " ⟹ " => PropFormula.impl
local infixl:60 " ≡ " => PropFormula.equiv_

/-- Example 3.2.3: ∧ binds more tightly than ⊃, for arbitrary propositions. -/
@[blueprint "chap3__example_3_2_3" (main := true)]
theorem exPrecedence1 (A B C : PropFormula) :
    (A ⋏ B ⟹ C) = PropFormula.impl (PropFormula.conj A B) C

/-- Example 3.2.3: ∧ binds more tightly than ∨, for arbitrary propositions. -/
@[blueprint "chap3__example_3_2_3" (main := true)]
theorem exPrecedence2 (A B C : PropFormula) :
    (A ⋎ B ⋏ C) = PropFormula.disj A (PropFormula.conj B C)

/-- Example 3.2.3: ∨ associates to the left, for arbitrary propositions. -/
@[blueprint "chap3__example_3_2_3" (main := true)]
theorem exLeftAssoc (A B C : PropFormula) :
    (A ⋎ B ⋎ C) = PropFormula.disj (PropFormula.disj A B) C

end Abbreviations

-- ========= Lemma 3.2.1: Parenthesis Balance and Prefix Properties =========

-- Helper: generalized foldl accumulator shift for left paren counting
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem leftParen_foldl_acc (s : PropString) (acc : Nat) :
    List.foldl (fun a c => match c with | .lParen => a + 1 | _ => a) acc s =
    acc + s.foldl (fun a c => match c with | .lParen => a + 1 | _ => a) 0 := by
-- BEGIN PROOF
  induction s generalizing acc with
  | nil => simp [List.foldl]
  | cons h t ih =>
    cases h with
    | lParen =>
      show List.foldl _ (acc + 1) t = acc + List.foldl _ (0 + 1) t
      rw [ih, ih (acc := 1)]; omega
    | propSym n => exact ih acc
    | connAnd => exact ih acc
    | connOr => exact ih acc
    | connImpl => exact ih acc
    | connNot => exact ih acc
    | connEquiv => exact ih acc
    | falsum => exact ih acc
    | rParen => exact ih acc

-- Helper: generalized foldl accumulator shift for right paren counting
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem rightParen_foldl_acc (s : PropString) (acc : Nat) :
    List.foldl (fun a c => match c with | .rParen => a + 1 | _ => a) acc s =
    acc + s.foldl (fun a c => match c with | .rParen => a + 1 | _ => a) 0 := by
-- BEGIN PROOF
  induction s generalizing acc with
  | nil => simp [List.foldl]
  | cons h t ih =>
    cases h with
    | rParen =>
      show List.foldl _ (acc + 1) t = acc + List.foldl _ (0 + 1) t
      rw [ih, ih (acc := 1)]; omega
    | propSym n => exact ih acc
    | connAnd => exact ih acc
    | connOr => exact ih acc
    | connImpl => exact ih acc
    | connNot => exact ih acc
    | connEquiv => exact ih acc
    | falsum => exact ih acc
    | lParen => exact ih acc

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem leftParenCount_append (s1 s2 : PropString) :
    PropString.leftParenCount (s1 ++ s2) =
    PropString.leftParenCount s1 + PropString.leftParenCount s2 := by
-- BEGIN PROOF
  simp only [PropString.leftParenCount, List.foldl_append]
  rw [leftParen_foldl_acc]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem rightParenCount_append (s1 s2 : PropString) :
    PropString.rightParenCount (s1 ++ s2) =
    PropString.rightParenCount s1 + PropString.rightParenCount s2 := by
-- BEGIN PROOF
  simp only [PropString.rightParenCount, List.foldl_append]
  rw [rightParen_foldl_acc]

-- Helper: every PropFormula.toStr contains a non-connNot character


-- Helper: toStr is never empty


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every PropFormula has equal left and right parenthesis counts in its
    string representation. -/
theorem propFormula_balanced_parens (A : PropFormula) :
    A.toStr.leftParenCount = A.toStr.rightParenCount :=
-- BEGIN PROOF
by
  induction A with
  | var n =>
    simp [PropFormula.toStr, PropString.leftParenCount, PropString.rightParenCount, List.foldl]
  | fls =>
    decide
  | neg A ih =>
    show PropString.leftParenCount ([.connNot] ++ A.toStr) =
         PropString.rightParenCount ([.connNot] ++ A.toStr)
    rw [leftParenCount_append, rightParenCount_append]
    simp [PropString.leftParenCount, PropString.rightParenCount, List.foldl]
    exact ih
  | conj A B ihA ihB =>
    show PropString.leftParenCount ([.lParen] ++ A.toStr ++ [.connAnd] ++ B.toStr ++ [.rParen]) =
         PropString.rightParenCount ([.lParen] ++ A.toStr ++ [.connAnd] ++ B.toStr ++ [.rParen])
    simp only [List.append_assoc]
    rw [leftParenCount_append, leftParenCount_append, leftParenCount_append, leftParenCount_append,
        rightParenCount_append, rightParenCount_append, rightParenCount_append, rightParenCount_append]
    have : PropString.leftParenCount [.lParen] = 1 := by decide
    have : PropString.rightParenCount [.lParen] = 0 := by decide
    have : PropString.leftParenCount [.connAnd] = 0 := by decide
    have : PropString.rightParenCount [.connAnd] = 0 := by decide
    have : PropString.leftParenCount [.rParen] = 0 := by decide
    have : PropString.rightParenCount [.rParen] = 1 := by decide
    omega
  | disj A B ihA ihB =>
    show PropString.leftParenCount ([.lParen] ++ A.toStr ++ [.connOr] ++ B.toStr ++ [.rParen]) =
         PropString.rightParenCount ([.lParen] ++ A.toStr ++ [.connOr] ++ B.toStr ++ [.rParen])
    simp only [List.append_assoc]
    rw [leftParenCount_append, leftParenCount_append, leftParenCount_append, leftParenCount_append,
        rightParenCount_append, rightParenCount_append, rightParenCount_append, rightParenCount_append]
    have : PropString.leftParenCount [.lParen] = 1 := by decide
    have : PropString.rightParenCount [.lParen] = 0 := by decide
    have : PropString.leftParenCount [.connOr] = 0 := by decide
    have : PropString.rightParenCount [.connOr] = 0 := by decide
    have : PropString.leftParenCount [.rParen] = 0 := by decide
    have : PropString.rightParenCount [.rParen] = 1 := by decide
    omega
  | impl A B ihA ihB =>
    show PropString.leftParenCount ([.lParen] ++ A.toStr ++ [.connImpl] ++ B.toStr ++ [.rParen]) =
         PropString.rightParenCount ([.lParen] ++ A.toStr ++ [.connImpl] ++ B.toStr ++ [.rParen])
    simp only [List.append_assoc]
    rw [leftParenCount_append, leftParenCount_append, leftParenCount_append, leftParenCount_append,
        rightParenCount_append, rightParenCount_append, rightParenCount_append, rightParenCount_append]
    have : PropString.leftParenCount [.lParen] = 1 := by decide
    have : PropString.rightParenCount [.lParen] = 0 := by decide
    have : PropString.leftParenCount [.connImpl] = 0 := by decide
    have : PropString.rightParenCount [.connImpl] = 0 := by decide
    have : PropString.leftParenCount [.rParen] = 0 := by decide
    have : PropString.rightParenCount [.rParen] = 1 := by decide
    omega
  | equiv_ A B ihA ihB =>
    show PropString.leftParenCount ([.lParen] ++ A.toStr ++ [.connEquiv] ++ B.toStr ++ [.rParen]) =
         PropString.rightParenCount ([.lParen] ++ A.toStr ++ [.connEquiv] ++ B.toStr ++ [.rParen])
    simp only [List.append_assoc]
    rw [leftParenCount_append, leftParenCount_append, leftParenCount_append, leftParenCount_append,
        rightParenCount_append, rightParenCount_append, rightParenCount_append, rightParenCount_append]
    have : PropString.leftParenCount [.lParen] = 1 := by decide
    have : PropString.rightParenCount [.lParen] = 0 := by decide
    have : PropString.leftParenCount [.connEquiv] = 0 := by decide
    have : PropString.rightParenCount [.connEquiv] = 0 := by decide
    have : PropString.leftParenCount [.rParen] = 0 := by decide
    have : PropString.rightParenCount [.rParen] = 1 := by decide
    omega

-- Helper: all-connNot strings have leftPC = rightPC = 0




-- Helper: if a ++ b = c ++ d and a.length ≤ c.length, then a <+: c
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem prefix_of_append_eq {a b c d : PropString}
    (h : a ++ b = c ++ d) (hlen : a.length ≤ c.length) : a <+: c := by
-- BEGIN PROOF
  have htak : List.take a.length c = a := by
    have h1 : List.take a.length (a ++ b) = List.take a.length (c ++ d) := by rw [h]
    simp at h1; rw [List.take_append] at h1
    simp [Nat.sub_eq_zero_of_le hlen] at h1; exact h1.symm
  exact htak ▸ List.take_prefix a.length c

-- Helper: if a ++ b = c ++ d and c.length ≤ a.length, then a = c ++ rest
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem split_past_prefix {a b c d : PropString}
    (h : a ++ b = c ++ d) (hlen : c.length ≤ a.length) :
    ∃ rest, a = c ++ rest ∧ rest ++ b = d := by
-- BEGIN PROOF
  have htak : List.take c.length a = c := by
    have : List.take c.length (a ++ b) = List.take c.length (c ++ d) := by rw [h]
    simp at this; rw [List.take_append] at this
    simp [Nat.sub_eq_zero_of_le hlen] at this; exact this
  have hsplit : a = List.take c.length a ++ List.drop c.length a := (List.take_append_drop c.length a).symm
  rw [htak] at hsplit
  refine ⟨a.drop c.length, hsplit, ?_⟩
  have : (c ++ a.drop c.length) ++ b = c ++ d := by rw [← hsplit]; exact h
  rw [List.append_assoc] at this; exact List.append_cancel_left this

/-- Lemma 3.2.1: Three-part lemma about structural properties of
    propositions: (i) parenthesis balance, (ii) proper prefix structure,
    (iii) no proper prefix is a proposition. -/
@[blueprint "chap3__lemma_3_2_1" (main := true)]
theorem propFormula_parenthesis_balance :
    -- (i) Balanced parentheses
    (∀ (A : PropFormula), A.toStr.leftParenCount = A.toStr.rightParenCount) ∧
    -- (ii) Proper prefix structure
    (∀ (A : PropFormula) (p : PropString),
      p <+: A.toStr → p ≠ A.toStr →
      p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
      p.leftParenCount > p.rightParenCount) ∧
    -- (iii) No proper prefix is a proposition
    (∀ (B : PropFormula) (p : PropString),
      p <+: B.toStr → p ≠ B.toStr →
      ¬(∃ C : PropFormula, C.toStr = p))

-- ========= Theorem 3.2.1: Free Generation of PROP =========



/-- Unique readability: the string representation determines the complete syntax tree. -/
@[blueprint "chap3__theorem_3_2_1"]
theorem PropFormula.toStr_injective {A B : PropFormula}
    (h : A.toStr = B.toStr) : A = B

/-- Theorem 3.2.1: On PROP, the five string formation functions are injective,
    have pairwise disjoint ranges, and never produce a proposition symbol or falsum. -/
@[blueprint "chap3__theorem_3_2_1" (main := true)]
theorem propFormula_free_generation :
    (∀ A B : PropString,
      A.IsFormula → B.IsFormula →
      FormationFn.c_neg A = FormationFn.c_neg B → A = B) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_conj A B = FormationFn.c_conj C D → A = C ∧ B = D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_disj A B = FormationFn.c_disj C D → A = C ∧ B = D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_impl A B = FormationFn.c_impl C D → A = C ∧ B = D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_equiv A B = FormationFn.c_equiv C D → A = C ∧ B = D) ∧
    (∀ A B C : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula →
      FormationFn.c_neg A ≠ FormationFn.c_conj B C) ∧
    (∀ A B C : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula →
      FormationFn.c_neg A ≠ FormationFn.c_disj B C) ∧
    (∀ A B C : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula →
      FormationFn.c_neg A ≠ FormationFn.c_impl B C) ∧
    (∀ A B C : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula →
      FormationFn.c_neg A ≠ FormationFn.c_equiv B C) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_conj A B ≠ FormationFn.c_disj C D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_conj A B ≠ FormationFn.c_impl C D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_conj A B ≠ FormationFn.c_equiv C D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_disj A B ≠ FormationFn.c_impl C D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_disj A B ≠ FormationFn.c_equiv C D) ∧
    (∀ A B C D : PropString,
      A.IsFormula → B.IsFormula → C.IsFormula → D.IsFormula →
      FormationFn.c_impl A B ≠ FormationFn.c_equiv C D) ∧
    (∀ A : PropString,
      A.IsFormula → (∀ n, FormationFn.c_neg A ≠ [.propSym n]) ∧
      FormationFn.c_neg A ≠ [.falsum]) ∧
    (∀ A B : PropString,
      A.IsFormula → B.IsFormula → (∀ n, FormationFn.c_conj A B ≠ [.propSym n]) ∧
      FormationFn.c_conj A B ≠ [.falsum]) ∧
    (∀ A B : PropString,
      A.IsFormula → B.IsFormula → (∀ n, FormationFn.c_disj A B ≠ [.propSym n]) ∧
      FormationFn.c_disj A B ≠ [.falsum]) ∧
    (∀ A B : PropString,
      A.IsFormula → B.IsFormula → (∀ n, FormationFn.c_impl A B ≠ [.propSym n]) ∧
      FormationFn.c_impl A B ≠ [.falsum]) ∧
    (∀ A B : PropString,
      A.IsFormula → B.IsFormula → (∀ n, FormationFn.c_equiv A B ≠ [.propSym n]) ∧
      FormationFn.c_equiv A B ≠ [.falsum])

/-- Example 3.2.1: `(())` cannot be formed by the proposition grammar. -/
@[blueprint "chap3__example_3_2_1" (main := true)]
theorem exEmptyParens_not_formula :
    ¬ PropString.IsFormula [.lParen, .lParen, .rParen, .rParen]

/-- Example 3.2.1: `(P1 ∨ P2) ∧` has a proper prefix that is already a proposition. -/
@[blueprint "chap3__example_3_2_1" (main := true)]
theorem exTrailingConjunction_not_formula :
    ¬ PropString.IsFormula [.lParen, .propSym 1, .connOr, .propSym 2, .rParen, .connAnd]

end LCS.Propositional.Syntax
