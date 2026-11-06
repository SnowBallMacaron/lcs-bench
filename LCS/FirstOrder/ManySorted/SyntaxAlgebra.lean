import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.Syntax.RankedAlphabet
import LCS.FirstOrder.Syntax.Algebra
import Attach
import LCS.FirstOrder.ManySorted.SyntaxAlgebra.ProofsStamp

/-! # Many-sorted source alphabets

The ranked variable/nonlogical alphabet and source tokens of Definition 10.2.1.
Data sorts embed as `some s`, and `none` is the distinguished bool sort.
The constructions apply to general signatures, including naming expansions;
a countable source language uses its `MSFirstOrderLanguage.toMSLanguage`.
-/

namespace LCS.FirstOrder.ManySorted.SyntaxAlgebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 10.2.1 (companion): The sort set S ∪ {bool}, with a distinct
Boolean sort `none` and data sorts `some s`. -/
@[blueprint "chap10__definition_10_2_1"]
abbrev MSSyntaxSort (L : MSLanguage) : Type := Option L.SortType

/-- Definition 10.2.1 (companion): The disjoint union of the sorted variable
family V, the sorted constant family CS, function symbols FS and predicate
symbols PS. Constructors embed raw symbols with their family and sort tags,
so even identical raw carriers have disjoint syntactic identities. -/
@[blueprint "chap10__definition_10_2_1"]
inductive MSNonlogicalSymbol (L : MSLanguage) : Type where
  | var : (s : L.SortType) → Nat → MSNonlogicalSymbol L
  | const : (s : L.SortType) → L.constSymbols s → MSNonlogicalSymbol L
  | func : L.funSymbols → MSNonlogicalSymbol L
  | pred : L.predSymbols → MSNonlogicalSymbol L

/-- Definition 10.2.1 (companion): Variables and constants have rank (ε,s).
Function ranks retain their ordered nonempty input word and data output sort.
Predicate inputs are ordered data-sort words, possibly empty, with bool output. -/
@[blueprint "chap10__definition_10_2_1"]
def msNonlogicalRank {L : MSLanguage} :
    MSNonlogicalSymbol L → List (MSSyntaxSort L) × MSSyntaxSort L
  | .var s _ | .const s _ => ([], some s)
  | .func f => ((L.funRank f).1.map some, some (L.funRank f).2)
  | .pred P => ((L.predArity P).map some, none)

/-- Definition 10.2.1 (companion): Source tokens for the variable/nonlogical
union, all six logical connectives, sort-indexed quantifiers and equality,
and auxiliary parentheses.
Quantifier tokens carry a sort; a bound-variable index belongs to a quantifier
application. Equality tokens are present when the language has equality. -/
@[blueprint "chap10__definition_10_2_1"]
inductive MSSourceToken (L : MSLanguage) : Type where
  | nonlogical : MSNonlogicalSymbol L → MSSourceToken L
  | conj : MSSourceToken L
  | disj : MSSourceToken L
  | impl : MSSourceToken L
  | equiv_ : MSSourceToken L
  | neg : MSSourceToken L
  | falsum : MSSourceToken L
  | all : L.SortType → MSSourceToken L
  | ex : L.SortType → MSSourceToken L
  | eq_ : L.hasEquality = true → L.SortType → MSSourceToken L
  | lparen : MSSourceToken L
  | rparen : MSSourceToken L

/-- Definition 10.2.1 (companion): Ranks of the represented source symbols.
Binary connectives have rank (bool.bool,bool), negation and quantifiers
have rank (bool,bool), bottom has rank (ε,bool), and equality at s has
rank (ss,bool).
Parentheses are auxiliary tokens, represented by an absent rank. -/
@[blueprint "chap10__definition_10_2_1"]
def msSourceTokenRank {L : MSLanguage} :
    MSSourceToken L → Option (List (MSSyntaxSort L) × MSSyntaxSort L)
  | .nonlogical a => some (msNonlogicalRank a)
  | .conj | .disj | .impl | .equiv_ => some ([none, none], none)
  | .neg | .all _ | .ex _ => some ([none], none)
  | .falsum => some ([], none)
  | .eq_ _ s => some ([some s, some s], none)
  | .lparen | .rparen => none

/-- Definition 10.2.1 (companion): All sorted variables embed in the
same source token alphabet, retaining their sort and Nat index. -/
@[blueprint "chap10__definition_10_2_1"]
def msVarToken {L : MSLanguage} (x : MSVar L) : MSSourceToken L :=
  .nonlogical (.var x.1 x.2)

/-- Definition 10.2.1 (companion): The entire sorted constant family
embeds in the source alphabet, with the fiber index retained. -/
@[blueprint "chap10__definition_10_2_1"]
def msConstToken {L : MSLanguage} (c : (s : L.SortType) × L.constSymbols s) :
    MSSourceToken L := .nonlogical (.const c.1 c.2)

/-- Definition 10.2.1 (companion): Function symbols embed in the source alphabet. -/
@[blueprint "chap10__definition_10_2_1"]
def msFunToken {L : MSLanguage} (f : L.funSymbols) : MSSourceToken L :=
  .nonlogical (.func f)

/-- Definition 10.2.1 (companion): Predicate symbols embed in the source alphabet. -/
@[blueprint "chap10__definition_10_2_1"]
def msPredToken {L : MSLanguage} (P : L.predSymbols) : MSSourceToken L :=
  .nonlogical (.pred P)

/-- Definition 10.2.1 (companion): The expanded constructor signature.
Variables are generators; constants, functions, predicates, all logical
connectives and equality are operations. A quantifier operation carries both
its sort and bound-variable index, unlike its source token. -/
@[blueprint "chap10__definition_10_2_1"]
inductive MSConstructorSymbol (L : MSLanguage) : Type where
  | const : (s : L.SortType) → L.constSymbols s → MSConstructorSymbol L
  | func : L.funSymbols → MSConstructorSymbol L
  | pred : L.predSymbols → MSConstructorSymbol L
  | conj | disj | impl | equiv_ | neg | falsum : MSConstructorSymbol L
  | eq_ : L.hasEquality = true → L.SortType → MSConstructorSymbol L
  | all : L.SortType → Nat → MSConstructorSymbol L
  | ex : L.SortType → Nat → MSConstructorSymbol L

/-- Definition 10.2.1 (companion): Total ranks of the expanded operations,
including unary bool-ranked quantifier operations for every sorted variable. -/
@[blueprint "chap10__definition_10_2_1"]
def msConstructorRank {L : MSLanguage} :
    MSConstructorSymbol L → List (MSSyntaxSort L) × MSSyntaxSort L
  | .const s _ => ([], some s)
  | .func f => ((L.funRank f).1.map some, some (L.funRank f).2)
  | .pred P => ((L.predArity P).map some, none)
  | .conj | .disj | .impl | .equiv_ => ([none, none], none)
  | .neg | .all _ _ | .ex _ _ => ([none], none)
  | .falsum => ([], none)
  | .eq_ _ s => ([some s, some s], none)

/-- Definition 10.2.1 (companion): The full expanded ranked signature used
by the term/formula algebra, with source variables as generators. -/
@[blueprint "chap10__definition_10_2_1"]
def msConstructorAlphabet (L : MSLanguage) : MSRankedAlphabet where
  SortType := MSSyntaxSort L
  symbols := MSConstructorSymbol L
  rank := msConstructorRank

open LCS.FirstOrder.Basic (FirstOrderLanguage)
open LCS.FirstOrder.Syntax.Algebra (SyntaxOperation FirstOrderSort)

/-- Definition 10.2.2 (companion): Finite strings over the enlarged source
alphabet, including logical/equality/quantifier tokens and parentheses. -/
@[blueprint "chap10__definition_10_2_2"]
abbrev MSTokenString (L : MSLanguage) : Type := List (MSSourceToken L)

/-- Definition 10.2.2 (companion): The result sort of the first token of
a string, when that token has a rank. Empty strings and strings starting
with auxiliary punctuation have no head sort. -/
@[blueprint "chap10__definition_10_2_2"]
def msStringHeadSort {L : MSLanguage} : MSTokenString L → Option (MSSyntaxSort L)
  | [] => none
  | a :: _ => (msSourceTokenRank a).map Prod.snd

/-- Definition 10.2.2 (companion): The corrected ambient string family.
At data sort s, the first token has result sort s. At bool, every nonempty
string is admitted, including strings beginning with a parenthesis. This is
the closure-repair reading of the printed construction. No term/formula
formation condition is imposed; the generated subalgebra is a separate object. -/
@[blueprint "chap10__definition_10_2_2"]
def msAmbientStringAt {L : MSLanguage} : MSSyntaxSort L → MSTokenString L → Prop
  | some s, w => msStringHeadSort w = some (some s)
  | none, w => w ≠ []

/-- Definition 10.2.2 (companion): The ambient carrier at a data or Boolean
sort, as an actual subtype of arbitrary token strings. The Boolean carrier
may overlap a data carrier, as permitted for a sorted algebra. -/
@[blueprint "chap10__definition_10_2_2"]
def MSAmbientString (L : MSLanguage) (s : MSSyntaxSort L) : Type :=
  {w : MSTokenString L // msAmbientStringAt s w}

/-- Definition 10.2.2 (companion): Any tail is allowed after a ranked head
of the required sort; ambient strings need not satisfy formation rules. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientString_cons {L : MSLanguage} (a : MSSourceToken L)
    (u : List (MSSyntaxSort L)) (s : MSSyntaxSort L)
    (hrank : msSourceTokenRank a = some (u, s)) (tail : MSTokenString L) :
    msAmbientStringAt s (a :: tail) 

/-- Definition 10.2.2 (companion): The ambient string of a sorted variable. -/
@[blueprint "chap10__definition_10_2_2"]
def msAmbientVariable (L : MSLanguage) (s : L.SortType) (i : Nat) :
    MSAmbientString L (some s) := ⟨[msVarToken (s, i)], rfl⟩

/-- Definition 10.2.2 (companion): The singleton bottom string in the
Boolean ambient carrier. -/
@[blueprint "chap10__definition_10_2_2"]
def msAmbientBottom (L : MSLanguage) : MSAmbientString L none :=
  ⟨[.falsum], by intro h; cases h⟩

/-- Definition 10.2.2 (companion): Each ambient carrier is nonempty,
using the variable x₀ at each data sort and bottom at bool. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientString_nonempty_carrier (L : MSLanguage) (s : MSSyntaxSort L) :
    Nonempty (MSAmbientString L s) 

/-- Definition 10.2.2 (companion): C_f sends arbitrary ambient strings
of the ordered input sorts of f to the string f t₁ … tₙ of its output sort.
Concatenation follows the input positions, with no parsing requirement. -/
@[blueprint "chap10__definition_10_2_2"]
def msFunctionString {L : MSLanguage} (f : L.funSymbols)
    (args : (i : Fin (L.funRank f).1.length) →
      MSAmbientString L (some ((L.funRank f).1.get i))) :
    MSAmbientString L (some (L.funRank f).2) :=
  ⟨msFunToken f :: (List.ofFn (fun i => (args i).val)).flatten,
    msAmbientString_cons _ _ _ rfl _⟩

/-- Definition 10.2.2 (companion): C_P sends arbitrary ambient strings
of the ordered input sorts of P to P t₁ … tₙ in the Boolean carrier.
The input word may be empty, giving the singleton propositional-letter string. -/
@[blueprint "chap10__definition_10_2_2"]
def msPredicateString {L : MSLanguage} (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) →
      MSAmbientString L (some ((L.predArity P).get i))) :
    MSAmbientString L none :=
  ⟨msPredToken P :: (List.ofFn (fun i => (args i).val)).flatten,
    msAmbientString_cons _ _ _ rfl _⟩

/-- Definition 10.2.2 (companion): Same-sort equality string formation,
C_eq^s(t,u) = eq_s t u, on the entire product of the sort-s ambient carrier.
The output is Boolean, and the source equality flag is retained. -/
@[blueprint "chap10__definition_10_2_2"]
def msEqualityString {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (t u : MSAmbientString L (some s)) :
    MSAmbientString L none :=
  ⟨MSSourceToken.eq_ hL s :: (t.val ++ u.val), msAmbientString_cons _ _ _ rfl _⟩

/-- Definition 10.2.2 (companion): The constant nullary is the singleton constant token in its data sort. -/
@[blueprint "chap10__definition_10_2_2"]
def msConstantString {L : MSLanguage} (s : L.SortType) (c : L.constSymbols s) :
    MSAmbientString L (some s) := ⟨[msConstToken ⟨s, c⟩], rfl⟩

/-- Definition 10.2.2 (companion): The Boolean string operation C_∧(A,B) = (A ∧ B). -/
@[blueprint "chap10__definition_10_2_2"]
def msConjString {L : MSLanguage} (A B : MSAmbientString L none) :
    MSAmbientString L none :=
  ⟨.lparen :: (A.val ++ [.conj] ++ B.val ++ [.rparen]), by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The Boolean string operation C_∨(A,B) = (A ∨ B). -/
@[blueprint "chap10__definition_10_2_2"]
def msDisjString {L : MSLanguage} (A B : MSAmbientString L none) :
    MSAmbientString L none :=
  ⟨.lparen :: (A.val ++ [.disj] ++ B.val ++ [.rparen]), by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The Boolean string operation C_⊃(A,B) = (A ⊃ B). -/
@[blueprint "chap10__definition_10_2_2"]
def msImplString {L : MSLanguage} (A B : MSAmbientString L none) :
    MSAmbientString L none :=
  ⟨.lparen :: (A.val ++ [.impl] ++ B.val ++ [.rparen]), by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The Boolean string operation C_≡(A,B) = (A ≡ B). -/
@[blueprint "chap10__definition_10_2_2"]
def msEquivString {L : MSLanguage} (A B : MSAmbientString L none) :
    MSAmbientString L none :=
  ⟨.lparen :: (A.val ++ [.equiv_] ++ B.val ++ [.rparen]), by intro h; cases h⟩

/-- Definition 10.2.2 (companion): Negation prefixes ¬ to an arbitrary Boolean ambient string. -/
@[blueprint "chap10__definition_10_2_2"]
def msNegString {L : MSLanguage} (A : MSAmbientString L none) :
    MSAmbientString L none := ⟨.neg :: A.val, by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The indexed unary operation ∀_s x_i A retains both the sort and variable index. -/
@[blueprint "chap10__definition_10_2_2"]
def msAllString {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSAmbientString L none) : MSAmbientString L none :=
  ⟨.all s :: msVarToken (s, i) :: A.val, by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The indexed unary operation ∃_s x_i A retains both the sort and variable index. -/
@[blueprint "chap10__definition_10_2_2"]
def msExString {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSAmbientString L none) : MSAmbientString L none :=
  ⟨.ex s :: msVarToken (s, i) :: A.val, by intro h; cases h⟩

/-- Definition 10.2.2 (companion): The full-signature ambient algebra on the corrected sorted string carriers.
Every symbol acts by its printed string operation; variables are generators.
All carriers are nonempty, and the dependent operation type enforces closure. -/
@[blueprint "chap10__definition_10_2_2"]
def msAmbientStringAlgebra (L : MSLanguage) :
    LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L) where
  carrier := MSAmbientString L
  carrierNonempty := msAmbientString_nonempty_carrier L
  operation := fun op => by
    cases op <;> dsimp only [MSRankedAlphabet.argSorts, MSRankedAlphabet.resultSort,
      msConstructorAlphabet, msConstructorRank]
    case const s c => exact fun _ => msConstantString s c
    case func f =>
      intro args
      apply msFunctionString f
      intro i
      simpa using args ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    case pred P =>
      intro args
      apply msPredicateString P
      intro i
      simpa using args ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    case conj => exact fun args => msConjString (args 0) (args 1)
    case disj => exact fun args => msDisjString (args 0) (args 1)
    case impl => exact fun args => msImplString (args 0) (args 1)
    case equiv_ => exact fun args => msEquivString (args 0) (args 1)
    case neg => exact fun args => msNegString (args 0)
    case falsum => exact fun _ => msAmbientBottom L
    case eq_ h s => exact fun args => msEqualityString h s (args 0) (args 1)
    case all s i => exact fun args => msAllString s i (args 0)
    case ex s i => exact fun args => msExString s i (args 0)

/-- Definition 10.2.2 (companion): The sorted family generated by variables
under every operation of the ambient string algebra. The Boolean generator
component is empty; bottom and propositional letters enter as nullary operations. -/
@[blueprint "chap10__definition_10_2_2"]
inductive MSGeneratedString (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop where
  | var (s : L.SortType) (i : Nat) :
      MSGeneratedString L (some s) (msAmbientVariable L s i)
  | operation (op : MSConstructorSymbol L)
      (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
        MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i))
      (generated : ∀ i, MSGeneratedString L _ (args i)) :
      MSGeneratedString L ((msConstructorAlphabet L).resultSort op)
        ((msAmbientStringAlgebra L).operation op args)

/-- Definition 10.2.2 (companion): Closure of a sorted subfamily under
all ambient string operations, including the nullaries. -/
@[blueprint "chap10__definition_10_2_2"]
def msStringSubalgebraClosed {L : MSLanguage}
    (C : (s : MSSyntaxSort L) → MSAmbientString L s → Prop) : Prop :=
  ∀ (op : MSConstructorSymbol L)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i)),
    (∀ i, C _ (args i)) → C _ ((msAmbientStringAlgebra L).operation op args)

/-- Definition 10.2.2 (companion): Every closed sorted family containing
V contains all generated strings, giving the least-subalgebra property. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msGeneratedString_least {L : MSLanguage}
    (C : (s : MSSyntaxSort L) → MSAmbientString L s → Prop)
    (variables : ∀ s i, C (some s) (msAmbientVariable L s i))
    (closed : msStringSubalgebraClosed C)
    {s : MSSyntaxSort L} {w : MSAmbientString L s} (h : MSGeneratedString L s w) :
    C s w 

/-- Definition 10.2.2: T(L,V), the least subalgebra of the corrected
ambient string algebra containing all sorted variables. Its carriers are
actual subtypes of strings; generation is a proposition on each string.
Operations restrict the ambient operations and preserve their printed equations. -/
@[blueprint "chap10__definition_10_2_2" (main := true)]
def msGeneratedStringAlgebra (L : MSLanguage) :
    LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L) where
  carrier := fun s => {w : MSAmbientString L s // MSGeneratedString L s w}
  carrierNonempty := by
    intro s
    cases s with
    | some s => exact ⟨⟨msAmbientVariable L s 0, .var s 0⟩⟩
    | none =>
      exact ⟨⟨msAmbientBottom L,
        .operation .falsum (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)⟩⟩
  operation := fun op args =>
    ⟨(msAmbientStringAlgebra L).operation op (fun i => (args i).val),
      .operation op (fun i => (args i).val) (fun i => (args i).property)⟩

/-- Theorem 10.2.1 (companion): Freeness of an actual sorted family C of
ambient strings over generators G and a chosen set of operation labels O.
Generation means containment, closure and leastness. The three freeness clauses
are injectivity on C-tuples, separation for distinct full labels, and exclusion
of generator values. Separation compares underlying token strings even when
result sorts differ. No injectivity is asserted on arbitrary malformed strings. -/
@[blueprint "chap10__theorem_10_2_1"]
structure MSStringFreeness (L : MSLanguage)
    (C G : (s : MSSyntaxSort L) → MSAmbientString L s → Prop)
    (O : MSConstructorSymbol L → Prop) : Prop where
  contains : ∀ s w, G s w → C s w
  closed : ∀ op, O op → ∀ args, (∀ i, C _ (args i)) →
    C _ ((msAmbientStringAlgebra L).operation op args)
  least : ∀ D : (s : MSSyntaxSort L) → MSAmbientString L s → Prop,
    (∀ s w, G s w → D s w) →
    (∀ op, O op → ∀ args, (∀ i, D _ (args i)) →
      D _ ((msAmbientStringAlgebra L).operation op args)) →
    ∀ s w, C s w → D s w
  free :
    (∀ op, O op → ∀ args more,
      (∀ i, C _ (args i)) → (∀ i, C _ (more i)) →
      (msAmbientStringAlgebra L).operation op args =
        (msAmbientStringAlgebra L).operation op more → args = more) ∧
    (∀ op other, O op → O other → op ≠ other → ∀ args more,
      (∀ i, C _ (args i)) → (∀ i, C _ (more i)) →
      ((msAmbientStringAlgebra L).operation op args).val ≠
        ((msAmbientStringAlgebra L).operation other more).val) ∧
    (∀ op, O op → ∀ args, (∀ i, C _ (args i)) →
      ¬ G _ ((msAmbientStringAlgebra L).operation op args))

/-- Theorem 10.2.1 (companion): V as a family of actual singleton strings;
its Boolean component is empty. -/
@[blueprint "chap10__theorem_10_2_1"]
def msVariableStringGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop
  | some s, w => ∃ i, msAmbientVariable L s i = w
  | none, _ => False

/-- Theorem 10.2.1: The actual generated string algebra T(L,V) is
freely generated by the sorted variable strings over the full expanded
signature, with injectivity and separation on generated argument strings. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1" (main := true)]
theorem msString_free_generation (L : MSLanguage) :
    MSStringFreeness L (MSGeneratedString L) (msVariableStringGenerators L)
      (fun _ => True) 

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
