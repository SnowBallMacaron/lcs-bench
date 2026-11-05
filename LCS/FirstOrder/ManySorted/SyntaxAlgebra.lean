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

/-- Definition 10.2.1 (companion): The variable/nonlogical union as an
actual many-sorted ranked alphabet over S ∪ {bool}. -/
@[blueprint "chap10__definition_10_2_1"]
def msNonlogicalAlphabet (L : MSLanguage) : MSRankedAlphabet where
  SortType := MSSyntaxSort L
  symbols := MSNonlogicalSymbol L
  rank := msNonlogicalRank

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

/-- Definition 10.2.1 (companion): Variable identities preserve both sort and index. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msVarToken_injective (L : MSLanguage) : Function.Injective (msVarToken (L := L)) 

/-- Definition 10.2.1 (companion): Constant identities preserve the whole indexed family. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msConstToken_injective (L : MSLanguage) : Function.Injective (msConstToken (L := L)) 

/-- Definition 10.2.1 (companion): The function-symbol embedding is injective. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msFunToken_injective (L : MSLanguage) : Function.Injective (msFunToken (L := L)) 

/-- Definition 10.2.1 (companion): The predicate-symbol embedding is injective. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msPredToken_injective (L : MSLanguage) : Function.Injective (msPredToken (L := L)) 

/-- Definition 10.2.1 (companion): The four embedded families are pairwise
disjoint over all sorts, even when the original raw symbol carriers coincide. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msSymbolFamilies_disjoint (L : MSLanguage) :
    (∀ x c, msVarToken (L := L) x ≠ msConstToken c) ∧
    (∀ x f, msVarToken (L := L) x ≠ msFunToken f) ∧
    (∀ x P, msVarToken (L := L) x ≠ msPredToken P) ∧
    (∀ c f, msConstToken (L := L) c ≠ msFunToken f) ∧
    (∀ c P, msConstToken (L := L) c ≠ msPredToken P) ∧
    (∀ f P, msFunToken (L := L) f ≠ msPredToken P) 

/-- Definition 10.2.1 (companion): Distinct data sorts remain distinct. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msDataSort_injective (L : MSLanguage) :
    Function.Injective (some : L.SortType → MSSyntaxSort L) 

/-- Definition 10.2.1 (companion): The Boolean sort is separate from every data sort. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msDataSort_ne_bool (L : MSLanguage) (s : L.SortType) :
    (some s : MSSyntaxSort L) ≠ none 

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

/-- Definition 10.2.1 (companion): The source token of a constructor;
quantifier indices belong to the operation rather than the quantifier token. -/
@[blueprint "chap10__definition_10_2_1"]
def msConstructorToken {L : MSLanguage} : MSConstructorSymbol L → MSSourceToken L
  | .const s c => .nonlogical (.const s c)
  | .func f => .nonlogical (.func f)
  | .pred P => .nonlogical (.pred P)
  | .conj => .conj
  | .disj => .disj
  | .impl => .impl
  | .equiv_ => .equiv_
  | .neg => .neg
  | .falsum => .falsum
  | .eq_ h s => .eq_ h s
  | .all s _ => .all s
  | .ex s _ => .ex s

/-- Definition 10.2.1 (companion): Every expanded constructor has the rank
of its source symbol; auxiliary punctuation is not a constructor operation. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msConstructorToken_rank {L : MSLanguage} (op : MSConstructorSymbol L) :
    msSourceTokenRank (msConstructorToken op) = some (msConstructorRank op) 

open LCS.FirstOrder.Basic (FirstOrderLanguage)
open LCS.FirstOrder.Syntax.Algebra (SyntaxOperation FirstOrderSort syntaxAlphabet)

/-- Definition 10.2.1 (companion): An ordinary source language presented
with the singleton data sort Unit. Encoding maps are explicit presentation
data, witnessing the ordinary wrapper's countability propositions. -/
@[blueprint "chap10__definition_10_2_1"]
abbrev msFromOneSorted (O : FirstOrderLanguage)
    (ef : O.funSymbols → Nat) (hf : Function.Injective ef)
    (ec : O.constSymbols → Nat) (hc : Function.Injective ec)
    (ep : O.predSymbols → Nat) (hp : Function.Injective ep) : MSFirstOrderLanguage where
  SortType := Unit
  someSort := ()
  funSymbols := O.funSymbols
  funRank := fun f => (List.replicate (O.funArity f) (), ())
  funRank_nonempty := by
    intro f h
    have hz := congrArg List.length h
    simp only [List.length_replicate, List.length_nil] at hz
    exact Nat.ne_of_gt (O.funArity_pos f) hz
  constSymbols := fun _ => O.constSymbols
  predSymbols := O.predSymbols
  predArity := fun P => List.replicate (O.predArity P) ()
  hasEquality := O.hasEquality
  sortCode := fun _ => 0
  sortCode_injective := by intro a b _; cases a; cases b; rfl
  funCode := ef
  funCode_injective := hf
  constCode := fun _ => ec
  constCode_injective := fun _ => hc
  predCode := ep
  predCode_injective := hp

/-- Definition 10.2.1 (companion): A countable many-sorted source language
with one data sort has an ordinary presentation. Ordered input words become
their lengths; all symbol categories and the equality flag are retained. -/
@[blueprint "chap10__definition_10_2_1"]
def msToOneSorted (M : MSFirstOrderLanguage) [Subsingleton M.SortType] :
    FirstOrderLanguage where
  funSymbols := M.funSymbols
  funArity := fun f => (M.funRank f).1.length
  constSymbols := M.constSymbols M.someSort
  predSymbols := M.predSymbols
  predArity := fun P => (M.predArity P).length
  hasEquality := M.hasEquality
  funSymbols_countable := ⟨M.funCode, M.funCode_injective⟩
  constSymbols_countable := ⟨M.constCode M.someSort, M.constCode_injective M.someSort⟩
  predSymbols_countable := ⟨M.predCode, M.predCode_injective⟩
  funArity_pos := fun f => List.length_pos_iff.mpr (M.funRank_nonempty f)

/-- Definition 10.2.1 (companion): Returning from the singleton presentation
recovers the ordinary source language, including every arity and equality flag. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msToOneSorted_from (O : FirstOrderLanguage)
    (ef : O.funSymbols → Nat) (hf : Function.Injective ef)
    (ec : O.constSymbols → Nat) (hc : Function.Injective ec)
    (ep : O.predSymbols → Nat) (hp : Function.Injective ep) :
    msToOneSorted (msFromOneSorted O ef hf ec hc ep hp) = O 

/-- Definition 10.2.1 (companion): Every ordinary source language has a
singleton-data-sort presentation. Countability witnesses are unpacked only
in this proposition; msFromOneSorted is the explicit data construction. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msOneSorted_has_singleton_presentation (O : FirstOrderLanguage) :
    ∃ M : MSFirstOrderLanguage, ∃ h : Subsingleton M.SortType,
      @msToOneSorted M h = O 

/-- Definition 10.2.1 (companion): Erase the singleton data-sort label,
keeping the data/formula distinction of ordinary primitive syntax. -/
@[blueprint "chap10__definition_10_2_1"]
def msEraseSingletonSort {M : MSFirstOrderLanguage} : MSSyntaxSort M.toMSLanguage → FirstOrderSort
  | some _ => .term
  | none => .formula

/-- Definition 10.2.1 (companion): Restore the unique data-sort label. -/
@[blueprint "chap10__definition_10_2_1"]
def msRestoreSingletonSort (M : MSFirstOrderLanguage) : FirstOrderSort → MSSyntaxSort M.toMSLanguage
  | .term => some M.someSort
  | .formula => none

/-- Definition 10.2.1 (companion): Erasing and restoring singleton sorts is inverse. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msSingletonSort_inverse (M : MSFirstOrderLanguage) [Subsingleton M.SortType] :
    (∀ s, msRestoreSingletonSort M (msEraseSingletonSort (M := M) s) = s) ∧
    (∀ s, msEraseSingletonSort (M := M) (msRestoreSingletonSort M s) = s) 

/-- Definition 10.2.1 (companion): Singleton-sort constructor correspondence,
preserving every primitive connective, both quantifier indices and equality. -/
@[blueprint "chap10__definition_10_2_1"]
def msEraseSingletonConstructor (M : MSFirstOrderLanguage) [Subsingleton M.SortType] :
    MSConstructorSymbol M.toMSLanguage → SyntaxOperation (msToOneSorted M).toLanguage
  | .const s c => .const (show M.constSymbols M.someSort from Subsingleton.elim s M.someSort ▸ c)
  | .func f => .func f
  | .pred P => .pred P
  | .conj => .conj
  | .disj => .disj
  | .impl => .impl
  | .equiv_ => .equiv
  | .neg => .neg
  | .falsum => .bot
  | .eq_ h _ => .eq h
  | .all _ i => .all i
  | .ex _ i => .ex i

/-- Definition 10.2.1 (companion): Restore singleton-sort constructors from
ordinary syntax operations, with all symbol payloads unchanged. -/
@[blueprint "chap10__definition_10_2_1"]
def msRestoreSingletonConstructor (M : MSFirstOrderLanguage) [Subsingleton M.SortType] :
    SyntaxOperation (msToOneSorted M).toLanguage → MSConstructorSymbol M.toMSLanguage
  | .const c => .const M.someSort c
  | .func f => .func f
  | .pred P => .pred P
  | .conj => .conj
  | .disj => .disj
  | .impl => .impl
  | .equiv => .equiv_
  | .neg => .neg
  | .bot => .falsum
  | .eq h => .eq_ h M.someSort
  | .all i => .all M.someSort i
  | .ex i => .ex M.someSort i

/-- Definition 10.2.1 (companion): The constructor presentation maps are
inverse in both directions, including dependent constant fibers. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msSingletonConstructor_inverse (M : MSFirstOrderLanguage) [Subsingleton M.SortType] :
    (∀ op, msRestoreSingletonConstructor M (msEraseSingletonConstructor M op) = op) ∧
    (∀ op, msEraseSingletonConstructor M (msRestoreSingletonConstructor M op) = op) 

/-- Definition 10.2.1 (companion): Erasing the singleton sort preserves the
entire ordered rank of every primitive syntax operation. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msSingletonConstructor_rank (M : MSFirstOrderLanguage) [Subsingleton M.SortType]
    (op : MSConstructorSymbol M.toMSLanguage) :
    ((msConstructorRank op).1.map (msEraseSingletonSort (M := M)),
      msEraseSingletonSort (M := M) (msConstructorRank op).2) =
    (syntaxAlphabet (msToOneSorted M).toLanguage).rank (msEraseSingletonConstructor M op) 

/-- Definition 10.2.1 (companion): Variables correspond by their Nat index;
the unique data sort is restored without changing that index. -/
@[blueprint "chap10__definition_10_2_1"]
theorem msSingletonVariable_inverse (M : MSFirstOrderLanguage) [Subsingleton M.SortType]
    (x : MSVar M.toMSLanguage) : (M.someSort, x.2) = x 

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

/-- Definition 10.2.2 (companion): Boolean ambient strings are exactly
all nonempty strings over the enlarged alphabet. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientBool_iff {L : MSLanguage} (w : MSTokenString L) :
    msAmbientStringAt none w ↔ w ≠ [] 

/-- Definition 10.2.2 (companion): The original first-token condition is
retained for every data sort. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientData_iff {L : MSLanguage} (s : L.SortType) (w : MSTokenString L) :
    msAmbientStringAt (some s) w ↔ msStringHeadSort w = some (some s) 

/-- Definition 10.2.2 (companion): Every sorted ambient string is nonempty. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientString_nonempty {L : MSLanguage} {s : MSSyntaxSort L}
    {w : MSTokenString L} (h : msAmbientStringAt s w) : w ≠ [] 

/-- Definition 10.2.2 (companion): Any tail is allowed after a ranked head
of the required sort; ambient strings need not satisfy formation rules. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientString_cons {L : MSLanguage} (a : MSSourceToken L)
    (u : List (MSSyntaxSort L)) (s : MSSyntaxSort L)
    (hrank : msSourceTokenRank a = some (u, s)) (tail : MSTokenString L) :
    msAmbientStringAt s (a :: tail) 

/-- Definition 10.2.2 (companion): Appending any suffix preserves an
ambient sort. No constraint is imposed on the suffix. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientString_append {L : MSLanguage} {s : MSSyntaxSort L}
    {w : MSTokenString L} (h : msAmbientStringAt s w) (tail : MSTokenString L) :
    msAmbientStringAt s (w ++ tail) 

/-- Definition 10.2.2 (companion): Every nonempty printed prefix yields a
Boolean ambient string with any suffix. This covers parenthesized binary
constructors, negation, predicates, equality, and sorted quantifier prefixes. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientBool_prefix {L : MSLanguage} (pre tail : MSTokenString L)
    (h : pre ≠ []) : msAmbientStringAt none (pre ++ tail) 

/-- Definition 10.2.2 (companion): Data ambient carriers embed into the
Boolean ambient family at the level of underlying strings. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientData_isBool {L : MSLanguage} (s : L.SortType)
    (w : MSTokenString L) (h : msAmbientStringAt (some s) w) :
    msAmbientStringAt none w 

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

/-- Definition 10.2.2 (companion): The defining concatenation equation of C_f. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msFunctionString_val {L : MSLanguage} (f : L.funSymbols)
    (args : (i : Fin (L.funRank f).1.length) →
      MSAmbientString L (some ((L.funRank f).1.get i))) :
    (msFunctionString f args).val =
      msFunToken f :: (List.ofFn (fun i => (args i).val)).flatten 

/-- Definition 10.2.2 (companion): The defining concatenation equation of C_P. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msPredicateString_val {L : MSLanguage} (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) →
      MSAmbientString L (some ((L.predArity P).get i))) :
    (msPredicateString P args).val =
      msPredToken P :: (List.ofFn (fun i => (args i).val)).flatten 

/-- Definition 10.2.2 (companion): The defining same-sort equality concatenation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msEqualityString_val {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (t u : MSAmbientString L (some s)) :
    (msEqualityString hL s t u).val = MSSourceToken.eq_ hL s :: (t.val ++ u.val) 

/-- Definition 10.2.2 (companion): Empty predicate arity produces exactly P. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msPredicateString_nullary {L : MSLanguage} (P : L.predSymbols)
    (h : L.predArity P = [])
    (args : (i : Fin (L.predArity P).length) →
      MSAmbientString L (some ((L.predArity P).get i))) :
    (msPredicateString P args).val = [msPredToken P] 

/-- Definition 10.2.2 (companion): The function string operation has the
ordered data-input word and data-output sort of its function symbol. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msFunctionString_rank {L : MSLanguage} (f : L.funSymbols) :
    (msConstructorAlphabet L).rank (.func f) =
      ((L.funRank f).1.map some, some (L.funRank f).2) 

/-- Definition 10.2.2 (companion): The predicate string operation has
its declared data-input word, including the empty word, and Boolean output. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msPredicateString_rank {L : MSLanguage} (P : L.predSymbols) :
    (msConstructorAlphabet L).rank (.pred P) = ((L.predArity P).map some, none) 

/-- Definition 10.2.2 (companion): Equality string formation has rank (ss,bool). -/
@[blueprint "chap10__definition_10_2_2"]
theorem msEqualityString_rank {L : MSLanguage} (hL : L.hasEquality = true) (s : L.SortType) :
    (msConstructorAlphabet L).rank (.eq_ hL s) = ([some s, some s], none) 

/-- Definition 10.2.2 (companion): The constant nullary is the singleton constant token in its data sort. -/
@[blueprint "chap10__definition_10_2_2"]
def msConstantString {L : MSLanguage} (s : L.SortType) (c : L.constSymbols s) :
    MSAmbientString L (some s) := ⟨[msConstToken ⟨s, c⟩], rfl⟩

/-- Definition 10.2.2 (companion): A propositional letter is a predicate with empty arity, interpreted as its singleton token. -/
@[blueprint "chap10__definition_10_2_2"]
def msPropositionalLetterString {L : MSLanguage} (P : L.predSymbols)
    (_h : L.predArity P = []) : MSAmbientString L none :=
  ⟨[msPredToken P], by intro h; cases h⟩

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

/-- Definition 10.2.2 (companion): The constant string equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msConstantString_val {L : MSLanguage} (s : L.SortType) (c : L.constSymbols s) :
    (msConstantString s c).val = [msConstToken ⟨s, c⟩] 

/-- Definition 10.2.2 (companion): The propositional-letter string equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msPropositionalLetterString_val {L : MSLanguage} (P : L.predSymbols)
    (h : L.predArity P = []) :
    (msPropositionalLetterString P h).val = [msPredToken P] 

/-- Definition 10.2.2 (companion): The bottom nullary is the singleton bottom token. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientBottom_val (L : MSLanguage) :
    (msAmbientBottom L).val = [MSSourceToken.falsum] 

/-- Definition 10.2.2 (companion): The defining parenthesized concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msConjString_val {L : MSLanguage} (A B : MSAmbientString L none) :
    (msConjString A B).val = .lparen :: (A.val ++ [.conj] ++ B.val ++ [.rparen]) 

/-- Definition 10.2.2 (companion): The defining parenthesized concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msDisjString_val {L : MSLanguage} (A B : MSAmbientString L none) :
    (msDisjString A B).val = .lparen :: (A.val ++ [.disj] ++ B.val ++ [.rparen]) 

/-- Definition 10.2.2 (companion): The defining parenthesized concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msImplString_val {L : MSLanguage} (A B : MSAmbientString L none) :
    (msImplString A B).val = .lparen :: (A.val ++ [.impl] ++ B.val ++ [.rparen]) 

/-- Definition 10.2.2 (companion): The defining parenthesized concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msEquivString_val {L : MSLanguage} (A B : MSAmbientString L none) :
    (msEquivString A B).val = .lparen :: (A.val ++ [.equiv_] ++ B.val ++ [.rparen]) 

/-- Definition 10.2.2 (companion): The defining negation concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msNegString_val {L : MSLanguage} (A : MSAmbientString L none) :
    (msNegString A).val = .neg :: A.val 

/-- Definition 10.2.2 (companion): The defining sorted quantifier concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAllString_val {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSAmbientString L none) :
    (msAllString s i A).val = .all s :: msVarToken (s, i) :: A.val 

/-- Definition 10.2.2 (companion): The defining sorted quantifier concatenation equation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msExString_val {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSAmbientString L none) :
    (msExString s i A).val = .ex s :: msVarToken (s, i) :: A.val 

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

/-- Definition 10.2.2 (companion): Every full-signature operation closes in its declared ambient result sort. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientStringAlgebra_closed (L : MSLanguage) (op : MSConstructorSymbol L)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i)) :
    msAmbientStringAt ((msConstructorAlphabet L).resultSort op)
      ((msAmbientStringAlgebra L).operation op args).val 

/-- Definition 10.2.2 (companion): The algebra predicate nullary agrees with the propositional-letter operation. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msAmbientStringAlgebra_propositionalLetter {L : MSLanguage} (P : L.predSymbols)
    (h : L.predArity P = [])
    (args : (i : Fin ((msConstructorAlphabet L).argSorts (.pred P)).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts (.pred P)).get i)) :
    (msAmbientStringAlgebra L).operation (.pred P) args = msPropositionalLetterString P h 

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

/-- Definition 10.2.2 (companion): The generated family contains every variable. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msGeneratedString_variable (L : MSLanguage) (s : L.SortType) (i : Nat) :
    MSGeneratedString L (some s) (msAmbientVariable L s i) 

/-- Definition 10.2.2 (companion): The generated family is a subalgebra. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msGeneratedString_closed (L : MSLanguage) :
    msStringSubalgebraClosed (MSGeneratedString L) 

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

/-- Definition 10.2.2 (companion): The generated operations are exactly
the restrictions of the ambient operations to generated arguments. -/
@[blueprint "chap10__definition_10_2_2"]
theorem msGeneratedStringAlgebra_operation (L : MSLanguage) (op : MSConstructorSymbol L)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      (msGeneratedStringAlgebra L).carrier (((msConstructorAlphabet L).argSorts op).get i)) :
    ((msGeneratedStringAlgebra L).operation op args).val =
      (msAmbientStringAlgebra L).operation op (fun i => (args i).val) 

/-- Definition 10.2.2 (companion): Concrete sorted printing of term ASTs
into the ambient strings, preserving variables, constants and prefix functions. -/
@[blueprint "chap10__definition_10_2_2"]
def msPrintTerm {L : MSLanguage} : {s : L.SortType} → MSTerm L s → MSAmbientString L (some s)
  | _, .var s i => msAmbientVariable L s i
  | _, .const s c => msConstantString s c
  | _, .func f args => msFunctionString f (fun i => msPrintTerm (args i))

/-- Definition 10.2.2 (companion): Concrete formula printing uses the
printed ambient operations, preserving every primitive connective and sorted binder. -/
@[blueprint "chap10__definition_10_2_2"]
def msPrintFormula {L : MSLanguage} : MSFormula L → MSAmbientString L none
  | .falsum => msAmbientBottom L
  | .pred P args => msPredicateString P (fun i => msPrintTerm (args i))
  | .eq_ h s t u => msEqualityString h s (msPrintTerm t) (msPrintTerm u)
  | .conj A B => msConjString (msPrintFormula A) (msPrintFormula B)
  | .disj A B => msDisjString (msPrintFormula A) (msPrintFormula B)
  | .impl A B => msImplString (msPrintFormula A) (msPrintFormula B)
  | .equiv_ A B => msEquivString (msPrintFormula A) (msPrintFormula B)
  | .neg A => msNegString (msPrintFormula A)
  | .all s i A => msAllString s i (msPrintFormula A)
  | .ex s i A => msExString s i (msPrintFormula A)

/-- Definition 10.2.2 (companion): The data-sort carrier of T(L,V) is
exactly the printed sort-s term ASTs, as an equality of subsets of ambient strings. -/
@[attach_debt, blueprint "chap10__definition_10_2_2"]
theorem msGeneratedString_iff_term {L : MSLanguage} (s : L.SortType)
    (w : MSAmbientString L (some s)) :
    MSGeneratedString L (some s) w ↔ ∃ t : MSTerm L s, msPrintTerm t = w 

/-- Definition 10.2.2 (companion): The Boolean carrier of T(L,V) is
exactly the printed formula ASTs, including bottom and nullary predicates. -/
@[attach_debt, blueprint "chap10__definition_10_2_2"]
theorem msGeneratedString_iff_formula {L : MSLanguage} (w : MSAmbientString L none) :
    MSGeneratedString L none w ↔ ∃ A : MSFormula L, msPrintFormula A = w 

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

/-- Theorem 10.2.1 (companion): The term-string family, with empty
Boolean component, inherited from the generated string algebra. -/
@[blueprint "chap10__theorem_10_2_1"]
def msTermStringCarrier (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop
  | some s, w => MSGeneratedString L (some s) w
  | none, _ => False

/-- Theorem 10.2.1 (companion): Separate term generators are exactly
singleton variables and constants of the requested data sort. -/
@[blueprint "chap10__theorem_10_2_1"]
def msTermStringGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop
  | some s, w => (∃ i, msAmbientVariable L s i = w) ∨
      (∃ c, msConstantString s c = w)
  | none, _ => False

/-- Theorem 10.2.1 (companion): Functions C_f are precisely the
operations for the separate term-string generation assertion. -/
@[blueprint "chap10__theorem_10_2_1"]
def msTermStringOperations {L : MSLanguage} : MSConstructorSymbol L → Prop
  | .func _ => True
  | _ => False

/-- Theorem 10.2.1 (companion): Atomic strings are bottom, predicates
on generated term strings (including empty arity), or available same-sort
equalities on generated term strings. -/
@[blueprint "chap10__theorem_10_2_1"]
def msAtomicString {L : MSLanguage} (w : MSAmbientString L none) : Prop :=
  w = msAmbientBottom L ∨
  (∃ (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) →
      MSAmbientString L (some ((L.predArity P).get i))),
    (∀ i, MSGeneratedString L _ (args i)) ∧ msPredicateString P args = w) ∨
  (∃ (h : L.hasEquality = true) (s : L.SortType)
    (t u : MSAmbientString L (some s)),
    MSGeneratedString L (some s) t ∧ MSGeneratedString L (some s) u ∧
      msEqualityString h s t u = w)

/-- Theorem 10.2.1 (companion): The formula-string family is the
Boolean generated carrier, with empty data components. -/
@[blueprint "chap10__theorem_10_2_1"]
def msFormulaStringCarrier (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop
  | none, w => MSGeneratedString L none w
  | some _, _ => False

/-- Theorem 10.2.1 (companion): Separate formula generators are the
atomic strings, all at bool. -/
@[blueprint "chap10__theorem_10_2_1"]
def msFormulaStringGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSAmbientString L s → Prop
  | none, w => msAtomicString w
  | some _, _ => False

/-- Theorem 10.2.1 (companion): Formula formation uses the five
connectives and the variable-indexed sorted quantifiers. Atomic operations
are excluded because their values are the generators of this separate claim. -/
@[blueprint "chap10__theorem_10_2_1"]
def msFormulaStringOperations {L : MSLanguage} : MSConstructorSymbol L → Prop
  | .conj | .disj | .impl | .equiv_ | .neg | .all _ _ | .ex _ _ => True
  | _ => False

/-- Theorem 10.2.1: The actual generated string algebra T(L,V) is
freely generated by the sorted variable strings over the full expanded
signature, with injectivity and separation on generated argument strings. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1" (main := true)]
theorem msString_free_generation (L : MSLanguage) :
    MSStringFreeness L (MSGeneratedString L) (msVariableStringGenerators L)
      (fun _ => True) 

/-- Theorem 10.2.1 (companion): Term strings are freely generated
by variables/constants under the functions C_f, separately from formulae. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msTermString_free_generation (L : MSLanguage) :
    MSStringFreeness L (msTermStringCarrier L) (msTermStringGenerators L)
      msTermStringOperations 

/-- Theorem 10.2.1 (companion): Formula strings are freely generated
by atomic strings under the connectives and sorted indexed quantifiers. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msFormulaString_free_generation (L : MSLanguage) :
    MSStringFreeness L (msFormulaStringCarrier L) (msFormulaStringGenerators L)
      msFormulaStringOperations 

/-- Theorem 10.2.1 (companion): Each expanded string operation is
injective on its correctly sorted tuples of generated strings. -/
@[blueprint "chap10__theorem_10_2_1"]
theorem msString_operation_injective (L : MSLanguage) (op : MSConstructorSymbol L)
    (args more : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i))
    (ha : ∀ i, MSGeneratedString L _ (args i))
    (hb : ∀ i, MSGeneratedString L _ (more i))
    (h : (msAmbientStringAlgebra L).operation op args =
      (msAmbientStringAlgebra L).operation op more) : args = more 

/-- Theorem 10.2.1 (companion): Different full operation labels have
disjoint string ranges on generated inputs. In particular different function
symbols, or different sort/index labels of one quantifier kind, are separated. -/
@[blueprint "chap10__theorem_10_2_1"]
theorem msString_operation_separated (L : MSLanguage) (op other : MSConstructorSymbol L)
    (hne : op ≠ other)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i))
    (more : (i : Fin ((msConstructorAlphabet L).argSorts other).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts other).get i))
    (ha : ∀ i, MSGeneratedString L _ (args i))
    (hb : ∀ i, MSGeneratedString L _ (more i)) :
    ((msAmbientStringAlgebra L).operation op args).val ≠
      ((msAmbientStringAlgebra L).operation other more).val 

/-- Theorem 10.2.1 (companion): No string operation on generated
arguments produces a variable generator. -/
@[blueprint "chap10__theorem_10_2_1"]
theorem msString_operation_not_variable (L : MSLanguage) (op : MSConstructorSymbol L)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSAmbientString L (((msConstructorAlphabet L).argSorts op).get i))
    (ha : ∀ i, MSGeneratedString L _ (args i)) :
    ¬ msVariableStringGenerators L _ ((msAmbientStringAlgebra L).operation op args) 

/-- Theorem 10.2.1 (companion): Distinct function labels already have
disjoint ranges on arbitrary ambient argument strings, by their first tokens. -/
@[blueprint "chap10__theorem_10_2_1"]
theorem msFunctionString_separated {L : MSLanguage} (f g : L.funSymbols) (hne : f ≠ g)
    (args : (i : Fin (L.funRank f).1.length) →
      MSAmbientString L (some ((L.funRank f).1.get i)))
    (more : (i : Fin (L.funRank g).1.length) →
      MSAmbientString L (some ((L.funRank g).1.get i))) :
    (msFunctionString f args).val ≠ (msFunctionString g more).val 


/-- Theorem 10.2.1 (companion): A sortwise map preserves every operation
of the expanded signature, including nullaries and both indexed quantifiers. -/
@[blueprint "chap10__theorem_10_2_1"]
def MSExpandedHom {L : MSLanguage}
    (A B : LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L))
    (f : (s : MSSyntaxSort L) → A.carrier s → B.carrier s) : Prop :=
  ∀ op args, f _ (A.operation op args) = B.operation op (fun i => f _ (args i))

/-- Theorem 10.2.1 (companion): The variable inclusion into T(L,V). -/
@[blueprint "chap10__theorem_10_2_1"]
def msGeneratedVariable (L : MSLanguage) (s : L.SortType) (i : Nat) :
    (msGeneratedStringAlgebra L).carrier (some s) :=
  ⟨msAmbientVariable L s i, .var s i⟩

/-- Theorem 10.2.1 (companion): Restriction to the sorted variable family,
independent of operation preservation or the extension theorem. -/
@[blueprint "chap10__theorem_10_2_1"]
def MSVariableRestriction {L : MSLanguage}
    (B : LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L))
    (assignment : (s : L.SortType) → Nat → B.carrier (some s))
    (f : (s : MSSyntaxSort L) → (msGeneratedStringAlgebra L).carrier s → B.carrier s) : Prop :=
  ∀ s i, f (some s) (msGeneratedVariable L s i) = assignment s i

/-- Theorem 10.2.1 (companion): Every sorted assignment of variables into
any algebra of the expanded signature extends to exactly one homomorphism
from the actual generated string algebra T(L,V). -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msString_universal_extension (L : MSLanguage)
    (B : LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L))
    (assignment : (s : L.SortType) → Nat → B.carrier (some s)) :
    ∃ f : (s : MSSyntaxSort L) → (msGeneratedStringAlgebra L).carrier s → B.carrier s,
      MSExpandedHom (msGeneratedStringAlgebra L) B f ∧ MSVariableRestriction B assignment f ∧
      ∀ g, MSExpandedHom (msGeneratedStringAlgebra L) B g →
        MSVariableRestriction B assignment g → g = f

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
