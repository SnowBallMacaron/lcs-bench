import LCS.FirstOrder.Completeness.Search
import Attach
import LCS.FirstOrder.Effective.Presentation.ProofsStamp

/-! # Effective presentations for first-order search

The provider fields below are the recursive symbol-set, rank, and input-position
premises. In the computable-Lean-function reading, implementations supply these
fields by compiled Lean definitions. This interface alone does not certify the
computability of an arbitrary function supplied noncomputably. All operations
implemented here are executable relative to the supplied providers.

Input positions contain the existing finite typed syntax. Symbol decoding checks
membership in the presented signature; symbol equality compares natural codes.
Canonical input order is increasing formula-code order. Finite prefix access is
separate from deciding an infinite range. No term/EQ enumerator or search solver
is part of the presentation premises.
-/

namespace LCS.FirstOrder.Effective

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae LCS.FirstOrder.Completeness.Search

/-- Definition 5.5.1 (effective presentation): Recursive sets of natural-number
codes for symbols, computable ranks, and the equality flag. Function symbols
have positive rank; predicate rank zero is allowed. -/
@[blueprint "chap5__definition_5_5_1"]
structure EffectivePresentation where
  functionSymbol : Nat → Bool
  constantSymbol : Nat → Bool
  predicateSymbol : Nat → Bool
  functionRank : Nat → Nat
  predicateRank : Nat → Nat
  functionRank_pos : ∀ n, functionSymbol n = true → 0 < functionRank n
  hasEquality : Bool


/-- Erase the presentation to the current language type. Each symbol retains
its natural code and a proof that the corresponding membership test accepts it. -/
@[blueprint "chap5__definition_5_5_1"]
def EffectivePresentation.toLanguage (p : EffectivePresentation) : Language where
  funSymbols := {n : Nat // p.functionSymbol n = true}
  funArity := fun f => p.functionRank f.val
  constSymbols := {n : Nat // p.constantSymbol n = true}
  predSymbols := {n : Nat // p.predicateSymbol n = true}
  predArity := fun P => p.predicateRank P.val
  hasEquality := p.hasEquality

/-- The erased signature has countable symbol sets and positive function ranks. -/
@[blueprint "chap5__definition_5_5_1"]
def EffectivePresentation.toFirstOrderLanguage (p : EffectivePresentation) : FirstOrderLanguage :=
  { p.toLanguage with
    funSymbols_countable := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    constSymbols_countable := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    predSymbols_countable := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    funArity_pos := fun f => p.functionRank_pos f.val f.property }

/-- Decode a symbol code using its recursive membership test. Invalid codes
return none. The same decoder serves function, constant, and predicate symbols. -/
@[blueprint "chap5__definition_5_5_1"]
def decodeSymbol (accept : Nat → Bool) (n : Nat) : Option {c : Nat // accept c = true} :=
  if h : accept n = true then some ⟨n, h⟩ else none

/-- Decoding recovers each admitted symbol at exactly its own code. -/
theorem decodeSymbol_eq_some (accept : Nat → Bool) (n : Nat)
    (s : {c : Nat // accept c = true}) :
    decodeSymbol accept n = some s ↔ n = s.val 

/-- Executable symbol equality compares codes, ignoring membership proofs. -/
def symbolEq {accept : Nat → Bool} (a b : {c : Nat // accept c = true}) : Bool :=
  a.val == b.val

/-- Code comparison reflects equality of presented symbols. -/
theorem symbolEq_correct {accept : Nat → Bool} (a b : {c : Nat // accept c = true}) :
    symbolEq a b = true ↔ a = b 

/-- A positive pairing code: the first component determines the power of two
and the second determines the odd factor. Zero is reserved for the empty list. -/
def pairCode (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

/-- A finite term's natural code, computed from its constructors and symbol
codes. Argument lists retain their order. -/
@[blueprint "chap5__definition_5_5_1"]
def termCode {p : EffectivePresentation} : Term p.toLanguage → Nat
  | .var n => pairCode 0 n
  | .const c => pairCode 1 c.val
  | .func f ts => pairCode 2 (pairCode f.val
      ((List.ofFn fun i => termCode (ts i)).foldr pairCode 0))

/-- A normalized formula's natural code. The constructor tags distinguish
all connectives; the equality constructor retains both ordered terms. -/
@[blueprint "chap5__definition_5_5_1"]
def formulaCode {p : EffectivePresentation} : FormulaN p.toLanguage → Nat
  | .predN P ts => pairCode 0 (pairCode P.val
      ((List.ofFn fun i => termCode (ts i)).foldr pairCode 0))
  | .eq_ _ t u => pairCode 1 (pairCode (termCode t) (termCode u))
  | .neg A => pairCode 2 (formulaCode A)
  | .conj A B => pairCode 3 (pairCode (formulaCode A) (formulaCode B))
  | .disj A B => pairCode 4 (pairCode (formulaCode A) (formulaCode B))
  | .impl A B => pairCode 5 (pairCode (formulaCode A) (formulaCode B))
  | .all x A => pairCode 6 (pairCode x (formulaCode A))
  | .ex x A => pairCode 7 (pairCode x (formulaCode A))

/-- Definition 5.5.1 (effective input): Finite or infinite position access to
an input, with no holes, in canonical increasing formula-code order on each
side. The recursive symbol sets of the input reduct are supplied separately,
with exact occurrence specifications. They are source premises, not inferred
from position access. No free-variable-range or term/EQ-list decision oracle
is assumed. The provider functions must be supplied as executable code. -/
@[blueprint "chap5__definition_5_5_1"]
structure EffectiveInput (p : EffectivePresentation) where
  input : InfSequentN p.toLanguage
  antecedent_increasing : ∀ n m A B,
    n < m → input.antecedent n = some A → input.antecedent m = some B →
      formulaCode A < formulaCode B
  succedent_increasing : ∀ n m A B,
    n < m → input.succedent n = some A → input.succedent m = some B →
      formulaCode A < formulaCode B
  functionOccurs : Nat → Bool
  constantOccurs : Nat → Bool
  predicateOccurs : Nat → Bool
  functionOccurs_spec : ∀ n, functionOccurs n = true ↔
    ∃ f, decodeSymbol p.functionSymbol n = some f ∧
      f ∈ signedSetFunSyms (inputSignedSet input)
  constantOccurs_spec : ∀ n, constantOccurs n = true ↔
    ∃ c, decodeSymbol p.constantSymbol n = some c ∧
      c ∈ signedSetConstSyms (inputSignedSet input)
  predicateOccurs_spec : ∀ n, predicateOccurs n = true ↔
    ∃ P, decodeSymbol p.predicateSymbol n = some P ∧
      P ∈ signedSetPredSyms (inputSignedSet input)

/-- Erase the effective input to the input type used by search51 and searchEq. -/
@[blueprint "chap5__definition_5_5_1"]
def EffectiveInput.toInfSequent {p : EffectivePresentation} (q : EffectiveInput p) :
    InfSequentN p.toLanguage := q.input

/-- Access the first k antecedent positions; this operation terminates after
k calls to the input provider, independently of whether the input is finite. -/
@[blueprint "chap5__definition_5_5_1"]
def EffectiveInput.antecedentPrefix {p : EffectivePresentation} (q : EffectiveInput p)
    (k : Nat) : List (FormulaN p.toLanguage) :=
  (List.range k).filterMap q.input.antecedent

/-- Access the first k succedent positions. No test of an eventual infinite
range is performed. -/
@[blueprint "chap5__definition_5_5_1"]
def EffectiveInput.succedentPrefix {p : EffectivePresentation} (q : EffectiveInput p)
    (k : Nat) : List (FormulaN p.toLanguage) :=
  (List.range k).filterMap q.input.succedent

/-- Finite antecedent access agrees exactly with the erased input positions. -/
theorem EffectiveInput.mem_antecedentPrefix {p : EffectivePresentation} (q : EffectiveInput p)
    (k : Nat) (A : FormulaN p.toLanguage) :
    A ∈ q.antecedentPrefix k ↔ ∃ n, n < k ∧ q.toInfSequent.antecedent n = some A 

/-- Finite succedent access agrees exactly with the erased input positions. -/
theorem EffectiveInput.mem_succedentPrefix {p : EffectivePresentation} (q : EffectiveInput p)
    (k : Nat) (A : FormulaN p.toLanguage) :
    A ∈ q.succedentPrefix k ↔ ∃ n, n < k ∧ q.toInfSequent.succedent n = some A 

end LCS.FirstOrder.Effective
