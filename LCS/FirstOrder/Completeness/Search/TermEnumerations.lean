import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.Variables
import Attach
import LCS.FirstOrder.Completeness.Search.TermEnumerations.ProofsStamp

/-! # Organizing the terms: TERMS and AVAILᵢ (Section 5.5.1)

The reduct L′ of the input, the enumerations TERMS and AVAILᵢ of its terms, their
admissibility over given symbol sets, and the initial TERM₀ and AVAIL streams.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae

/-- Definition 5.5.1: The signed formulae of the possibly infinite input. -/
@[blueprint "chap5__definition_5_5_1"]
def inputSignedSet {L : Language} (q : InfSequentN L) : Set (SignedFormula L)
  | .trueF A => q.memAntecedent A
  | .falseF A => q.memSuccedent A

/-- Definition 5.5.1: The input supplies a free variable or a constant as a
term generator. -/
@[blueprint "chap5__definition_5_5_1"]
def hasInputGenerators {L : Language} (q : InfSequentN L) : Prop :=
  (∃ x, x ∈ signedSetFreeVars (inputSignedSet q)) ∨
    ∃ c, c ∈ signedSetConstSyms (inputSignedSet q)

/-- Definition 5.5.1: Initial variable generators are the input's free
variables, with y₀ supplied exactly when there are no input generators. -/
@[blueprint "chap5__definition_5_5_1"]
def initialVar {L : Language} (q : InfSequentN L) (x : Nat) : Prop :=
  x ∈ signedSetFreeVars (inputSignedSet q) ∨ (¬ hasInputGenerators q ∧ x = 1)

/-- Definition 5.5.1: A term uses the function and constant symbols of L′. -/
@[blueprint "chap5__definition_5_5_1"]
def termOverInput {L : Language} (q : InfSequentN L) (t : Term L) : Prop :=
  termFunSyms t ⊆ signedSetFunSyms (inputSignedSet q) ∧
    termConstSyms t ⊆ signedSetConstSyms (inputSignedSet q)

/-- Definition 5.5.1: TERMS consists exactly of L′-terms over the input
free variables and constants, or over y₀ and the function symbols when
there are no input generators. -/
@[blueprint "chap5__definition_5_5_1"]
def termsTerm {L : Language} (q : InfSequentN L) (t : Term L) : Prop :=
  termOverInput q t ∧ ∀ x, x ∈ termFV t → initialVar q x

/-- Definition 5.5.1: AVAILᵢ variables are the initial generators together
with y₁, …, yᵢ; y₀ is included precisely in the fallback case. -/
@[blueprint "chap5__definition_5_5_1"]
def availVar {L : Language} (q : InfSequentN L) (i x : Nat) : Prop :=
  initialVar q x ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ x = 2 * j + 1

/-- Definition 5.5.1: AVAILᵢ contains exactly the L′-terms over its
allowed generators that actually contain yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def availTerm {L : Language} (q : InfSequentN L) (i : Nat) (t : Term L) : Prop :=
  termOverInput q t ∧ (∀ x, x ∈ termFV t → availVar q i x) ∧
    2 * i + 1 ∈ termFV t

/-- Definition 5.5.1: A finite or infinite term stream has no holes and
lists each present term at most once; trailing empty markers may repeat. -/
@[blueprint "chap5__definition_5_5_1"]
structure TermStream (L : Language) where
  entries : Nat → Option (Term L)
  noHoles : ∀ n, entries n = none → entries (n + 1) = none
  some_injective : ∀ n m t, entries n = some t → entries m = some t → n = m

/-- Definition 5.5.1: The head of an exhausted term stream is absent. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.head {L : Language} (s : TermStream L) : Option (Term L) := s.entries 0

/-- Definition 5.5.1: Removing the head preserves no holes and uniqueness. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.tail {L : Language} (s : TermStream L) : TermStream L where
  entries := fun n => s.entries (n + 1)
  noHoles := fun n => s.noHoles (n + 1)
  some_injective := by
    intro n m t hn hm
    have h := s.some_injective (n + 1) (m + 1) t hn hm
    omega

/-- Definition 5.5.1: An exhausted stream contributes no terms. -/
@[blueprint "chap5__definition_5_5_1"]
def TermStream.empty (L : Language) : TermStream L where
  entries := fun _ => none
  noHoles := fun _ _ => rfl
  some_injective := by intro n m t h; cases h

/-- Definition 5.5.1: An admissible TERMS enumeration lists exactly the
initial term set; in the fallback case its first term is y₀. -/
@[blueprint "chap5__definition_5_5_1"]
structure TermsEnum {L : Language} (q : InfSequentN L) extends TermStream L where
  enumerates : ∀ t, (∃ n, entries n = some t) ↔ termsTerm q t
  fallback_head : ¬ hasInputGenerators q → entries 0 = some (yVar 0)

/-- Definition 5.5.1: An admissible AVAILᵢ enumeration, for i ≥ 1,
lists exactly the terms containing yᵢ over the prescribed generators,
and starts with yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
structure AvailEnum {L : Language} (q : InfSequentN L) (i : Nat)
    extends TermStream L where
  index_pos : 0 < i
  enumerates : ∀ t, (∃ n, entries n = some t) ↔ availTerm q i t
  starts_with : entries 0 = some (yVar i)

/-- Definition 5.5.1: The initial root has an empty formula record for
the head term; an absent head contributes no record. -/
@[blueprint "chap5__definition_5_5_1"]
def initialTermRecords {L : Language} (s : TermStream L) :
    List (Term L × List (FormulaN L)) :=
  match s.head with
  | none => []
  | some t => [(t, [])]

/-- Definition 5.5.1: Term bookkeeping at the unique initial root.
The formula lists are that root's records; AVAIL and NUMACT are global. -/
@[blueprint "chap5__definition_5_5_1"]
structure InitialTermState (L : Language) where
  term0 : List (Term L × List (FormulaN L))
  avail : Nat → TermStream L
  numact : Nat

/-- Definition 5.5.1: Initialize the root's TERM₀ from head(TERMS),
AVAIL₀ from tail(TERMS), each positive AVAILᵢ from its admissible
enumeration, and NUMACT to zero. -/
@[blueprint "chap5__definition_5_5_1"]
def initialTermState {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i) : InitialTermState L where
  term0 := initialTermRecords terms.toTermStream
  avail := fun i => match i with
    | 0 => terms.toTermStream.tail
    | j + 1 => (avail (j + 1) (by omega)).toTermStream
  numact := 0

end LCS.FirstOrder.Completeness.Search

namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae

/-- Definition 5.5.1: The allowed initial variables determined by the
constant symbols and free variables, with y₀ when both sets are empty. -/
@[blueprint "chap5__definition_5_5_1"]
def initialVarOfSymbols {L : Language} (cs : Set L.constSymbols) (fv : Set Nat)
    (x : Nat) : Prop :=
  fv x ∨ (¬ ((∃ x, fv x) ∨ ∃ c, cs c) ∧ x = 1)

/-- Definition 5.5.1: TERMS membership depends only on the function and
constant symbols of L′ and the set of initial free variables. -/
@[blueprint "chap5__definition_5_5_1"]
def termsTermOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (t : Term L) : Prop :=
  (termFunSyms t ⊆ fs ∧ termConstSyms t ⊆ cs) ∧
    ∀ x, x ∈ termFV t → initialVarOfSymbols cs fv x

/-- Definition 5.5.1: AVAILᵢ membership depends only on the symbols of L′,
the initial free variables, and y₁ through yᵢ, and requires occurrence of yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def availTermOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (i : Nat) (t : Term L) : Prop :=
  (termFunSyms t ⊆ fs ∧ termConstSyms t ⊆ cs) ∧
    (∀ x, x ∈ termFV t →
      initialVarOfSymbols cs fv x ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ x = 2 * j + 1) ∧
    2 * i + 1 ∈ termFV t

/-- Definition 5.5.1: Admissibility of a TERMS stream over fixed symbol
and variable sets. The stream supplies no holes and injectivity; this predicate
specifies its exact range and its first entry in the y₀ fallback case. -/
@[blueprint "chap5__definition_5_5_1"]
def TermsAdmissibleOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (stream : TermStream L) : Prop :=
  (∀ t, (∃ n, stream.entries n = some t) ↔ termsTermOfSymbols fs cs fv t) ∧
    (¬ ((∃ x, fv x) ∨ ∃ c, cs c) → stream.entries 0 = some (yVar 0))

/-- Definition 5.5.1: Admissibility of AVAILᵢ over fixed symbol and variable
sets: exact range, positive index, and first entry yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def AvailAdmissibleOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (i : Nat) (stream : TermStream L) : Prop :=
  0 < i ∧ (∀ t, (∃ n, stream.entries n = some t) ↔ availTermOfSymbols fs cs fv i t) ∧
    stream.entries 0 = some (yVar i)

end LCS.FirstOrder.Completeness.Search
end
