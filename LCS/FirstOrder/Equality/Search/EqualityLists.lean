import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.FirstOrder.Equality.Search.EqualityLists.ProofsStamp

section
namespace LCS.FirstOrder.Equality.Search
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.6.3: At level i the term domain is TERMS ∪ AVAIL₁ ∪ … ∪ AVAILᵢ,
using the initial enumerations, including the y₀ fallback in TERMS. -/
@[blueprint "chap5__definition_5_6_3"]
def levelTerm {L : Language} (q : InfSequentN L) (i : Nat) (t : Term L) : Prop :=
  termsTerm q t ∨ ∃ k, 0 < k ∧ k ≤ i ∧ availTerm q k t

/-- Definition 5.6.3: Every argument lies in the level domain, and a positive
level uses at least one term from its own AVAILᵢ (the mixed-term reading). -/
@[blueprint "chap5__definition_5_6_3"]
def levelArguments {L : Language} (q : InfSequentN L) (i : Nat)
    (ts : List (Term L)) : Prop :=
  (∀ t ∈ ts, levelTerm q i t) ∧ (i = 0 ∨ ∃ t ∈ ts, availTerm q i t)

/-- Definition 5.6.3: The EQ families over the input reduct. Function congruence
uses positive ranks; EQ₃ includes every predicate rank and equality congruence.
The axiom constructors implement the right-nested conjunctions. -/
@[blueprint "chap5__definition_5_6_3"]
def EqLevelInstance {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (j i : Nat) (A : FormulaN L) : Prop :=
  (j = 1 ∧ ∃ t, levelArguments q i [t] ∧ A = .eq_ hL t t) ∨
  (j = 2 ∧ ∃ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
    f ∈ signedSetFunSyms (inputSignedSet q) ∧ 0 < L.funArity f ∧
    levelArguments q i (List.ofFn ss ++ List.ofFn ts) ∧
    A = eqCongruenceImplFunc L hL f ss ts) ∨
  (j = 3 ∧ ∃ (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L),
    P ∈ signedSetPredSyms (inputSignedSet q) ∧
    levelArguments q i (List.ofFn ss ++ List.ofFn ts) ∧
    A = eqCongruenceImplPred L hL P ss ts) ∨
  (j = 3 ∧ ∃ s₁ s₂ t₁ t₂, levelArguments q i [s₁, s₂, t₁, t₂] ∧
    A = eqCongruenceImplEq hL s₁ s₂ t₁ t₂)

/-- Definition 5.6.3: An equality formula with its generalized-rule witness. -/
@[blueprint "chap5__definition_5_6_3"]
def EqEntry (L : Language) :=
  { A : FormulaN L // ∀ hL : L.hasEquality = true, isEqAxiomInstance hL A }

/-- Definition 5.6.3: An equality enumeration has no holes or repeated entries. -/
@[blueprint "chap5__definition_5_6_3"]
structure EqStream (L : Language) where
  entries : Nat → Option (EqEntry L)
  noHoles : ∀ n, entries n = none → entries (n + 1) = none
  some_injective : ∀ n m A, entries n = some A → entries m = some A → n = m

/-- Definition 5.6.3: Admissible initial EQ streams enumerate exactly the
level families for the occurrence language of the possibly infinite input. -/
@[blueprint "chap5__definition_5_6_3"]
structure EqEnumeration {L : Language} (hL : L.hasEquality = true) (q : InfSequentN L) where
  streams : Nat → Nat → EqStream L
  enumerates : ∀ j i A,
    (∃ n e, (streams j i).entries n = some e ∧ e.val = A) ↔ EqLevelInstance hL q j i A

/-- Definition 5.6.3: Append an equality packet after the rightmost antecedent formula. -/
@[blueprint "chap5__definition_5_6_3"]
def appendHeads {L : Language} (s : Sequent L) (heads : List (EqEntry L)) : Sequent L :=
  .mk (s.antecedent ++ heads.map Subtype.val) s.succedent

end LCS.FirstOrder.Equality.Search
end
