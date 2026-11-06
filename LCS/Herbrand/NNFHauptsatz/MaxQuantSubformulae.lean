import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.MaxQuantSubformulae.ProofsStamp

/-! # Herbrand.NNFHauptsatz.MaxQuantSubformulae

Definition 7.4.1: the maximal quantified subformulae QF(A) of an NNF formula,
as exact occurrences and as a set, with Example 7.4.2.
-/

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- Definition 7.4.1 (required helper): singleton-`Set` constructor used to build the mathematical set QF(A) of maximal quantified subformulae in `maxQuantSubformulae`. Sequent containers in G2nnf use `LCS.Finset` instead (Definition 7.4.3). -/
@[blueprint "chap7__definition_7_4_1"]
def sng {L : Language} (A : FormulaN L) : Set (FormulaN L) := fun x => x = A

-- ===================================================================
-- Occurrence-sensitive maximal quantified subformula infrastructure
-- ===================================================================

/-- One branch step in the address of a maximal quantified occurrence.
Unlike formula equality, an address distinguishes the two copies in `Q ∧ Q`
or `Q ∨ Q`. -/
@[blueprint "chap7__definition_7_4_1"]
inductive MaxQuantifierOccurrenceStep : Type where
  | left
  | right
  deriving DecidableEq

/-- A branch address through conjunctions and disjunctions. -/
@[blueprint "chap7__definition_7_4_1"]
abbrev MaxQuantifierOccurrenceAddress :=
  List MaxQuantifierOccurrenceStep

/-- A proof-relevant path to one maximal quantified occurrence of `A`.
The path stops as soon as it reaches `∀` or `∃`; consequently it cannot select
a quantifier nested below another quantifier.  The four branch constructors
retain occurrence identity even when the selected formula has the same syntax
in both branches. -/
@[blueprint "chap7__definition_7_4_1"]
inductive MaxQuantifierOccurrence {L : Language} :
    FormulaN L → Type where
  | all (x : Nat) (B : FormulaN L) :
      MaxQuantifierOccurrence (.all x B)
  | ex (x : Nat) (B : FormulaN L) :
      MaxQuantifierOccurrence (.ex x B)
  | conjLeft {A : FormulaN L}
      (occurrence : MaxQuantifierOccurrence A) (B : FormulaN L) :
      MaxQuantifierOccurrence (.conj A B)
  | conjRight (A : FormulaN L) {B : FormulaN L}
      (occurrence : MaxQuantifierOccurrence B) :
      MaxQuantifierOccurrence (.conj A B)
  | disjLeft {A : FormulaN L}
      (occurrence : MaxQuantifierOccurrence A) (B : FormulaN L) :
      MaxQuantifierOccurrence (.disj A B)
  | disjRight (A : FormulaN L) {B : FormulaN L}
      (occurrence : MaxQuantifierOccurrence B) :
      MaxQuantifierOccurrence (.disj A B)

namespace MaxQuantifierOccurrence

/-- The maximal quantified formula selected by an occurrence path. -/
@[blueprint "chap7__definition_7_4_1"]
def selected {L : Language} {A : FormulaN L} :
    MaxQuantifierOccurrence A → FormulaN L
  | .all x B => .all x B
  | .ex x B => .ex x B
  | .conjLeft occurrence _ => occurrence.selected
  | .conjRight _ occurrence => occurrence.selected
  | .disjLeft occurrence _ => occurrence.selected
  | .disjRight _ occurrence => occurrence.selected

/-- The left/right address encoded by an occurrence path. -/
@[blueprint "chap7__definition_7_4_1"]
def address {L : Language} {A : FormulaN L} :
    MaxQuantifierOccurrence A → MaxQuantifierOccurrenceAddress
  | .all _ _ => []
  | .ex _ _ => []
  | .conjLeft occurrence _ => .left :: occurrence.address
  | .conjRight _ occurrence => .right :: occurrence.address
  | .disjLeft occurrence _ => .left :: occurrence.address
  | .disjRight _ occurrence => .right :: occurrence.address

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Look up a formula at a branch address.  Maximal-quantifier addresses never
descend through a quantifier, so only conjunction and disjunction steps are
accepted. -/
def lookup {L : Language} :
    FormulaN L → MaxQuantifierOccurrenceAddress → Option (FormulaN L)
  | A, [] => some A
  | .conj A _, .left :: rest => lookup A rest
  | .conj _ B, .right :: rest => lookup B rest
  | .disj A _, .left :: rest => lookup A rest
  | .disj _ B, .right :: rest => lookup B rest
  | _, _ => none

end MaxQuantifierOccurrence

/-- General QF recursion for both ordinary and equality consumers. Conjunction
and disjunction descend through their children; a quantifier returns its whole
formula as a singleton. Atoms, negations and implications return the empty set.
The function is total, including on formulae outside NNF. -/
@[blueprint "chap7__definition_7_4_4"]
def maxQuantSubformulaeCore {L : Language} : FormulaN L → Set (FormulaN L)
  | .predN _ _       => ∅
  | .eq_ _ _ _       => ∅
  | .neg _           => ∅
  | .disj A B        => maxQuantSubformulaeCore A ∪ maxQuantSubformulaeCore B
  | .conj A B        => maxQuantSubformulaeCore A ∪ maxQuantSubformulaeCore B
  | .all x B         => sng (FormulaN.all x B)
  | .ex x B          => sng (FormulaN.ex x B)
  | .impl _ _        => ∅

/-- Definition 7.4.1: In an equality-free language, QF(A) for a formula A in
NNF is empty for literals, a union for conjunction/disjunction, and the singleton
of A for either quantifier. The totalized operation preserves these five clauses
on the source domain; it does not descend into quantified bodies. -/
@[blueprint "chap7__definition_7_4_1" (main := true)]
def maxQuantSubformulae {L : Language} (_hL : L.withoutEquality)
    (A : FormulaN L) : Set (FormulaN L) := maxQuantSubformulaeCore A

namespace MaxQuantifierOccurrence

/-- The formula selected by an occurrence path belongs to the set-valued
`QF(A)` API. -/
theorem selected_mem {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    Membership.mem (maxQuantSubformulaeCore A) occurrence.selected := by
  induction occurrence with
  | all _ _ => rfl
  | ex _ _ => rfl
  | conjLeft _ _ ih => exact Or.inl ih
  | conjRight _ _ ih => exact Or.inr ih
  | disjLeft _ _ ih => exact Or.inl ih
  | disjRight _ _ ih => exact Or.inr ih

end MaxQuantifierOccurrence

/-- Example 7.4.2 (companion type): Constant symbols for the QF
computation example. The constant b is needed for the formula Q(b). -/
@[blueprint "chap7__example_7_4_2"]
inductive QFExConst : Type where
  | b : QFExConst

-- ===================================================================
-- Example 7.4.2 (companion def): qfExLang
-- ===================================================================

/-- Example 7.4.2 (companion def): Language for the QF computation example with predicates P (unary), Q (unary), R (binary), one constant b, no function symbols, and no equality. -/
@[blueprint "chap7__example_7_4_2"]
def qfExLang : Language where
  hasEquality := false
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := QFExConst
  predSymbols := NnfExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 2

-- ===================================================================
-- Example 7.4.2 (companion def): qfExVec1
-- ===================================================================

/-- Example 7.4.2 (companion def): Build a Fin 1 -> Term from a single
variable index in the qfExLang. -/
@[blueprint "chap7__example_7_4_2"]
def qfExVec1 (n : Nat) : Fin 1 → Term qfExLang
  | ⟨0, _⟩ => .var n

-- ===================================================================
-- Example 7.4.2 (companion def): qfExVec2
-- ===================================================================

/-- Example 7.4.2 (companion def): Build a Fin 2 -> Term from two variable
indices in the qfExLang. -/
@[blueprint "chap7__example_7_4_2"]
def qfExVec2 (n m : Nat) : Fin 2 → Term qfExLang
  | ⟨0, _⟩ => .var n
  | ⟨1, _⟩ => .var m

-- ===================================================================
-- Example 7.4.2: qfExFormula
-- ===================================================================

/-- Example 7.4.2: The NNF formula A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))) or exists z P(z). Variables: u = 0, x = 1, y = 2, z = 3. Constant b from QFExConst. -/
@[blueprint "chap7__example_7_4_2"]
def qfExFormula : FormulaN qfExLang :=
  FormulaN.disj
    (FormulaN.disj
      (FormulaN.all 0 (FormulaN.predN .P (qfExVec1 0)))
      (FormulaN.conj
        (FormulaN.predN .Q (fun _ => Term.const QFExConst.b))
        (FormulaN.all 1
          (FormulaN.disj
            (FormulaN.neg (FormulaN.predN .P (qfExVec1 1)))
            (FormulaN.all 2 (FormulaN.predN .R (qfExVec2 1 2)))))))
    (FormulaN.ex 3 (FormulaN.predN .P (qfExVec1 3)))

-- ===================================================================
-- Example 7.4.2 (companion theorem): qfExResult
-- ===================================================================

/-- Example 7.4.2 (companion theorem): The computation QF(A) = {forall u P(u), forall x(not P(x) or forall y R(x,y)), exists z P(z)}, verifying the textbook's claimed result for the formula A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))) or exists z P(z). -/
@[blueprint "chap7__example_7_4_2" (main := true)]
theorem qfExResult :
    maxQuantSubformulae (by rfl) qfExFormula =
      sng (FormulaN.all 0
            (FormulaN.predN NnfExPred.P (qfExVec1 0))) ∪
      (∅ ∪ sng (FormulaN.all 1
        (FormulaN.disj
          (FormulaN.neg (FormulaN.predN NnfExPred.P (qfExVec1 1)))
          (FormulaN.all 2
            (FormulaN.predN NnfExPred.R
              (qfExVec2 1 2)))))) ∪
      sng (FormulaN.ex 3
            (FormulaN.predN NnfExPred.P (qfExVec1 3))) 

-- ===================================================================
-- Example 7.4.2 (companion theorem): qfExNonMaximal
-- ===================================================================

/-- Example 7.4.2 (companion theorem): The formula forall y R(x, y) is NOT in QF(A) because it is nested inside the larger quantified formula forall x(not P(x) or forall y R(x, y)), which is itself a maximal quantified subformula. This demonstrates the maximality exclusion principle. -/
@[blueprint "chap7__example_7_4_2" (main := true)]
theorem qfExNonMaximal :
    ¬ Membership.mem
      (maxQuantSubformulae (by rfl) qfExFormula)
      (FormulaN.all 2
        (FormulaN.predN NnfExPred.R (qfExVec2 1 2))) 
end LCS.Herbrand.NNFHauptsatz
end
