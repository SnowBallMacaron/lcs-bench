import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import Attach
import LCS.FirstOrder.Completeness.Search.Variables.ProofsStamp

/-! # The variables x₀, x₁, … and y₀, y₁, … (Section 5.5.1)

The set of variables is the disjoint union of the x variables, used to build the
input formulae, and the y variables, an infinite supply of new variables.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables

/-- Definition 5.5.1 (variable convention): The i-th reserved variable yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def yVar {L : Language} (i : Nat) : Term L := .var (2 * i + 1)

/-- Definition 5.5.1 (variable convention): An x-variable has an even index. -/
@[blueprint "chap5__definition_5_5_1"]
def isXIndex (n : Nat) : Prop := n % 2 = 0

-- retained: used by LCS.FirstOrder.Completeness.Search.Part2
/-- Every variable in an even-renamed term has an x index. -/
theorem evenTerm_isXIndex {L : Language} (t : Term L) :
    ∀ n, n ∈ termFV (InfiniteSearch.evenTerm t) → isXIndex n := by
  induction t with
  | var i =>
    intro n hn
    have heq : n = 2 * i := hn
    subst n
    simp [isXIndex]
  | const c => intro n hn; exact False.elim hn
  | func f ts ih =>
    intro n hn
    obtain ⟨i, hi⟩ := hn
    exact ih i n hi

end LCS.FirstOrder.Completeness.Search

namespace LCS.FirstOrder.SyntaxN.FormulaN
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.5.1 (variable convention): Every variable occurring in a
formula, free or bound, is an x variable; this includes vacuous binders. -/
@[blueprint "chap5__definition_5_5_1"]
def builtFromX {L : Language} (A : FormulaN L) : Prop :=
  ∀ n, n ∈ formulaFVN A ∨ n ∈ formulaBVN A → isXIndex n

-- retained: used by LCS.FirstOrder.Completeness.Search.Part2
/-- Even-index renaming produces a formula built entirely from x variables. -/
theorem builtFromX_evenFormula {L : Language} (A : FormulaN L) :
    (InfiniteSearch.evenFormula A).builtFromX := by
  induction A with
  | predN P ts =>
    intro n hn
    rcases hn with ⟨i, hi⟩ | hfalse
    · exact evenTerm_isXIndex (ts i) n hi
    · exact False.elim hfalse
  | eq_ h t u =>
    intro n hn
    rcases hn with (ht | hu) | hfalse
    · exact evenTerm_isXIndex t n ht
    · exact evenTerm_isXIndex u n hu
    · exact False.elim hfalse
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    intro n hn
    rcases hn with (ha | hb) | (ha | hb)
    · exact ihA n (Or.inl ha)
    · exact ihB n (Or.inl hb)
    · exact ihA n (Or.inr ha)
    · exact ihB n (Or.inr hb)
  | all x A ih | ex x A ih =>
    intro n hn
    rcases hn with ⟨ha, _⟩ | (ha | hx)
    · exact ih n (Or.inl ha)
    · exact ih n (Or.inr ha)
    · have heq : n = 2 * x := hx
      subst n
      simp [isXIndex]

end LCS.FirstOrder.SyntaxN.FormulaN

namespace LCS.FirstOrder.Gentzen.InfSequentN
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN

/-- Definition 5.5.1 (input convention): Every formula on either side of
a possibly infinite input sequent is built entirely from x variables. -/
@[blueprint "chap5__definition_5_5_1"]
def builtFromX {L : Language} (q : InfSequentN L) : Prop :=
  ∀ A, q.memAntecedent A ∨ q.memSuccedent A → A.builtFromX

end LCS.FirstOrder.Gentzen.InfSequentN
end
