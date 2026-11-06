import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FirstOrder.Gentzen.DeductionTrees
import Attach
import LCS.FirstOrder.Gentzen.InfiniteSequents.ProofsStamp

/-! # Possibly infinite sequents (Sections 5.5.1 and 5.5.3)

Sequents whose antecedent and succedent are enumerations of formulae, their
validity and falsifiability, and the free/bound variable convention for them.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

/-- Theorem 5.5.1 (input convention): An empty marker terminates a finite
formula sequence; a sequence with no empty marker is countably infinite. -/
@[blueprint "chap5__definition_5_5_1"]
def NoHolesN {L : Language} (a : Nat → Option (FormulaN L)) : Prop :=
  ∀ n, a n = none → a (n + 1) = none

/-- Theorem 5.5.1 (input): A possibly infinite sequent has two ordered
formula sequences, each finite or countably infinite, with no holes. -/
@[blueprint "chap5__definition_5_5_1"]
structure InfSequentN (L : Language) where
  antecedent : Nat → Option (FormulaN L)
  succedent : Nat → Option (FormulaN L)
  antecedent_noHoles : NoHolesN antecedent
  succedent_noHoles : NoHolesN succedent

/-- Theorem 5.5.1 (input): Embed a finite sequent by terminating each list
with empty markers. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.ofSequent {L : Language} (s : Sequent L) : InfSequentN L where
  antecedent := fun n => s.antecedent[n]?
  succedent := fun n => s.succedent[n]?
  antecedent_noHoles := by
    intro n hn
    have h := List.getElem?_eq_none_iff.mp hn
    exact List.getElem?_eq_none (by omega)
  succedent_noHoles := by
    intro n hn
    have h := List.getElem?_eq_none_iff.mp hn
    exact List.getElem?_eq_none (by omega)

/-- Theorem 5.5.1 (input): Membership in the antecedent means occurrence
at some finite position. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.memAntecedent {L : Language} (q : InfSequentN L) (A : FormulaN L) : Prop :=
  ∃ n, q.antecedent n = some A

/-- Theorem 5.5.1 (input): Membership in the succedent means occurrence
at some finite position. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.memSuccedent {L : Language} (q : InfSequentN L) (A : FormulaN L) : Prop :=
  ∃ n, q.succedent n = some A

/-- Finite embedding preserves antecedent membership. -/
theorem InfSequentN.memAntecedent_ofSequent {L : Language} (s : Sequent L) (A : FormulaN L) :
    (ofSequent s).memAntecedent A ↔ A ∈ s.antecedent := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hn
    exact List.mem_iff_getElem.mpr ⟨n, hlt, heq⟩
  · intro hA
    obtain ⟨n, hlt, heq⟩ := List.mem_iff_getElem.mp hA
    exact ⟨n, List.getElem?_eq_some_iff.mpr ⟨hlt, heq⟩⟩

/-- Finite embedding preserves succedent membership. -/
theorem InfSequentN.memSuccedent_ofSequent {L : Language} (s : Sequent L) (A : FormulaN L) :
    (ofSequent s).memSuccedent A ↔ A ∈ s.succedent := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hn
    exact List.mem_iff_getElem.mpr ⟨n, hlt, heq⟩
  · intro hA
    obtain ⟨n, hlt, heq⟩ := List.mem_iff_getElem.mp hA
    exact ⟨n, List.getElem?_eq_some_iff.mpr ⟨hlt, heq⟩⟩

/-- Theorem 5.5.1, using Definition 3.5.2: Validity means that in every
structure and assignment, truth of every antecedent member implies truth
of some succedent member. -/
@[blueprint "chap5__theorem_5_5_1"]
def infSequentValid {L : Language} (q : InfSequentN L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A, q.memAntecedent A → formulaEvalN M A s) →
    ∃ B, q.memSuccedent B ∧ formulaEvalN M B s

/-- Theorem 5.5.1, using Definition 3.5.2: Falsifiability means that some
structure and assignment satisfy every antecedent member and falsify every
succedent member. -/
@[blueprint "chap5__theorem_5_5_1"]
def infSequentFalsifiable {L : Language} (q : InfSequentN L) : Prop :=
  ∃ (M : Structure L) (s : Assignment M),
    (∀ A, q.memAntecedent A → formulaEvalN M A s) ∧
    (∀ B, q.memSuccedent B → ¬ formulaEvalN M B s)

/-- Theorem 5.5.1 (standing assumption): No variable free in any formula
on either side occurs bound in any formula on either side. -/
@[blueprint "chap5__definition_5_5_1"]
def crossNoFreeBoundInf {L : Language} (q : InfSequentN L) : Prop :=
  ∀ x : Nat,
    (∃ A, (q.memAntecedent A ∨ q.memSuccedent A) ∧ x ∈ formulaFVN A) →
    ∀ B, (q.memAntecedent B ∨ q.memSuccedent B) → x ∉ formulaBVN B

end LCS.FirstOrder.Gentzen
end
