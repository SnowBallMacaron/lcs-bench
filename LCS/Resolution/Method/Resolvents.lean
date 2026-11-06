import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.Resolvents.ProofsStamp

/-! # Resolvents and the resolution process (Section 4.3.2, Lemma 4.3.1 to Example 4.3.3)

Lemma 4.3.1, resolution steps on clause sets, resolvents (Definition 4.3.2),
satisfaction of clauses and clause sets, and Example 4.3.3.
-/
section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace Clause

/-- Definition 4.3.2 (companion def): The conjugate of a literal, re-exported
    in the resolution namespace. -/
@[blueprint "chap4__definition_4_3_2"]
def conjugate : Literal → Literal :=
  Literal.conjugate

/-- Definition 4.3.2 (companion def): Remove all occurrences of a literal
    from a clause. -/
@[blueprint "chap4__definition_4_3_2"]
def remove (C : Clause) (L : Literal) : Clause :=
  GCNF.Clause.remove C L

/-- Definition 4.3.2: A clause C is a resolvent of C1 and C2 iff for some
    literal L in C1 with conjugate in C2, C = (C1 \ {L}) ∪ (C2 \ {~L}). -/
@[blueprint "chap4__definition_4_3_2" (main := true)]
def isResolvent (C C1 C2 : Clause) : Prop :=
  ∃ L : Literal, L ∈ C1 ∧ (Literal.conjugate L) ∈ C2 ∧
    C = GCNF.Clause.union (Clause.remove C1 L) (Clause.remove C2 (Literal.conjugate L))

/-- Definition 4.3.3 (companion def): The empty clause, containing no literals.
    A set of clauses containing the empty clause is unsatisfiable. -/
@[blueprint "chap4__definition_4_3_3"]
def empty : Clause := GCNF.Clause.empty

/-- Lemma 4.3.1 (companion def): A valuation satisfies a clause iff it
    satisfies at least one literal in the clause. -/
@[blueprint "chap4__lemma_4_3_1"]
def satisfies (v : Nat → Bool) (C : Clause) : Prop :=
  ∃ L ∈ C, Literal.satisfiedBy L v

end Clause
namespace ClauseSet

/-- Definition 4.3.2 (companion def): A valuation satisfies a set of clauses iff
    it satisfies every clause in the set. -/
@[blueprint "chap4__definition_4_3_2"]
def satisfies (v : Nat → Bool) (S : ClauseSequent) : Prop :=
  ∀ C ∈ S, Clause.satisfies v C

/-- Definition 4.3.2 (companion def): A set of clauses is unsatisfiable iff no
    valuation satisfies all clauses in the set. -/
@[blueprint "chap4__definition_4_3_2"]
def isUnsatisfiable (S : ClauseSequent) : Prop :=
  ¬ ∃ v : Nat → Bool, ClauseSet.satisfies v S

end ClauseSet
end LCS.Resolution.Method
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

/-- Example 4.3.3: Under the contextually distinct-atom reading, the two
    displayed clauses have exactly the two displayed resolvents. A and B
    range over arbitrary atom identities, not a fixed chosen pair. -/
@[blueprint "chap4__example_4_3_3" (main := true)]
theorem exampleTwoResolvents (A B : Nat) (hAB : A ≠ B) (C : Clause) :
    Clause.isResolvent C
      (GCNF.Clause.ofList [.pos A, .pos B])
      (GCNF.Clause.ofList [.neg A, .neg B]) ↔
    C = GCNF.Clause.ofList [.pos A, .neg A] ∨
      C = GCNF.Clause.ofList [.pos B, .neg B] 

-- ========= Lemma 4.3.1: Resolution Tautology =========

open LCS.Propositional.Syntax LCS.Propositional.Semantics

/-- Proof of Lemma 4.3.1: The displayed equivalence is a tautology for
    arbitrary formulas A and B and propositional symbol P. False represents
    an empty residual disjunction, so these instances are included. -/
@[blueprint "chap4__lemma_4_3_1" (main := true)]
theorem resolutionFormulaTautology (A B : PropFormula) (P : Nat) :
    ∀ v : Valuation,
      evalExt v (.equiv_
        (.conj (.disj A (.var P)) (.disj B (.neg (.var P))))
        (.conj (.conj (.disj A (.var P)) (.disj B (.neg (.var P))))
          (.disj A B))) = .T 

/-- Empty residual disjunctions have exactly the reductions used in
    Lemma 4.3.1, including the both-empty contradiction. -/
@[blueprint "chap4__lemma_4_3_1"]
theorem emptyDisjunctionReductions (A : PropFormula) (P : Nat) (v : Valuation) :
    evalExt v (.disj .fls A) = evalExt v A ∧
    evalExt v (.disj A .fls) = evalExt v A ∧
    evalExt v (.conj
      (.conj (.disj .fls (.var P)) (.disj .fls (.neg (.var P))))
      (.disj .fls .fls)) = evalExt v (.conj (.var P) (.neg (.var P))) 

/-- Complementary unit clauses resolve to the empty clause. -/
@[blueprint "chap4__example_4_3_3"]
theorem complementaryUnitsResolve (L : Literal) :
    Clause.isResolvent GCNF.Clause.empty (GCNF.Clause.single L)
      (GCNF.Clause.single (Literal.conjugate L)) 

/-- A resolution step selects two existing parent clauses and adds exactly
    one resolvent, retaining every original clause. -/
@[blueprint "chap4__definition_4_3_3"]
def resolutionStep (S T : ClauseSequent) : Prop :=
  ∃ C₁ ∈ S, ∃ C₂ ∈ S, ∃ C,
    Clause.isResolvent C C₁ C₂ ∧ T = LCS.Finset.insert C S

/-- A finite sequence of successive resolution steps beginning with S.
    Zero steps are permitted, as needed when S already contains the empty clause. -/
@[blueprint "chap4__definition_4_3_3"]
structure ResolutionProcess (S : ClauseSequent) where
  length : Nat
  stage : Fin (length + 1) → ClauseSequent
  initial : stage ⟨0, Nat.zero_lt_succ length⟩ = S
  successive : ∀ i : Fin length,
    resolutionStep (stage ⟨i.val, by omega⟩) (stage ⟨i.val + 1, by omega⟩)

end LCS.Resolution.Method
end
