import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import Attach
import LCS.FOResolution.GroundResolution.GroundClauses.ProofsStamp

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
namespace FOLiteral

/-- Lemma 8.3.1 (companion): A first-order literal is satisfied in a
    structure M under assignment s. A positive literal pos B is true
    when B holds; a negative literal neg B is true when B does not
    hold. -/
@[blueprint "chap8__lemma_8_3_1"]
def isSatisfied {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) :
    FOLiteral L hNoEq → Prop
  | .pos B => formulaEvalN M B.toFormula s
  | .neg B => ¬ formulaEvalN M B.toFormula s

end FOLiteral

namespace FOClause

/-- Lemma 8.3.1 (companion): A ground clause (disjunction of literals)
    is satisfied in a structure M under assignment s iff at least one
    of its literals is true. -/
@[blueprint "chap8__lemma_8_3_1"]
def isSatisfied {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (c : FOClause L hNoEq) : Prop :=
  ∃ lit ∈ c, FOLiteral.isSatisfied (hNoEq := hNoEq) M s lit

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Groundness is preserved when every literal of one clause occurs in a
    ground clause. -/
theorem isGround_of_subset {L : Language} (hNoEq : L.withoutEquality)
    {source target : FOClause L hNoEq}
    (hGround : source.isGround hNoEq)
    (hSubset : ∀ lit, lit ∈ target → lit ∈ source) :
    target.isGround hNoEq := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    have : source.vars hNoEq x := ⟨lit, hSubset lit hLit, hVar⟩
    dsimp only [FOClause.vars] at this
    rw [hGround] at this
    exact this
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Appending ground clauses preserves groundness. -/
theorem isGround_append {L : Language} (hNoEq : L.withoutEquality)
    {left right : FOClause L hNoEq}
    (hLeft : left.isGround hNoEq)
    (hRight : right.isGround hNoEq) :
    (left ++ right).isGround hNoEq := by
  apply isGround_of_subset (hNoEq := hNoEq) (source := left ++ right)
      (target := left ++ right)
  · ext x
    constructor
    · intro ⟨lit, hLit, hVar⟩
      rw [List.mem_append] at hLit
      rcases hLit with hLit | hLit
      · have : left.vars hNoEq x := ⟨lit, hLit, hVar⟩
        dsimp only [FOClause.vars] at this
        rw [hLeft] at this
        exact this
      · have : right.vars hNoEq x := ⟨lit, hLit, hVar⟩
        dsimp only [FOClause.vars] at this
        rw [hRight] at this
        exact this
    · intro h
      exact h.elim
  · exact fun _ h => h

end FOClause

namespace GroundClauseSet

/-- Lemma 8.3.1 (companion): A set of ground clauses is unsatisfiable
    iff no interpretation satisfies all clauses simultaneously. Adapts
    the unsatisfiability concept from propositional resolution to the
    first-order ground setting. A ground clause (a disjunction of
    ground literals) is viewed as a formula; the set is unsatisfiable
    when the conjunction of all clause-formulae is unsatisfiable. -/
@[blueprint "chap8__lemma_8_3_1"]
def isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOClause L hNoEq)) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    ∃ c ∈ S, ¬ FOClause.isSatisfied (hNoEq := hNoEq) M s c

end GroundClauseSet

/-- Lemma 8.3.1 (companion): A ground substitution maps variable
    indices to ground terms (terms with no variables). -/
@[blueprint "chap8__lemma_8_3_1"]
structure GroundSubstitution (L : Language) where
  /-- The term substituted for each variable. -/
  toSubst : Nat → Term L
  /-- Every substituted term is closed. -/
  termsGround : ∀ n, termVars (toSubst n) = Set.empty

end LCS.FOResolution.GroundResolution
end
