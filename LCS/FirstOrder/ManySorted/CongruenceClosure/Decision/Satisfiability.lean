import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Satisfiability.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

/-- Lemma 10.6.1 (companion): A many-sorted formula `A` is satisfiable
iff some structure `M` and assignment `v` make it true,
`A_M[v] = T`. Grounded on the §10.3 formula meaning `msFormulaEval`.
`noncomputable` because `msFormulaEval` is. -/
@[blueprint "chap10__lemma_10_6_1"]
noncomputable def msSatisfiable {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∃ (M : MSStructure L) (v : MSAssignment M), msFormulaEval M A v = BoolVal.T

/-- Lemma 10.6.1 (companion): A many-sorted formula `A` is valid iff
`A_M[v] = T` in every structure under every assignment — the validity
the decision procedure aims to decide. -/
@[blueprint "chap10__lemma_10_6_1"]
noncomputable def msValid {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∀ (M : MSStructure L) (v : MSAssignment M), msFormulaEval M A v = BoolVal.T

/-- Lemma 10.6.1 (companion): A many-sorted formula `A` is unsatisfiable
iff no structure/assignment makes it true — the property the algorithm
decides. -/
@[blueprint "chap10__lemma_10_6_1"]
noncomputable def msUnsatisfiable {L : MSLanguage} (A : MSFormula L) : Prop :=
  ¬ msSatisfiable A

/-- Lemma 10.6.2 (companion): The semantic entailment `Γ ⊨ A`: every
structure/assignment satisfying all of `Γ` satisfies `A`. The basis for
the semantic-equality relation `R_s`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def msEntails {L : MSLanguage} (Γ : Set (MSFormula L))
    (A : MSFormula L) : Prop :=
  ∀ (M : MSStructure L) (v : MSAssignment M),
    (∀ B, Γ B → msFormulaEval M B v = BoolVal.T) →
      msFormulaEval M A v = BoolVal.T

/-- Lemma 10.6.2 (companion): `M ⊨ A[v]`: the formula `A` is true in
structure `M` under assignment `v` (the satisfaction relation used to
state "M is a model of C"). -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def msModels {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) (A : MSFormula L) : Prop :=
  msFormulaEval M A v = BoolVal.T

/-- §10.3.3 (via §5.3.3): A formula is satisfiable in a fixed structure when one full assignment satisfies it. -/
noncomputable def msSatisfiableIn {L : MSLanguage} (M : MSStructure L) (A : MSFormula L) : Prop :=
  ∃ v : MSAssignment M, msModels M v A

/-- §10.3.3 (via §5.3.3): Validity in a fixed structure, also called modelhood of a formula. -/
noncomputable def msValidIn {L : MSLanguage} (M : MSStructure L) (A : MSFormula L) : Prop :=
  ∀ v : MSAssignment M, msModels M v A

/-- §10.3.3 (via §5.3.3): Satisfaction of a set with one shared assignment. -/
noncomputable def msSetSatisfiedAt {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) (T : Set (MSFormula L)) : Prop :=
  ∀ A, T A → msModels M v A

/-- §10.3.3 (via §5.3.3): Satisfiability of an arbitrary set with one structure and one shared assignment. -/
noncomputable def msSetSatisfiable {L : MSLanguage} (T : Set (MSFormula L)) : Prop :=
  ∃ (M : MSStructure L) (v : MSAssignment M), msSetSatisfiedAt M v T

/-- §10.3.3 (via §5.3.3): A model of a set satisfies every member under every full assignment. -/
noncomputable def msSetModel {L : MSLanguage} (M : MSStructure L) (T : Set (MSFormula L)) : Prop :=
  ∀ v : MSAssignment M, msSetSatisfiedAt M v T

/-- §10.3.3 (via §5.3.3): Universal validity of an arbitrary set of formulae. -/
noncomputable def msSetValid {L : MSLanguage} (T : Set (MSFormula L)) : Prop :=
  ∀ M : MSStructure L, msSetModel M T

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
