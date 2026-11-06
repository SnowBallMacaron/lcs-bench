import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.CompletenessTheorem
import Attach
import LCS.FirstOrder.Equality.Search.ModelExistence.ProofsStamp

section
namespace LCS.FirstOrder.Equality.MetaTheorems
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen

/-- Theorem 5.6.4 (companion): A set Gamma is G_=-consistent when some
normalized formula is unprovable from every finite list of members of Gamma. -/
@[blueprint "chap5__theorem_5_6_4"]
def isConsistentSetEq {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L)) : Prop :=
  ∃ B : FormulaN L, ∀ cs : List (FormulaN L),
    (∀ c ∈ cs, c ∈ Gamma) →
    ¬ sequentProvableEq hL (Sequent.mk cs [B])

end LCS.FirstOrder.Equality.MetaTheorems

end
