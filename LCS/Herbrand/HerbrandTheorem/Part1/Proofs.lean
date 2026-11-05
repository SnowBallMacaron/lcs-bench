import LCS.Herbrand.HerbrandTheorem.Part1

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

helper /-- Every normalized prenex input admits its canonical Skolem allocation. -/
theorem validitySkolemAllocation_exists {L : Language} (Γ : List (FormulaN L))
    (hΓ : HerbrandInputConvention Γ) (hPrenex : ∀ A ∈ Γ, isPrenex A) :
    Nonempty (ValiditySkolemAllocation Γ) :=
  ⟨mkValiditySkolemAllocation Γ hΓ hPrenex⟩



end LCS.Herbrand.HerbrandTheorem

end

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

proof_of functionalFormExample_eq_allocated := by
  -- REPAIR(T7-131): proof pending
  sorry


end LCS.Herbrand.HerbrandTheorem

end

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

namespace Substitution

proof_of applyTerm_unique := by
  funext t
  induction t with
  | var x => exact hVar x
  | const c => exact hConst c
  | func f ts ih =>
    rw [hFunc]
    exact congrArg (Term.func f) (funext ih)


proof_of applySequential_eq_simultaneous := by
  have hRaw : applySequential sigma A xs = applyFormula sigma A := by
    -- REPAIR(T7-97): proof pending
    sorry
  exact ⟨hRaw, hRaw.trans (applyInstance_eq_applyFormula sigma A hA).symm⟩


proof_of applySequential_perm := by
  have hys : ExactSupportEnumeration sigma ys :=
    ⟨hPerm.nodup_iff.mp hxs.1, fun x => hPerm.mem_iff.symm.trans (hxs.2 x)⟩
  exact (applySequential_eq_simultaneous sigma A hA xs hxs hDisjoint).1.trans
    (applySequential_eq_simultaneous sigma A hA ys hys hDisjoint).1.symm


proof_of IsGround.applySequential_eq_simultaneous := Substitution.applySequential_eq_simultaneous sigma A hA xs hxs h.supportImagesDisjoint


proof_of IsGround.applySequential_perm := Substitution.applySequential_perm sigma A hA xs ys hxs hPerm h.supportImagesDisjoint


helper /-- A full existential-prefix assignment with closed images at every prefix
variable is a ground substitution. This covers the complete Herbrand tuples,
including vacuous binders, while leaving all other variables fixed. -/
theorem Substitution.isGround_of_prefixAssignment {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (hPrefix : IsExistentialPrefixAssignment sigma A)
    (hClosed : ∀ x, (QuantifierKind.existential, x) ∈ prenexPrefix A →
      termFV (sigma x) = ∅) : IsGround sigma :=
  ⟨hPrefix.2.1, fun x hx => hClosed x (hPrefix.2.2 x hx)⟩

end Substitution

end LCS.Herbrand.HerbrandTheorem

end
