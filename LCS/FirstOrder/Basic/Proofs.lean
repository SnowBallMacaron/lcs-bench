import LCS.FirstOrder.Basic

namespace LCS.FirstOrder.Basic





proof_of forallM_iff_constTrue := by
  constructor
  · intro h
    funext a
    exact propext ⟨fun _ => trivial, fun _ => h a⟩
  · intro h a
    exact Eq.mp (congrFun h a).symm trivial


proof_of not_existsM_iff_constFalse := by
  constructor
  · intro h
    funext a
    exact propext ⟨fun ha => h ⟨a, ha⟩, False.elim⟩
  · intro h ⟨a, ha⟩
    exact Eq.mp (congrFun h a) ha


proof_of namingConstEval := by
  -- BEGIN PROOF
    simp [namingConst, termEval, extendedInterp]


end LCS.FirstOrder.Basic
