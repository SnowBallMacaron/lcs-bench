import LCS.FirstOrder.Semantics

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Semantics

proof_of captureExample_5_2_5_not_satisfied := by
  unfold Syntax.Substitution.captureExample_5_2_5_after
  rw [Syntax.Substitution.captureExample_5_2_5_after_eq]
  intro ⟨a, ha⟩
  apply hIrrefl a
  simpa [formulaEval, termEval, assignUpdate] using ha


proof_of captureExample_5_2_5_satisfiable := by
  refine ⟨(0 : Nat), ?_⟩
  change (0 : Nat) < 1
  decide


proof_of peanoNatStructure_isModel := peanoAP_validIn


proof_of peanoSuccNonZero_not_validIn_subsingleton := by
  intro h
  obtain ⟨a⟩ := M.carrierNonempty
  exact h (fun _ => a) a (Subsingleton.elim _ _)


proof_of peanoAP_not_validSet := by
  let M : Structure peanoLanguage :=
    { carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun p => Empty.elim p }
  intro h
  have hM : validIn M peanoSuccNonZero :=
    h M peanoSuccNonZero (Or.inl (by simp [peanoAxioms]))
  exact peanoSuccNonZero_not_validIn_subsingleton M hM


end LCS.FirstOrder.Semantics
