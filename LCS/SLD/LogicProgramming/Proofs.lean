import LCS.SLD.LogicProgramming

namespace LCS.SLD.LogicProgramming

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.SLD.FirstOrder

namespace HerbrandStructure

proof_of funcInterp := by
  -- BEGIN PROOF
    refine ⟨⟨Term.func f (fun i => (ts i).val), ?_⟩, rfl⟩
    show termFV (Term.func f (fun i => (ts i).val)) = ∅
    unfold termFV
    funext x
    show (∃ i, termFV ((ts i).val) x) = False
    apply propext
    constructor
    · intro ⟨j, hj⟩
      have hcl := (ts j).property
      rw [Term.isClosed] at hcl
      have : (termFV (ts j).val) = (fun _ => False) := hcl
      rw [this] at hj
      exact hj
    · exact False.elim


proof_of constInterp := by
  -- BEGIN PROOF
    exact ⟨⟨Term.const c, by simp [Term.isClosed, termFV]⟩, rfl⟩


end HerbrandStructure

proof_of evalTermInHerbrandRaw_closed := by
  -- BEGIN PROOF
    induction t with
    | var v => exact (assign v).property
    | const c => show termFV (Term.const c) = (∅ : Set Nat); rfl
    | func f args ih =>
      show termFV (Term.func f (fun i => evalTermInHerbrandRaw assign (args i))) = (∅ : Set Nat)
      unfold termFV
      funext x
      show (∃ i, termFV (evalTermInHerbrandRaw assign (args i)) x) = False
      apply propext
      constructor
      · intro ⟨j, hj⟩
        have hcl : termFV (evalTermInHerbrandRaw assign (args j)) = (∅ : Set Nat) := ih j
        have : (∅ : Set Nat) x := hcl ▸ hj
        exact this
      · exact False.elim


proof_of closedFunc_arg := by
  -- BEGIN PROOF
    show termFV (args i) = (∅ : Set Nat)
    have hcl' : termFV (Term.func f args) = (∅ : Set Nat) := hcl
    funext x
    apply propext
    constructor
    · intro hx
      have : (termFV (Term.func f args)) x := by
        show (Set.iUnion (fun j => termFV (args j))) x
        exact ⟨i, hx⟩
      rw [hcl'] at this
      exact this
    · exact False.elim
















helper /-- Helper: Formula evaluation agrees on two assignments that agree on
    free variables of the formula. -/
theorem formulaEval_agree_on_fv {L : Language} (M : Structure L)
    (s1 s2 : Assignment M) (A : FormulaN L)
    (h : ∀ v, formulaFVN A v → s1 v = s2 v) :
    formulaEvalN M A s1 ↔ formulaEvalN M A s2 :=
-- BEGIN PROOF
  coincidenceLemmaN M A s1 s2 (fun v hv => h v hv)

helper theorem formulaEval_closed_agree {L : Language} (M : Structure L)
    (s1 s2 : Assignment M) (A : FormulaN L) (hcl : FormulaN.isClosed A) :
    formulaEvalN M A s1 ↔ formulaEvalN M A s2 := by
-- BEGIN PROOF
  apply formulaEval_agree_on_fv
  intro v hv; exfalso
  rw [FormulaN.isClosed] at hcl
  have : (∅ : Set Nat) v := hcl ▸ hv
  exact this











proof_of herbrand_satisfiability := by
  -- BEGIN PROOF
    constructor
    · -- Forward: given model A and assignment s with A |= X[s],
      -- construct the Herbrand structure H from A and show H |= X.
      intro ⟨A, s_A, hsat⟩
      -- Pick any assignment s : Nat → GroundTerm L
      let gt0 : GroundTerm L := herbDefaultGT hConst
      let s : Nat → GroundTerm L := fun _ => gt0
      refine ⟨herbrandStructureFromModel (hNoEq := hNoEq) A hConst, s, ?_⟩
      apply herbrand_model_transfer (hNoEq := hNoEq) A hConst s X hNNF hUniv hNoEqF
      -- Need: formulaEvalN A (fun v => herbrandHom A (s v)) X
      -- Since X is a sentence (closed), the assignment doesn't matter.
      -- We have hsat : formulaEvalN A s_A X.
      exact (formulaEval_closed_agree A s_A _ X _hSentence).mp hsat
    · -- Backward: a Herbrand structure H is an L-structure, so
      -- satisfiability in H implies satisfiability in some structure.
      intro ⟨H, s, hsat⟩
      exact ⟨herbrandToStructure H, s,
        (herbrandToStructure_formulaEval H s X).mpr hsat⟩


proof_of exIndAnswer_valid := by
  -- BEGIN PROOF
    intro H hDisj
    cases hDisj with
    | inl hNotA => exact ⟨groundConst_a, hNotA⟩
    | inr hNotB => exact ⟨groundConst_b, hNotB⟩


helper def herbrandExceptB : HerbrandStructure exIndAnswerLang rfl where
  predInterp := fun _ args =>
    match args with
    | [gt] => gt.val ≠ Term.const ExIndAnswerConst.b
    | _ => True
  hasConstant := ⟨ExIndAnswerConst.a⟩

helper def herbrandExceptA : HerbrandStructure exIndAnswerLang rfl where
  predInterp := fun _ args =>
    match args with
    | [gt] => gt.val ≠ Term.const ExIndAnswerConst.a
    | _ => True
  hasConstant := ⟨ExIndAnswerConst.a⟩

proof_of exIndAnswer_noSingleWitness := by
  intro t
  let s : Nat → GroundTerm exIndAnswerLang := fun _ => groundConst_a
  by_cases ht : (evalTermInHerbrand s t).val = Term.const ExIndAnswerConst.b
  · refine ⟨herbrandExceptA, s, Or.inl ?_, ?_⟩
    · simp [HerbrandStructure.predInterp, herbrandExceptA, groundConst_a]
    · change (evalTermInHerbrand s t).val ≠ Term.const ExIndAnswerConst.a
      rw [ht]
      intro h; cases h
  · refine ⟨herbrandExceptB, s, Or.inr ?_, ?_⟩
    · simp [HerbrandStructure.predInterp, herbrandExceptB, groundConst_b]
    · exact ht

proof_of definiteAnswerLemma := by
  -- REPAIR(T9-21): proof pending — empty-conjunction extension
  sorry

end LCS.SLD.LogicProgramming
