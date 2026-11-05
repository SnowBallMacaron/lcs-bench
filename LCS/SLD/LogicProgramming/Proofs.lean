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

namespace AntiHornClause

proof_of negationIsHorn := by
  -- REPAIR(T9-23): proof pending — negation of the existential matrix equals its universal Horn dual
  sorry


end AntiHornClause

namespace LogicProgram

proof_of negQueryIsConjOfHorn := by
  -- REPAIR(T9-23): proof pending — De Morgan equivalence for the same finite query components
  sorry


proof_of outputVarList_nodup := by
  exact LCS.SLD.FirstOrder.list_eraseDups_nodup _

proof_of mem_outputVarList := by
  simp only [outputVarList, List.mem_eraseDups, List.mem_flatMap, outputVars]
  constructor
  · rintro ⟨a, ha, hv⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    refine ⟨i, ?_⟩
    rw [hi]
    exact (a.wellFormed.2 v).mp hv
  · rintro ⟨i, hv⟩
    exact ⟨lp.qry.get i, List.get_mem _ _, ((lp.qry.get i).wellFormed.2 v).mpr hv⟩

end LogicProgram

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

namespace programSemantics
proof_of mem_isDefiniteSemantics := by
  rfl
proof_of definiteAnswer_exists := by
  -- REPAIR(T9-22): proof pending — finite subtheory and definite-answer lemma yield singleton membership
  sorry

end programSemantics


helper /-- Lemma 9.5.2 (Definite answer lemma): If P is a finite set of
    definite clauses and G = exists z_1...exists z_q (B_1 and ... and B_l)
    where each B_i is an atomic formula, and if P entails G (i.e.
    models P supset G), then there exists a q-tuple (t_1,...,t_q) of
    ground terms in the Herbrand universe such that
    models P supset (B_1 and ... and B_l)[t_1/z_1,...,t_q/z_q].
    The proof relies on Lemma 9.5.1 to reduce to Herbrand structures
    and on the intersection property of minimal Herbrand models for
    definite clause sets. -/
-- Helper: evalTermInHerbrand agrees on free variables
theorem evalTermInHerbrand_agree_fv {L : Language}
    (s1 s2 : Nat → GroundTerm L) (t : Term L)
    (h : ∀ v, termFV t v → s1 v = s2 v) :
    evalTermInHerbrand s1 t = evalTermInHerbrand s2 t := by
-- BEGIN PROOF
  apply Subtype.ext; simp [evalTermInHerbrand]
  induction t with
  | var v => exact congrArg Subtype.val (h v rfl)
  | const c => rfl
  | func f args ih =>
    simp [evalTermInHerbrandRaw]; congr 1; funext i
    exact ih i (fun v hv => h v ⟨i, hv⟩)

helper theorem findIndex_mem_some {v : Nat} {l : List Nat} (h : v ∈ l) :
    ∃ i, findIndex l v = some i := by
-- BEGIN PROOF
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    simp only [findIndex]; split
    · exact ⟨0, rfl⟩
    · next hne =>
      have hNe : ¬(x = v) := by simp [BEq.beq] at hne; exact hne
      have : v ∈ xs := by
        cases h with | head => exact absurd rfl hNe | tail _ h => exact h
      obtain ⟨i, hi⟩ := ih this
      exact ⟨i + 1, by simp [hi]⟩

helper theorem atomicEvalTransfer {L : Language} (hNoEq : L.withoutEquality)
    (H1 H2 : HerbrandStructure L hNoEq)
    (s1 s2 : Nat → GroundTerm L)
    (b : FOAtom L hNoEq)
    (hPred : ∀ (p : L.predSymbols) (gts : List (GroundTerm L)),
      H1.predInterp p gts → H2.predInterp p gts)
    (hFV : ∀ v, formulaFVN b.toFormula v → s1 v = s2 v) :
    evalFormulaInHerbrand H1 s1 b.toFormula →
      evalFormulaInHerbrand H2 s2 b.toFormula := by
-- BEGIN PROOF
  cases b with
  | predN p args =>
    simp only [FOAtomCore.toFormula, evalFormulaInHerbrand]
    intro h1
    have hArgsEq : (fun i => evalTermInHerbrand s1 (args i)) =
                   (fun i => evalTermInHerbrand s2 (args i)) :=
      funext fun i => evalTermInHerbrand_agree_fv s1 s2 (args i)
        (fun v hv => hFV v ⟨i, hv⟩)
    rw [show List.ofFn (fun i => evalTermInHerbrand s2 (args i)) =
           List.ofFn (fun i => evalTermInHerbrand s1 (args i)) from
        congrArg List.ofFn hArgsEq.symm]
    exact hPred p _ h1
  | eq_ _ t1 t2 =>
    simp only [FOAtomCore.toFormula, evalFormulaInHerbrand]
    intro h1
    rw [← evalTermInHerbrand_agree_fv s1 s2 t1 (fun v hv => hFV v (Or.inl hv)),
        ← evalTermInHerbrand_agree_fv s1 s2 t2 (fun v hv => hFV v (Or.inr hv))]
    exact h1

proof_of definiteAnswerLemma := by
  -- REPAIR(T9-21): proof pending — empty-conjunction extension
  sorry

proof_of exHanoiProgram_moveRelation := by
  -- REPAIR(T9-53): proof pending — the five clauses hold in the recursive Hanoi move interpretation
  sorry

end LCS.SLD.LogicProgramming
