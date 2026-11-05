import LCS.SLD.LogicProgramming.Completeness

namespace LCS.SLD.LogicProgramming.Completeness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.SLD.FirstOrder

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.Method.Soundness

open LCS.SLD.LogicProgramming

open LCS.SLD.LogicProgramming.Correctness

proof_of groundTermSubstInvariant := by
  -- BEGIN PROOF
    obtain ⟨tv, hcl⟩ := t
    -- Proof by structural induction on the term tv.
    -- Ground terms have no variables, so substitution acts as identity.
    induction tv with
    | var x =>
      -- A ground term cannot be a variable: termFV (var x) = {x} != empty
      exfalso
      have hx : (termFV (L := L) (Term.var x)) x := rfl
      rw [Term.isClosed] at hcl
      rw [hcl] at hx
      exact hx
    | const c =>
      -- termSubstAll (.const c) sigma = .const c by definition
      simp [termSubstAll]
    | func f args ih =>
      -- termSubstAll (.func f args) sigma = .func f (fun i => termSubstAll (args i) sigma)
      -- By induction, each termSubstAll (args i) sigma = args i (since args i is ground).
      simp [termSubstAll]
      funext i
      apply ih i
      -- Each arg is closed because the parent func term is closed.
      rw [Term.isClosed]
      have hcl' : termFV (Term.func f args) = (∅ : Set Nat) := hcl
      unfold termFV at hcl'
      funext x
      apply propext
      constructor
      · intro hx
        have hmem : (Set.iUnion fun j => termFV (args j)) x := ⟨i, hx⟩
        rw [show (Set.iUnion fun j => termFV (args j)) = (∅ : Set Nat) from hcl'] at hmem
        exact hmem
      · exact False.elim


proof_of unsatisfiableGroundInstance := by
  -- BEGIN PROOF
    -- Proof by contradiction: suppose some Structure M satisfies all
    -- universal closures of clause translations in P ++ [negGoalClause].
    -- We construct a Herbrand structure H from M and show both prog and
    -- negGoalClause are satisfied in H, contradicting hEntails.
    simp only [FOHornClauseSet.isUnsatisfiable, FOClauseSet.isUnsatisfiable]
    intro ⟨M, hSat⟩
    let H := herbrandStructureFromModel (hNoEq := hNoEq) M hConst
    let assign : Nat → GroundTerm L := fun _ => herbDefaultGT hConst
    -- Step 1: Transfer each clause formula from M to H.
    -- resolvent_subtree_pw strips universal quantifiers, then
    -- herbrand_model_transfer moves from M to the Herbrand structure.
    have transfer : ∀ (assign : Nat → GroundTerm L), ∀ c ∈ P ++ [negGoalClause],
        evalFormulaInHerbrand H assign ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))) := by
      intro assign c hc
      have ⟨hNNF, hUniv, hFormulaNoEq⟩ := hClauseWF c hc
      exact herbrand_model_transfer (hNoEq := hNoEq) M hConst assign
        ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))) hNNF hUniv hFormulaNoEq
        ((resolvent_subtree_pw (hNoEq := hNoEq)) M Afalsum (c.toFOClause (hNoEq := hNoEq))
          (fun fvs _ => FOClause.universalClosure_of_validIn hNoEq M _
            (hSat _ ⟨c, hc, rfl⟩) Afalsum fvs)
          (fun v => herbrandHom M (assign v)))
    -- Step 2: Bridge clauseToFormula evaluation to evalInHerbrand.
    -- Use clauseToFormula_exists_of_true (via herbrandToStructure) to
    -- extract a witnessing literal, then case-split on clause type.
    have clauseToEval : ∀ (assign : Nat → GroundTerm L), ∀ c ∈ P ++ [negGoalClause],
        evalFormulaInHerbrand H assign ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))) →
        (FOHornClause.evalInHerbrand (hNoEq := hNoEq)) H c assign := by
      intro assign c _ hCF
      obtain ⟨lit, hMem, hLitEval⟩ :=
        (clauseToFormula_exists_of_true (hNoEq := hNoEq)) (herbrandToStructure H) assign Afalsum (c.toFOClause (hNoEq := hNoEq))
          ((herbrandToStructure_formulaEval H assign _).mpr hCF)
      match c, hMem with
      | FOHornClauseCore.fact head, hMem' =>
        simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_singleton] at hMem'; subst hMem'
        simp only [clauseToFormula.litToFormula] at hLitEval
        simp only [FOHornClause.evalInHerbrand]
        exact (herbrandToStructure_formulaEval H assign head).mp hLitEval
      | FOHornClauseCore.rule head body, hMem' =>
        simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause] at hMem'
        simp only [FOHornClause.evalInHerbrand]; intro hBody
        rw [List.mem_append] at hMem'
        cases hMem' with
        | inl hNeg =>
          rw [List.mem_map] at hNeg; obtain ⟨b, hbMem, rfl⟩ := hNeg
          simp only [clauseToFormula.litToFormula, formulaEvalN] at hLitEval
          exact absurd
            ((herbrandToStructure_formulaEval H assign b).mpr (hBody b ((LCS.Finset.mem_toList body b).mp hbMem)))
            hLitEval
        | inr hPos =>
          rw [List.mem_singleton] at hPos; subst hPos
          exact (herbrandToStructure_formulaEval H assign head).mp
            (by simp only [clauseToFormula.litToFormula] at hLitEval; exact hLitEval)
      | FOHornClauseCore.goal body, hMem' =>
        simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause] at hMem'
        simp only [FOHornClause.evalInHerbrand]; intro hAll
        rw [List.mem_map] at hMem'; obtain ⟨b, hbMem, rfl⟩ := hMem'
        simp only [clauseToFormula.litToFormula, formulaEvalN] at hLitEval
        exact hLitEval
          ((herbrandToStructure_formulaEval H assign b).mpr (hAll b ((LCS.Finset.mem_toList body b).mp hbMem)))
    -- Step 3: Derive contradiction via hEntails.
    -- All prog clauses hold in H, and negGoalClause also holds in H.
    -- But hEntails says: if prog holds then negGoalClause does NOT hold.
    exact hEntails H
      (fun s c hc => clauseToEval s c (List.mem_append_left _ hc)
        (transfer s c (List.mem_append_left _ hc)))
      assign
      (clauseToEval assign negGoalClause
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        (transfer assign negGoalClause
          (List.mem_append_right _ (List.mem_singleton.mpr rfl))))


proof_of uniqueNegativeClause := by
  -- BEGIN PROOF
    -- All clauses in P are definite (by hDef), so the only
    -- non-definite clause in P ++ [negGoalClause] is negGoalClause.
    intro c hc hcNeg
    rw [hSet] at hc
    rw [List.mem_append] at hc
    cases hc with
    | inl hIn =>
      -- c ∈ P, so c is definite by hDef, contradicting hcNeg
      exact absurd (hDef c hIn) hcNeg
    | inr hIn =>
      -- c ∈ [negGoalClause], so c = negGoalClause
      rw [List.mem_singleton] at hIn
      exact hIn


helper /-- Theorem 9.5.2 (helper): Under the indexed `FOSLDDerivation D goals cg`
    API, each step already carries `hClause : clause ∈ D` as a
    constructor field, so `clauseSequenceInP d D` is an immediate
    structural induction on `d`. -/
theorem derivation_clauseSeqInP {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (clauseSequenceInP (hNoEq := hNoEq)) d D := by
-- BEGIN PROOF
  show clauseSequenceInP.clauseSeqAux hNoEq d D
  induction d with
  | init _ _ => trivial
  | step _ _ hClause _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨hClause, ih⟩

helper /-- findIndex returns an index strictly less than the list length. -/
theorem findIndex_lt_length {l : List Nat} {v k : Nat}
    (h : _root_.LCS.SLD.LogicProgramming.findIndex l v = some k) : k < l.length := by
-- BEGIN PROOF
  induction l generalizing k with
  | nil => simp [_root_.LCS.SLD.LogicProgramming.findIndex] at h
  | cons x xs ih =>
    simp only [_root_.LCS.SLD.LogicProgramming.findIndex] at h
    split at h
    · injection h with h; subst h; exact Nat.zero_lt_succ _
    · cases hfi : _root_.LCS.SLD.LogicProgramming.findIndex xs v with
      | none => simp [hfi] at h
      | some j =>
        simp [hfi] at h
        have hj := ih hfi
        simp [List.length_cons]; omega

helper /-- getD at an in-bounds index is independent of the default value. -/
theorem getD_inbounds {α : Type} (l : List α) (k : Nat) (d1 d2 : α)
    (h : k < l.length) : l.getD k d1 = l.getD k d2 := by
  simp [List.getD, List.getElem?_eq_getElem (h := h)]

helper /-- Evaluating termSubstAll t sigma in a Herbrand structure is the same as
    evaluating t with the induced assignment v => evalTermInHerbrand assign (sigma v). -/
theorem evalTermInHerbrand_subst {L : Language}
    (assign : Nat → _root_.LCS.SLD.LogicProgramming.GroundTerm L) (sigma : Nat → Term L) (t : Term L) :
    _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (termSubstAll t sigma) =
    _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand (fun v => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (sigma v)) t := by
-- BEGIN PROOF
  induction t with
  | var v => apply Subtype.ext; rfl
  | const c => apply Subtype.ext; rfl
  | func f args ih =>
    apply Subtype.ext
    simp [termSubstAll, _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand, _root_.LCS.SLD.LogicProgramming.evalTermInHerbrandRaw]
    funext i; exact congrArg Subtype.val (ih i)

helper /-- For quantifier-free formulas, evaluating formulaSubstAll f sigma in a
    Herbrand structure equals evaluating f with the sigma-induced assignment. -/
theorem evalFormulaInHerbrand_subst {L : Language} {hNoEq : L.withoutEquality}
    (H : _root_.LCS.SLD.LogicProgramming.HerbrandStructure L hNoEq)
    (assign : Nat → _root_.LCS.SLD.LogicProgramming.GroundTerm L) (sigma : Nat → Term L) (f : FormulaN L)
    (hQF : isQuantifierFree f) :
    _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand H assign (formulaSubstAll f sigma) ↔
    _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand H (fun v => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (sigma v)) f := by
-- BEGIN PROOF
  induction f with
  | predN P args =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    have : (fun i => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (termSubstAll (args i) sigma)) =
           (fun i => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand (fun v => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (sigma v)) (args i)) :=
      funext (fun i => evalTermInHerbrand_subst assign sigma (args i))
    rw [show List.ofFn (fun i => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (termSubstAll (args i) sigma)) =
           List.ofFn (fun i => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand (fun v => _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign (sigma v)) (args i))
        from congrArg List.ofFn this]
  | eq_ _ t1 t2 =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    constructor <;> intro h
    · rw [← evalTermInHerbrand_subst assign sigma t1,
          ← evalTermInHerbrand_subst assign sigma t2]; exact h
    · rw [evalTermInHerbrand_subst assign sigma t1,
          evalTermInHerbrand_subst assign sigma t2]; exact h
  | neg A ih =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    exact not_congr (ih hQF)
  | conj A B ihA ihB =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    exact and_congr (ihA hQF.1) (ihB hQF.2)
  | disj A B ihA ihB =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    exact or_congr (ihA hQF.1) (ihB hQF.2)
  | impl A B ihA ihB =>
    simp only [formulaSubstAll, _root_.LCS.SLD.LogicProgramming.evalFormulaInHerbrand]
    exact imp_congr (ihA hQF.1) (ihB hQF.2)
  | all _ _ => exact absurd hQF id
  | ex _ _ => exact absurd hQF id

helper /-- Evaluating a ground term in a Herbrand structure returns the term itself. -/
theorem evalTermInHerbrand_ground {L : Language}
    (assign : Nat → _root_.LCS.SLD.LogicProgramming.GroundTerm L) (gt : _root_.LCS.SLD.LogicProgramming.GroundTerm L) :
    _root_.LCS.SLD.LogicProgramming.evalTermInHerbrand assign gt.val = gt := by
-- BEGIN PROOF
  apply Subtype.ext
  simp [_root_.LCS.SLD.LogicProgramming.evalTermInHerbrand]
  obtain ⟨tv, hcl⟩ := gt
  induction tv with
  | var v =>
    exfalso
    have hv : termFV (Term.var (L := L) v) v := rfl
    have hcl' : termFV (Term.var (L := L) v) = (∅ : Set Nat) := hcl
    rw [hcl'] at hv; exact hv
  | const c => rfl
  | func f args ih =>
    simp [_root_.LCS.SLD.LogicProgramming.evalTermInHerbrandRaw]; funext i
    exact ih i (_root_.LCS.SLD.LogicProgramming.closedFunc_arg hcl i)

helper /-- clauseToFormula of a non-empty FOClause is NNF, universal-only, and
    equality-free, when each literal wraps a FormulaN that is itself
    NNF, universal-only, and equality-free. -/
theorem clauseToFormula_wf_of_lits {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L) :
    ∀ (lits : FOClause L hNoEq),
    lits ≠ [] →
    (∀ lit ∈ lits, match lit with
      | .pos f =>
          _root_.LCS.SLD.LogicProgramming.formulaIsNNF f.toFormula ∧
            _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly f.toFormula ∧ formulaNoEq f.toFormula
      | .neg f =>
          _root_.LCS.SLD.LogicProgramming.formulaIsNNF (.neg f.toFormula) ∧
            _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly f.toFormula ∧ formulaNoEq f.toFormula) →
    _root_.LCS.SLD.LogicProgramming.formulaIsNNF ((clauseToFormula (hNoEq := hNoEq)) A lits) ∧
    _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly ((clauseToFormula (hNoEq := hNoEq)) A lits) ∧
    formulaNoEq ((clauseToFormula (hNoEq := hNoEq)) A lits) := by
-- BEGIN PROOF
  intro lits hNe hLits
  induction lits with
  | nil => exact absurd rfl hNe
  | cons lit rest ih =>
    have hLitWF := hLits lit (by simp)
    cases rest with
    | nil =>
      simp only [clauseToFormula]
      cases lit with
      | pos f =>
        simp only [clauseToFormula.litToFormula]; exact hLitWF
      | neg f =>
        simp only [clauseToFormula.litToFormula]
        obtain ⟨h1, h2, h3⟩ := hLitWF
        exact ⟨h1, h2, h3⟩
    | cons r rs =>
      simp only [clauseToFormula]
      have hRest := ih (by simp) (fun l hl => hLits l (List.mem_cons.mpr (Or.inr hl)))
      cases lit with
      | pos f =>
        simp only [clauseToFormula.litToFormula, _root_.LCS.SLD.LogicProgramming.formulaIsNNF, _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly, formulaNoEq]
        obtain ⟨h1, h2, h3⟩ := hLitWF
        exact ⟨⟨h1, hRest.1⟩, ⟨h2, hRest.2.1⟩, ⟨h3, hRest.2.2⟩⟩
      | neg f =>
        simp only [clauseToFormula.litToFormula, _root_.LCS.SLD.LogicProgramming.formulaIsNNF, _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly, formulaNoEq]
        obtain ⟨h1, h2, h3⟩ := hLitWF
        exact ⟨⟨h1, hRest.1⟩, ⟨h2, hRest.2.1⟩, ⟨h3, hRest.2.2⟩⟩

helper /-- An atomic formula (predN or eq_) is quantifier-free (in the
    Soundness sense). -/
theorem isAtomic_implies_isQuantifierFree {L : Language}
    (b : FormulaN L) (h : b.isAtomic = true) :
    isQuantifierFree b := by
-- BEGIN PROOF
  cases b <;> simp [FormulaN.isAtomic] at h <;> trivial

helper /-- formulaSubstAll of an atomic formula is still quantifier-free. -/
theorem isAtomic_substAll_isQuantifierFree {L : Language}
    (b : FormulaN L) (sigma : Nat → Term L) (h : b.isAtomic = true) :
    isQuantifierFree (formulaSubstAll b sigma) :=
-- BEGIN PROOF
  isQF_formulaSubstAll _ sigma (isAtomic_implies_isQuantifierFree b h)

helper /-- findIndex on a Nodup list returns exactly the index of the element. -/
theorem findIndex_get_eq_of_nodup {l : List Nat}
    (hNoDup : l.Nodup)
    (i : Fin l.length) :
    _root_.LCS.SLD.LogicProgramming.findIndex l (l.get i) = some i.val := by
-- BEGIN PROOF
  induction l with
  | nil => exact absurd i.isLt (by simp)
  | cons x xs ih =>
    have ⟨hNotMemXs, hNoDupXs⟩ := List.nodup_cons.mp hNoDup
    match i with
    | ⟨0, _⟩ =>
      simp only [_root_.LCS.SLD.LogicProgramming.findIndex, List.get]
      simp [BEq.beq]
    | ⟨k + 1, hk⟩ =>
      simp only [List.get]
      have hklt : k < xs.length := Nat.lt_of_succ_lt_succ hk
      -- Unfold findIndex and simplify the if
      simp only [_root_.LCS.SLD.LogicProgramming.findIndex]
      -- x ≠ xs[k] because xs[k] ∈ xs and x ∉ xs
      have hNe : ¬(x = xs[k]) := by
        intro heq
        exact hNotMemXs (heq ▸ List.getElem_mem hklt)
      simp [hNe]
      -- Now goal: findIndex xs xs[k] = some k
      -- This matches ih applied to ⟨k, hklt⟩ after simplifying List.get
      exact ih hNoDupXs ⟨k, hklt⟩

helper /-- For Horn clauses whose atoms are all predN (no eq_), clauseToFormula
    of the clause translation is NNF, universal-only, and equality-free,
    provided the clause's toFOClause is non-empty. -/
theorem hornClause_clauseToFormula_wf {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (c : FOHornClause L hNoEq)
    (hNe : (c.toFOClause (hNoEq := hNoEq)) ≠ [])
    (hAtoms : ∀ lit ∈ (c.toFOClause (hNoEq := hNoEq)), match lit with
      | .pos f => ∃ p args, f = .predN p args
      | .neg f => ∃ p args, f = .predN p args) :
    _root_.LCS.SLD.LogicProgramming.formulaIsNNF ((clauseToFormula (hNoEq := hNoEq)) A (c.toFOClause (hNoEq := hNoEq))) ∧
    _root_.LCS.SLD.LogicProgramming.formulaUniversalOnly ((clauseToFormula (hNoEq := hNoEq)) A (c.toFOClause (hNoEq := hNoEq))) ∧
    formulaNoEq ((clauseToFormula (hNoEq := hNoEq)) A (c.toFOClause (hNoEq := hNoEq))) := by
-- BEGIN PROOF
  apply (clauseToFormula_wf_of_lits (hNoEq := hNoEq)) A (c.toFOClause (hNoEq := hNoEq)) hNe
  intro lit hlit
  have hA := hAtoms lit hlit
  cases lit with
  | pos f =>
    obtain ⟨p, args, rfl⟩ := hA
    exact ⟨trivial, trivial, trivial⟩
  | neg f =>
    obtain ⟨p, args, rfl⟩ := hA
    exact ⟨trivial, trivial, trivial⟩

proof_of sldResolution_complete := by
  -- DEBT(T9-18): pre-existing completeness proof obligation
  -- REPAIR(T9-27): proof pending — lift a finite subtheory refutation of the original query and factor the answer through one finite-support eta
  sorry

end LCS.SLD.LogicProgramming.Completeness
