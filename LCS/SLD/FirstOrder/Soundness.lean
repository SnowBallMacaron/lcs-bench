import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import Attach
import LCS.SLD.FirstOrder.Soundness.ProofsStamp

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: formulaSubstAll agrees with substLit.substFormula. Both
    apply termSubstAll to all terms in a formula homomorphically. -/
theorem formulaSubstAll_eq_substFormula {L : Language} :
    ∀ (A : FormulaN L) (sigma : Nat → Term L),
    formulaSubstAll A sigma = substLit.substFormula sigma A := by
-- BEGIN PROOF
  intro A; induction A with
  | predN _ _ => intro _; rfl
  | eq_ _ _ _ => intro _; rfl
  | neg A ih => intro s; simp [formulaSubstAll, substLit.substFormula, ih]
  | conj A B ihA ihB => intro s; simp [formulaSubstAll, substLit.substFormula, ihA, ihB]
  | disj A B ihA ihB => intro s; simp [formulaSubstAll, substLit.substFormula, ihA, ihB]
  | impl A B ihA ihB => intro s; simp [formulaSubstAll, substLit.substFormula, ihA, ihB]
  | all _ A ih => intro s; simp [formulaSubstAll, substLit.substFormula, ih]
  | ex _ A ih => intro s; simp [formulaSubstAll, substLit.substFormula, ih]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- formulaSubstAll preserves the quantifier-free property. -/
theorem isQF_formulaSubstAll {L : Language} (A : FormulaN L) (sigma : Nat → Term L)
    (h : isQuantifierFree A) : isQuantifierFree (formulaSubstAll A sigma) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih => exact ih h
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | all _ _ => exact absurd h id
  | ex _ _ => exact absurd h id



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: evaluating a formula after formulaSubstAll sigma is equivalent
    to evaluating the original formula under the substitution-induced
    assignment. Requires the formula to be quantifier-free, since
    simultaneous substitution may capture bound variables in quantifier
    cases. All SLD clause-form formulas are quantifier-free, so this
    hypothesis is always satisfied in practice. -/
theorem formulaSubstAll_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (A : FormulaN L) (hQF : isQuantifierFree A) :
    formulaEvalN M (formulaSubstAll A sigma) s ↔
    formulaEvalN M A (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  rw [formulaSubstAll_eq_substFormula]
  exact (substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma A (isQF_implies_substFreshFor sigma A hQF)

-- ===================================================================
-- Lemma 9.4.1 (helper): list element in take or drop
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.PropositionalEncoding
/-- Helper: if xs[j] exists and j ≠ k, then xs[j] is in
    xs.take k ++ xs.drop (k + 1). -/
theorem getElem_in_take_append_drop {α : Type} (xs : List α) (k j : Nat)
    (hj : j < xs.length) (hjk : j ≠ k) :
    xs[j] ∈ xs.take k ++ xs.drop (k + 1) := by
-- BEGIN PROOF
  by_cases hjltk : j < k
  · have hlen : j < ((xs.take k).length) := by
      rw [List.length_take]; omega
    have heq : xs[j] = (xs.take k)[j] := by
      rw [List.getElem_take]
    rw [heq]
    exact List.mem_append_left _ (List.getElem_mem hlen)
  · have hjgek1 : k + 1 ≤ j := by omega
    have hlen : j - (k + 1) < ((xs.drop (k + 1)).length) := by
      rw [List.length_drop]; omega
    have heq : xs[j] = (xs.drop (k + 1))[j - (k + 1)] := by
      rw [List.getElem_drop]; congr; omega
    rw [heq]
    exact List.mem_append_right _ (List.getElem_mem hlen)

-- ===================================================================
-- Lemma 9.4.1 (helper): currentGoal atoms are QF
-- ===================================================================

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Every atom in the current goal of a derivation has a
    quantifier-free ambient-formula embedding. This is immediate from
    the structural atomic carrier. -/
theorem currentGoal_allQF {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {currentGoalVal : LCS.Finset (FOAtom L hNoEq)}
    (_d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals currentGoalVal) :
    ∀ a ∈ currentGoalVal, isQuantifierFree a.toFormula := by
-- BEGIN PROOF
  intro atom _
  exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) atom

-- ===================================================================
-- Lemma 9.4.1 (helper): preimage atom QF from clause and prevGoal QF
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every atom in the preimage Finset used by an SLD step has a
    quantifier-free ambient-formula embedding. -/
theorem preimage_allQF {L : Language} (hNoEq : L.withoutEquality)
    (prevGoal : LCS.Finset (FOAtom L hNoEq))
    (clause : FOHornClause L hNoEq)
    (Ak : FOAtom L hNoEq)
    (rho : Nat → Term L) :
    ∀ a ∈ (prevGoal.erase Ak).union
      (LCS.Finset.ofList
        (clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) rho)))),
    isQuantifierFree a.toFormula := by
-- BEGIN PROOF
  intro atom _
  exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) atom

-- ===================================================================
-- Lemma 9.4.1 (key invariant): SLD goal clause preservation
-- ===================================================================

-- ATTACH-KEEP: existing oversized helper stays with its front size allowance
-- ATTACH-BLOCKER: existing oversized helper stays with its front size allowance
/-- Key invariant for SLD-resolution soundness: if the SLD-derivation
    is indexed by `currentGoalVal` against D and goals, and a structure
    M satisfies the universal closures of all clause translations in
    D ∪ goals, then for every assignment s, the clause formula of the
    current goal (translated as negative literals) holds in M at s.
    This means: for any assignment s, at least one current goal atom
    evaluates to False. When the derivation is a refutation (current
    goal is empty), the clause formula is falsum, giving a
    contradiction. Requires all Horn clauses to have quantifier-free
    atoms (always true for SLD clause-form). Well-formedness is now
    automatic from the indexed inductive's constructor fields, and
    quantifier-freeness is automatic from the structural atom carrier. -/
theorem sld_goal_invariant
    {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D : Set (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {currentGoalVal : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoalVal)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal body hNoEq)
    (M : Structure L)
    (hSat : ∀ C, (∃ h, (h ∈ D ∨ h ∈ goals) ∧ (h.toFOClause (hNoEq := by all_goals exact hNoEq)) = C) →
      ∀ fvs, (∀ n, (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) C n → n ∈ fvs) →
        (∀ s : Assignment M, formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum C fvs) s)) :
    ∀ s : Assignment M,
      formulaEvalN M
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (currentGoalVal.toList.map FOLiteralCore.neg)) s := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

-- ===================================================================
-- Lemma 9.4.1: Soundness of first-order SLD-resolution
-- ===================================================================

/-- Lemma 9.4.1: if an arbitrary program and finite negative-goal family
    have an SLD-refutation, their same original union is unsatisfiable
    (SQ17). The derivation retains its local renaming and MGU certificates. -/
@[blueprint "chap9__lemma_9_4_1" (main := true)]
theorem foSLDResolution_sound
    {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D : Set (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {currentGoalVal : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoalVal)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal body hNoEq)
    (hRef : (d.isRefutation (hNoEq := by all_goals exact hNoEq))) :
    FOClauseSet.isUnsatisfiable hNoEq
      (fun C => ∃ h, (h ∈ D ∨ h ∈ goals) ∧ h.toFOClause = C)

-- ===================================================================
-- Theorem 9.4.1 (helpers): Ground propositional SLD → FO SLD lifter
-- ===================================================================

/-- Theorem 9.4.1 (required helper): Identity substitution preserves a ground
    term. Used by `sldDerivation_to_foSLD_ground` to discharge the per-step
    unification/separating-pair conditions when lifting a propositional
    (ground-instance) SLD-derivation to a first-order SLD-derivation. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem termSubstAll_var_ground {L : Language} (t : Term L)
    (hG : ∀ x, ¬ termVars (L := L) t x) :
    termSubstAll t Term.var = t 

/-- Theorem 9.4.1 (required helper): Identity substitution preserves a ground
    formula. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaSubstAll_var_ground {L : Language} (A : FormulaN L)
    (hG : ∀ x, ¬ formulaVars A x) :
    formulaSubstAll A Term.var = A 

/-- Theorem 9.4.1 (required helper): Mapping `formulaSubstAll Term.var`
    over a list of ground formulas is the identity. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem map_formulaSubstAll_var_ground {L : Language}
    (xs : List (FormulaN L))
    (hG : ∀ a ∈ xs, ∀ x, ¬ formulaVars a x) :
    xs.map (fun a => formulaSubstAll a Term.var) = xs 

/-- Theorem 9.4.1 (required helper): Extensionality for `formulaSubstAll`.
    If two substitutions agree on every free variable of `A`, they produce
    the same result when applied to `A`. Bridges to `substFormula_ext_vars`
    via `formulaSubstAll_eq_substFormula`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaSubstAll_ext {L : Language} (A : FormulaN L)
    (sigma tau : Nat → Term L)
    (h : ∀ x, formulaVars A x → sigma x = tau x) :
    formulaSubstAll A sigma = formulaSubstAll A tau 

/-- Theorem 9.4.1 (required helper): For a ground formula `A` (no free
    variables), `formulaSubstAll A sigma = A` for any substitution `sigma`.
    Strengthens `formulaSubstAll_var_ground` (which handles only the
    identity substitution) to arbitrary substitutions. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaSubstAll_ground {L : Language} (A : FormulaN L)
    (sigma : Nat → Term L)
    (hG : ∀ x, ¬ formulaVars A x) :
    formulaSubstAll A sigma = A 

/-- Theorem 9.4.1 (required helper): Composition law for `formulaSubstAll`.
    Applying `rho` and then `theta` is the same as applying the
    composition `SubstitutionCore.substCompose theta rho` in one step. Bridges to
    `substFormula_comp` via `formulaSubstAll_eq_substFormula`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaSubstAll_comp {L : Language} (A : FormulaN L)
    (theta rho : Nat → Term L) :
    formulaSubstAll (formulaSubstAll A rho) theta =
      formulaSubstAll A (SubstitutionCore.substCompose theta rho) 





-- retained: used by LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Composition law for structural atom substitution. -/
theorem atomSubst_comp {L : Language} (hNoEq : L.withoutEquality)  (A : FOAtom L hNoEq)
    (theta rho : Nat → Term L) :
    ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) rho A)).subst (hNoEq := by all_goals exact hNoEq) theta =
      (A.subst (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose theta rho) := by
  apply FOAtomCore.toFormula_injective
  simp only [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq))]
  exact formulaSubstAll_comp A.toFormula theta rho

/-- Theorem 9.4.1 (required helper): For two ground clauses, `(Term.var,
    Term.var)` is a separating pair. All conjuncts of `IsSeparatingPair`
    hold vacuously since neither clause has free variables. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem isSeparatingPair_var_ground {L : Language} (hNoEq : L.withoutEquality)
    (A B : FOClause L hNoEq)
    (hGA : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) A x)
    (hGB : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) B x) :
    (IsSeparatingPair (L := L) (hNoEq := by all_goals exact hNoEq)) Term.var Term.var A B 

/-- Theorem 9.4.1 (companion type): A ground SLD step transcript. Carries the
    per-step data needed to build one `FOSLDDerivation.step` onto an existing
    derivation indexed at `prevGoal` using identity (ground) substitutions.
    Fields correspond one-to-one to the `.step` constructor's arguments. -/
@[blueprint "chap9__theorem_9_4_1"]
structure GroundSLDStep {L : Language} (hNoEq : L.withoutEquality)
    (D : List (FOHornClause L hNoEq))
    (prevGoal : LCS.Finset (FOAtom L hNoEq)) where
  /-- The definite Horn clause used in this resolution step. -/
  clause : FOHornClause L hNoEq
  /-- Witness: the clause is in the program `D`. -/
  hClause : clause ∈ D
  /-- Witness: the clause is a definite clause (rule or fact). -/
  hDef : (clause.isDefinite (hNoEq := by all_goals exact hNoEq))
  /-- The selected atom. -/
  Ak : FOAtom L hNoEq
  /-- The head atom of the definite clause. -/
  headA : FOAtom L hNoEq
  /-- Witness that `Ak ∈ prevGoal`. -/
  hAk : Ak ∈ prevGoal
  /-- Witness that the clause's structural head equals `some headA`. -/
  hHead : (clause.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA
  /-- Ground unification: `Ak = headA`. With identity substitution,
      the textbook `hUnif` equation reduces to `Ak = headA`. -/
  hUnifGround : Ak = headA
  /-- Ground condition: atoms in `prevGoal` have no free variables
      (the sequence N_i atoms are all ground). -/
  hGroundPrev : ∀ a ∈ prevGoal, ∀ x, ¬ a.vars x
  /-- Ground condition: `clause.toFOClause` has no free variables
      (the definite clause is a ground instance). -/
  hGroundClause : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (clause.toFOClause (hNoEq := by all_goals exact hNoEq)) x

/-- The equality-free MGU certificate supplies the general derivation kernel. -/
theorem isAtomMGU_toCore {L : Language} (hNoEq : L.withoutEquality)
    {a b : FOAtom L hNoEq} {σ : Nat → Term L} (h : IsAtomMGU hNoEq a b σ) :
    IsAtomMGUCore a b σ := by
  cases a <;> cases b <;>
    simpa [IsAtomMGU, IsAtomMGUCore, atomUnifPairs?, atomUnifPairsCore] using h

/-- Theorem 9.4.1 (required helper): Extend an `FOSLDDerivation` with one
    ground SLD step using identity substitutions `rho = sigma = Term.var`.
    Under the ground assumption (prev goal and clause have no free variables),
    `hUnif` reduces to `Ak = headA` via `formulaSubstAll_var_ground`, and
    `hSep` hold vacuously. The output index equals `prevGoal`
    with selected atom erased and `clause.bodyFOAtoms` unioned, all under
    identity substitution (as a Finset). -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def foSLDStepGround {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}

    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal) :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
        ((prevGoal.erase step.Ak).union
          (LCS.Finset.ofList
            (step.clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)))))) :=
-- BEGIN PROOF
  FOSLDDerivation.step
    (prev := prev)
    (clause := step.clause)
    (hClause := step.hClause)
    (hDef := step.hDef)
    (Ak := step.Ak)
    (headA := step.headA)
    (hAk := step.hAk)
    (hHead := step.hHead)
    (rho := Term.var)
    (sigma := Term.var)
    (hMGU := by
      change IsAtomMGUCore step.Ak (FOAtomCore.subst hNoEq Term.var step.headA) Term.var
      rw [(atomSubst_id (hNoEq := by all_goals exact hNoEq))]
      apply isAtomMGU_toCore hNoEq
      exact (identitySubst_isAtomMGU_of_eq_noEquality (hNoEq := hNoEq)) step.hUnifGround)
    (hSep := by
      apply (isSeparatingPair_var_ground (hNoEq := by all_goals exact hNoEq))
      · intro x ⟨lit, hMem, hV⟩
        rw [List.mem_map] at hMem
        obtain ⟨a, ha, rfl⟩ := hMem
        rw [LCS.Finset.mem_toList] at ha
        exact step.hGroundPrev a ha x hV
      · exact step.hGroundClause)


/-- Theorem 9.4.1 (required helper): A ground SLD transcript is a list of
    ground step-data values, each one producing one `.step` on the running
    derivation. The indices at each step are implicit — they are computed by
    `foSLDStepGround` from `prevGoal`. This encodes the per-step transcript
    of a propositional SLD-derivation lifted to the FO level with all
    substitutions being identity (ground). -/
@[blueprint "chap9__theorem_9_4_1"]
inductive GroundSLDTranscript {L : Language} (hNoEq : L.withoutEquality)
    (D : List (FOHornClause L hNoEq)) :
    (prevGoal : LCS.Finset (FOAtom L hNoEq)) → Type where
  /-- Empty transcript: no steps, prevGoal unchanged. -/
  | nil {prevGoal : LCS.Finset (FOAtom L hNoEq)} : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal
  /-- Cons: one step onto the transcript, producing a new prevGoal. -/
  | cons {prevGoal : LCS.Finset (FOAtom L hNoEq)}
      (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal)
      (rest : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D
        (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
          ((prevGoal.erase step.Ak).union
            (LCS.Finset.ofList
              (step.clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))))))) :
      (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal

/-- Theorem 9.4.1 (required helper): The final (terminal) goal after folding
    a ground SLD transcript onto a starting prevGoal. For `.nil` the final
    goal is `prevGoal`; for `.cons step rest` it is the final goal obtained
    by recursing on `rest` from the resolved subsequent goal. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def GroundSLDTranscript.finalGoal {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)} :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} → (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal →
      LCS.Finset (FOAtom L hNoEq)
  | prevGoal, .nil => prevGoal
  | _, .cons _ rest => rest.finalGoal

/-- Theorem 9.4.1 (required helper): Fold a ground SLD transcript onto an
    existing `FOSLDDerivation`, producing a new `FOSLDDerivation` indexed
    at the transcript's `finalGoal`. Each step in the transcript produces
    one `FOSLDDerivation.step` via `foSLDStepGround`. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def foldGroundTranscript {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}

    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal) :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals t.finalGoal :=
-- BEGIN PROOF
  match t with
  | .nil => prev
  | .cons step rest =>
    (foldGroundTranscript (hNoEq := by all_goals exact hNoEq)) ((foSLDStepGround (hNoEq := by all_goals exact hNoEq)) prev step) rest

/-- Theorem 9.4.1 (required helper): Lifter from a propositional SLD-derivation
    (via ordered FO transcript) to a first-order SLD-derivation. Given a
    first-order Horn program `D`, goal clauses `goals`, an initial goal
    witness, and a ground SLD transcript from that initial goal, produce an
    FOSLDDerivation whose final goal equals the transcript's `finalGoal`.

    This encodes the lifting lemma restricted to GROUND instances: the
    propositional derivation's clauses (atoms-as-Nat) correspond via an
    atom↔ground-formula encoding (the caller-supplied `atomMap`, which
    appears only indirectly through the transcript's `step.Ak` / `step.headA`
    values) to first-order atoms. At each step we use `rho = sigma = Term.var`
    (identity), so `hUnif` reduces to `Ak = headA` (supplied as
    `hUnifGround`), and `hSep` hold vacuously for ground clauses.

    Refutation transfer: if the transcript's `finalGoal` equals the empty
    list (the propositional square), the resulting FOSLDDerivation is an
    `.isRefutation`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem sldDerivation_to_foSLD_ground {L : Language} (hNoEq : L.withoutEquality)

    (D goals : List (FOHornClause L hNoEq))
    (initGoal : FOHornClause L hNoEq)
    (hInitMem : initGoal ∈ goals)
    (body : LCS.Finset (FOAtom L hNoEq))
    (hBody : LCS.Finset.ofList
      (initGoal.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))) = body)
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D body)
    (hRefEmpty : t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))) :
    ∃ (currentGoalFO : LCS.Finset (FOAtom L hNoEq))
      (d' : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals currentGoalFO), (d'.isRefutation (hNoEq := by all_goals exact hNoEq))

-- ===================================================================
-- Theorem 9.4.1 (helpers): Non-ground lifting from ground transcript
-- ===================================================================

/-- Theorem 9.4.1 (companion): Apply a simultaneous substitution to every
    atom in a Horn clause. Rule/fact/goal constructors are handled
    homomorphically via `formulaSubstAll`. -/
@[blueprint "chap9__theorem_9_4_1"]
def substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) : FOHornClause L hNoEq :=
  FOHornClauseCore.subst σ c

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Substitution preserves body membership through finite-set image (SQ16).
    Distinct atoms may have the same substitution instance. -/
theorem bodyFOAtoms_substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) (a : FOAtom L hNoEq) :
    a ∈ ((substAllInHornClause hNoEq c σ).bodyFOAtoms hNoEq) ↔
      a ∈ (c.bodyFOAtoms hNoEq).map (FOAtomCore.subst hNoEq σ) := by
  cases c <;>
    simp [substAllInHornClause, FOHornClause.bodyFOAtoms, FOHornClauseCore.subst,
      FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty,
      LCS.Finset.mem_toList, LCS.Finset.mem_image, List.mem_map, FOAtomCore.subst]

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Theorem 9.4.1 (companion): Substitution preserves definiteness. -/
theorem isDefinite_substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) :
    (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ).isDefinite (hNoEq := by all_goals exact hNoEq)) ↔ (c.isDefinite (hNoEq := by all_goals exact hNoEq)) := by
-- BEGIN PROOF
  cases c <;> rfl







-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Theorem 9.4.1 (companion type): Per-step correspondence between a ground
    SLD transcript over a ground-instance program `D_g` and a non-ground
    source program `D_orig`. Each step in the transcript is witnessed to
    arise from applying some substitution `σ_i` to a source clause
    `C_i ∈ D_orig`. This structure mirrors the per-leaf correspondence in
    `lifting_lemma_refutation_wf` (Ch8) but at the SLD-step level. -/
@[blueprint "chap9__theorem_9_4_1"]
inductive GroundSLDCorrespondence {L : Language} (hNoEq : L.withoutEquality)
    (D_orig : List (FOHornClause L hNoEq))
    (D_g : List (FOHornClause L hNoEq)) :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} →
      (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g prevGoal → Type where
  /-- Empty correspondence for an empty transcript. -/
  | nil {prevGoal : LCS.Finset (FOAtom L hNoEq)} :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g
        (prevGoal := prevGoal) GroundSLDTranscript.nil
  /-- Cons: one step's correspondence witnesses, plus the rest. -/
  | cons {prevGoal : LCS.Finset (FOAtom L hNoEq)}
      (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g prevGoal)
      (rest : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g
        (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
          ((prevGoal.erase step.Ak).union
            (LCS.Finset.ofList
              (step.clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)))))))
      (sourceC : FOHornClause L hNoEq)
      (hSourceMem : sourceC ∈ D_orig)
      (sigma : Nat → Term L)
      (hInst : step.clause = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceC sigma)
      (restCorr : (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g rest) :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g
        (prevGoal := prevGoal) (GroundSLDTranscript.cons step rest)

/-- Theorem 9.4.1 (required helper): Build a `GroundSLDCorrespondence` by
    recursively walking a ground SLD transcript. At each `.cons step rest`
    the per-clause instance witness `hDGInst step.clause step.hClause`
    yields the source clause `sourceC ∈ D_orig`, a substitution `σ`, and
    the instance relation `step.clause = substAllInHornClause sourceC σ`;
    these populate the `.cons` constructor fields. The recursive call on
    `rest` supplies the tail correspondence. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def buildGroundSLDCorrespondence {L : Language} (hNoEq : L.withoutEquality)
    (D_orig D_g : List (FOHornClause L hNoEq))
    (hDGInst : ∀ c_g ∈ D_g, ∃ (c : FOHornClause L hNoEq) (_hMem : c ∈ D_orig)
        (σ : Nat → Term L),
      c_g = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ ∧
      (∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c_g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)) :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} →
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g prevGoal) →
    (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g t
  | _, .nil => .nil
  | _, .cons step rest =>
    let h := hDGInst step.clause step.hClause
    let sourceC : FOHornClause L hNoEq := h.choose
    let hSourceMem : sourceC ∈ D_orig := h.choose_spec.choose
    let sigma : Nat → Term L := h.choose_spec.choose_spec.choose
    let hInst : step.clause = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceC sigma :=
      h.choose_spec.choose_spec.choose_spec.1
    let restCorr : (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g rest :=
      (buildGroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g hDGInst rest
    .cons step rest sourceC hSourceMem sigma hInst restCorr

-- ===================================================================
-- Theorem 9.4.1 (required helpers): Atomic-formula shape extraction
-- ===================================================================

/-- Theorem 9.4.1 (required helper): Every atomic `FormulaN` in a language
    without equality is a predicate application `predN P args`.

    The `eq_` constructor carries a proof `L.hasEquality = true`, which
    directly contradicts `L.withoutEquality = (L.hasEquality = false)`.
    All non-atomic constructors (`neg`, `conj`, `disj`, `impl`, `all`,
    `ex`) are ruled out by `hAtomic`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem atomic_no_eq_shape {L : Language} (hNoEq : L.withoutEquality)
    (a : FormulaN L) (hAtomic : FormulaN.isAtomic a = true) :
    ∃ (P : L.predSymbols) (args : Fin (L.predArity P) → Term L),
      a = FormulaN.predN P args 

/-- Theorem 9.4.1 (required helper): If two atomic `FormulaN`s in a
    language without equality are equal, they share the same predicate
    symbol and their argument vectors agree (after suitable `HEq` cast).

    This is a direct consequence of `atomic_no_eq_shape` and constructor
    injectivity for `predN`. In the `.cons` case of the lifting lemma,
    `step.hUnifGround : step.Ak = step.headA` together with both being
    atomic yields the pair `(P, args_Ak) ≡ (P, args_headA)` from which the
    per-position unification pairs are formed. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem atomic_no_eq_same_pred {L : Language} (hNoEq : L.withoutEquality)
    (a b : FormulaN L)
    (hAtomicA : FormulaN.isAtomic a = true)
    (hAtomicB : FormulaN.isAtomic b = true)
    (hEq : a = b) :
    ∃ (P : L.predSymbols) (args_a args_b : Fin (L.predArity P) → Term L),
      a = FormulaN.predN P args_a ∧
      b = FormulaN.predN P args_b ∧
      args_a = args_b 

/-- Theorem 9.4.1 (required helper): IsPairwiseUnifier witness for the
    SLD lifting `.cons` case. Given a ground step `Ak = headA`
    (`hUnifGround`) where `step.clause = substAllInHornClause sourceC sigma`
    (`hInst`), the structural atoms `step.Ak` and `sourceC`'s head are
    predicate applications in a language without equality, and `sigma` unifies the
    per-position pair list
    `{(args_headOrig i, args_Ak i) | i : Fin (predArity P)}`.

    The groundness of `Ak` (`hAkGround`) discharges the idempotence
    requirement: `args_Ak i = termSubstAll (args_headOrig i) sigma` is
    itself ground (as a term in `Ak`'s argument vector), so applying
    `sigma` again is identity. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem sld_lifting_pairwise_unifier_witness {L : Language} (hNoEq : L.withoutEquality)

    (sourceC : FOHornClause L hNoEq)
    (headOrig : FOAtom L hNoEq)
    (hHeadOrig : (sourceC.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headOrig)
    (sigma : Nat → Term L)
    (step_clause : FOHornClause L hNoEq)
    (hInst : step_clause = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceC sigma)
    (Ak headA : FOAtom L hNoEq)
    (hStepHead : (step_clause.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA)
    (hUnifGround : Ak = headA)
    (hAkGround : ∀ x, ¬ Ak.vars x) :
    ∃ (P : L.predSymbols)
      (args_headOrig args_Ak : Fin (L.predArity P) → Term L),
      headOrig = FOAtomCore.predN P args_headOrig ∧
      Ak = FOAtomCore.predN P args_Ak ∧
      IsPairwiseUnifier sigma
        (List.ofFn (fun i : Fin (L.predArity P) =>
          (args_headOrig i, args_Ak i))) 

/-- Theorem 9.4.1 (required helper): Construct a separating pair
    `(Term.var, ρ')` for the SLD lifting `.cons` case. In the SLD setting
    `prevGoal` is ground (by `step.hGroundPrev` on the caller side), so
    `clauseFV prevGoalLits` is empty and the goal-side renaming can be
    taken to be the identity `Term.var`. The clause-side renaming is the
    odd-numbered fresh renaming on `FV(sourceC)`:
    `ρ' x = Term.var (2 * x + 1)` if `x ∈ clauseFV sourceC`, else
    `Term.var x`. This mirrors the even/odd pattern of the Ch8
    classical resolution lift at
    `LCS/FOResolution/Method/Completeness.lean:1253-1287`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem sld_lifting_separating_pair {L : Language} (hNoEq : L.withoutEquality)
    (prevGoalLits : List (FOLiteral L hNoEq))
    (sourceC : FOClause L hNoEq)
    (hPrevGround : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) prevGoalLits x) :
    ∃ (ρ' : Nat → Term L),
      (IsSeparatingPair (L := L) (hNoEq := by all_goals exact hNoEq)) Term.var ρ' prevGoalLits sourceC 

/-- Theorem 9.4.1 (required helper): Concrete separating-pair renaming
    for SLD lifting. Defined via `dite` against `Classical.propDecidable`:
    if `x ∈ clauseFV sourceC` return `Term.var (2*x+1)`, else return
    `Term.var x`. Returned as a plain `Nat → Term L` (not an opaque
    `.choose`) so `liftTranscript`'s `hUnifTransport` proof can invert
    it via its concrete definition. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def sldLiftingSeparatingPairConcrete {L : Language} (hNoEq : L.withoutEquality)
    (sourceC : FOClause L hNoEq) : Nat → Term L :=
  fun x =>
    @dite (Term L) ((clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x) (Classical.propDecidable _)
      (fun _ => Term.var (2 * x + 1)) (fun _ => Term.var x)

/-- Theorem 9.4.1 (required helper): On `FV(sourceC)`, the concrete
    separating pair's renaming returns `Term.var (2 * x + 1)`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem sldLiftingSeparatingPairConcrete_on_fv {L : Language} (hNoEq : L.withoutEquality)
    (sourceC : FOClause L hNoEq) (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x) :
    (sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) sourceC x = Term.var (2 * x + 1) 



/-- Theorem 9.4.1 (required helper): Off `FV(sourceC)`, the concrete
    separating pair's renaming returns `Term.var x` (identity). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem sldLiftingSeparatingPairConcrete_off_fv {L : Language} (hNoEq : L.withoutEquality)
    (sourceC : FOClause L hNoEq) (x : Nat) (hx : ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x) :
    (sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) sourceC x = Term.var x 

@[blueprint "chap9__theorem_9_4_1"]
theorem sld_lifting_separating_pair_concrete {L : Language} (hNoEq : L.withoutEquality)
    (prevGoalLits : List (FOLiteral L hNoEq))
    (sourceC : FOClause L hNoEq)
    (hPrevGround : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) prevGoalLits x) :
    (IsSeparatingPair (L := L) (hNoEq := by all_goals exact hNoEq)) Term.var
      ((sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) sourceC)
      prevGoalLits sourceC 

/-- Lift a ground transcript to its source program at the same final goal.
    The pending construction must account for MGU factorization. -/
noncomputable def liftTranscript {L : Language} (hNoEq : L.withoutEquality)
    (D_orig D_g goals : List (FOHornClause L hNoEq))
     :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D_orig) goals prevGoal →
    {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g prevGoal} →
    (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g t →
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D_orig) goals t.finalGoal := by
  -- REPAIR(CH9-ROOT): proof pending
  -- DEBT(pre-existing: arbitrary unifier supplied where the derivation requires an MGU)
  sorry

/-- Theorem 9.4.1 (required helper): (Lifting Lemma, SLD analogue of Lem 8.5.4)
    Given a GROUND `FOSLDDerivation`-style transcript `t` over a list of
    ground clauses `D_g` plus a per-step correspondence witnessing that
    each `t`-step's clause is a substitution instance of some `C_i` in a
    non-ground program `D_orig`, there exists an `FOSLDDerivation` over
    the ORIGINAL non-ground `D_orig` that is also a refutation.

    This is the SLD analogue of `lifting_lemma_refutation_wf` at
    `LCS/FOResolution/Method/Completeness.lean:1799`: the input carries
    ground labels that arose as `σ_i`-instances of non-ground source
    clauses; the output is a non-ground derivation over the originals.

    The statement's compatibility with the current derivation carrier is
    recorded as truth-open in the chapter 9 proof-debt ledger. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem lifting_lemma_foSLD_refutation {L : Language} (hNoEq : L.withoutEquality)
    (D_orig D_g goals : List (FOHornClause L hNoEq))

    (initGoal : FOHornClause L hNoEq)
    (hInitMem : initGoal ∈ goals)
    (sigmaInit : Nat → Term L)
    (body : LCS.Finset (FOAtom L hNoEq))
    (hBody : body = LCS.Finset.ofList
      (initGoal.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigmaInit))))
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g body)
    (hRefEmpty : t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq)))
    (corr : (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g t) :
    ∃ (d' : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D_orig) goals (∅ : LCS.Finset (FOAtom L hNoEq))),
      (d'.isRefutation (hNoEq := by all_goals exact hNoEq))

-- ===================================================================
-- Direct hash-ground transcript adapter
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The first selected atom recorded by a ground transcript.  A transcript
    stores its chronological first step at the outermost `cons`, unlike
    `FOSLDDerivation`, whose chronological first step is the innermost
    `step` above `init`. -/
def GroundSLDTranscript.firstSelectedAtom {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} :
    (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal → Option (FOAtom L hNoEq)
  | .nil => none
  | .cons step _ => some step.Ak

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Left-biased selection composition.  It states the accumulator
    orientation used when a transcript is appended to an existing
    derivation: an earlier selection already present in the accumulator
    remains first. -/
def firstSelectedAppend {α : Type} (earlier later : Option α) : Option α :=
  match earlier with
  | some a => some a
  | none => later

end LCS.SLD.FirstOrder
end

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness
namespace FOSLDDerivation

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Casting only the goal index does not change the derivation's first
    selected atom. -/
theorem firstSelectedAtom_cast {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {S T : LCS.Finset (FOAtom L hNoEq)} (h : S = T)
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals S) :
    (firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) (h ▸ d) = (firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) d := by
  cases h
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every positive-length derivation has a first selected atom. -/
theorem firstSelectedAtom_ne_none_of_length_pos {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {S : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals S) (hLength : 0 < (d.length (hNoEq := by all_goals exact hNoEq))) :
    (d.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) ≠ none := by
  induction d with
  | init goal hGoal =>
    simp [FOSLDDerivation.length] at hLength
  | step prev clause hClause hDef Ak headA hAk hHead rho sigma
      hUnif hSep ih =>
    cases prev with
    | init goal hGoal =>
      simp [FOSLDDerivation.firstSelectedAtom]
    | step prev' clause' hClause' hDef' Ak' headA' hAk' hHead'
        rho' sigma' hUnif' hSep' =>
      simp only [FOSLDDerivation.firstSelectedAtom]
      apply ih
      simp [FOSLDDerivation.length]

end FOSLDDerivation
end LCS.SLD.FirstOrder
end

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ATTACH-KEEP: helper is used from a reopened nested proof namespace
-- ATTACH-BLOCKER: helper is used from a reopened nested proof namespace
/-- A present earlier selection dominates left-biased selection
    composition. -/
theorem firstSelectedAppend_eq_left_of_ne_none {α : Type}
    (earlier later : Option α) (hEarlier : earlier ≠ none) :
    firstSelectedAppend earlier later = earlier := by
  cases earlier <;> simp_all [firstSelectedAppend]

end LCS.SLD.FirstOrder
end

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness
namespace FOSLDDerivation



end FOSLDDerivation
end LCS.SLD.FirstOrder
end

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness





-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A body atom contributes all of its syntactic variables to the
    standard-clause translation of its Horn clause. -/
theorem bodyAtom_formulaVars_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (A : FOAtom L hNoEq) (hA : A ∈ (c.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)))
    (x : Nat) (hx : A.vars x) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
  refine ⟨FOLiteralCore.neg A, ?_, hx⟩
  cases c with
  | rule head body =>
    simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at hA
    simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_append, List.mem_map]
    exact Or.inl ⟨A, hA, rfl⟩
  | fact head =>
    simpa [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms,
      FOHornClauseCore.body, finset_toList_empty] using hA
  | goal body =>
    simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at hA
    simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_map]
    exact ⟨A, hA, rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A head atom contributes all of its syntactic variables to the
    standard-clause translation of its Horn clause. -/
theorem headAtom_formulaVars_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (A : FOAtom L hNoEq)
    (hHead : (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some A)
    (x : Nat) (hx : A.vars x) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
  refine ⟨FOLiteralCore.pos A, ?_, hx⟩
  cases c with
  | rule head body =>
    simp only [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom, Option.some.injEq] at hHead
    subst head
    simp [FOHornClause.toFOClause, FOHornClauseCore.toFOClause]
  | fact head =>
    simp only [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom, Option.some.injEq] at hHead
    subst head
    simp [FOHornClause.toFOClause, FOHornClauseCore.toFOClause]
  | goal body =>
    simp [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] at hHead

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The selected atom of a ground step is ground. -/
theorem GroundSLDStep.akGround {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal) :
    ∀ x, ¬ step.Ak.vars x :=
  step.hGroundPrev step.Ak step.hAk

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The head atom named by a ground step is ground. -/
theorem GroundSLDStep.headGround {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal) :
    ∀ x, ¬ step.headA.vars x := by
  intro x hx
  exact step.hGroundClause x
    ((headAtom_formulaVars_clauseFV (hNoEq := by all_goals exact hNoEq)) step.clause step.headA step.hHead x hx)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every body atom of a ground step's input clause is ground. -/
theorem GroundSLDStep.bodyGround {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal)
    (A : FOAtom L hNoEq) (hA : A ∈ (step.clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq))) :
    ∀ x, ¬ A.vars x := by
  intro x hx
  exact step.hGroundClause x
    ((bodyAtom_formulaVars_clauseFV (hNoEq := by all_goals exact hNoEq)) step.clause A hA x hx)





end LCS.SLD.FirstOrder
end

noncomputable section
namespace LCS.SLD.FirstOrder.FOSLDDerivation
attribute [local instance] Classical.propDecidable
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm LCS.FOResolution.Method

/-- The linear input-resolution tree of a trace (SQ21). The left spine follows
    the trace; the right leaves are the original side-clause occurrences.
    Each node retains the trace's selected atoms, local renaming and MGU. -/
@[blueprint "chap9__definition_9_4_2"]
def toResolutionTree {L : Language} (hNoEq : L.withoutEquality)
    {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    FOSLDDerivation hNoEq D goals currentGoal → FOResolutionTree L hNoEq
  | .init goal _ => .axiom_ goal.toFOClause
  | .step prev clause _ _ Ak headA _ _ rho sigma _ _ =>
      .resolve (toResolutionTree hNoEq prev) (.axiom_ clause.toFOClause)
        [FOLiteralCore.neg Ak] [FOLiteralCore.pos headA] Term.var rho sigma

/-- Every trace has its linear input-resolution DAG over the same input union.
    Labels agree extensionally with the finite goal sets, and the final node
    is empty exactly for refutations (SQ16/SQ21). -/
@[attach_debt, blueprint "chap9__definition_9_4_2"]
theorem toResolutionDAG_exists {L : Language} (hNoEq : L.withoutEquality)
    {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    {currentGoal : LCS.Finset (FOAtom L hNoEq)}
    (d : FOSLDDerivation hNoEq D goals currentGoal) :
    ∃ graph : FOResolutionDAG L hNoEq,
      graph = [toResolutionTree hNoEq d] ∧
      FOResolutionDAG.isResolutionDAGFor hNoEq graph
        (fun C => ∃ c, (c ∈ D ∨ c ∈ goals) ∧ c.toFOClause = C) ∧
      LCS.Finset.ofList ((toResolutionTree hNoEq d).label hNoEq) =
        LCS.Finset.ofList (currentGoal.toList.map FOLiteralCore.neg) ∧
      ((toResolutionTree hNoEq d).label hNoEq = [] ↔ isRefutation hNoEq d)

end LCS.SLD.FirstOrder.FOSLDDerivation
end
