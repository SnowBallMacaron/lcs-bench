import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
import Attach
import LCS.Herbrand.SHGTheorem.Main.SHG.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution



-- ===================================================================
-- Theorem 7.6.1 (helper): c-instance source entails toFormula
-- ===================================================================

-- ATTACH-BLOCKER: termination suffix
/-- Helper theorem: A well-formed c-instance's source formula entails
its extracted `toFormula`. That is, for any structure `M` and
assignment `s`, if `M, s ⊨ ci.source`, then `M, s ⊨ ci.toFormula`.

Proof by structural recursion on `ci`:
- `atom B _` / `negAtom B _`: `source = toFormula` (= B or .neg B), so the
  implication is trivial (identity).
- `connective star C D H K`: `source = (C ⋆ D)` and `toFormula =
  (H.toFormula ⋆ K.toFormula)` where `⋆` is conj (star=true) or disj
  (star=false). WellFormed gives `H.source = C` and `K.source = D`. Then
  in the conjunction case, both operands evaluate to true, so by IH on
  `H` (with `M, s ⊨ C = H.source`) we get `M, s ⊨ H.toFormula`, and
  similarly for `K`; the conjunction `H.toFormula ⋆ K.toFormula` holds.
  The disjunction case is analogous.
- `forallInst x C t₀ h₀ tsRest hsRest _ _`: `source = ∀x C` and
  `toFormula` is the right-nested nonempty conjunction of `h₀.toFormula`
  and `(hsRest.map toFormula)`. If `M, s ⊨ ∀x C`, then for any `t` in
  `[t₀] ++ tsRest`, `M, s ⊨ C[t/x]` (via `formulaSubstEval_closed` using
  `t` being closed ⇒ `isFreeForN t x C` holds trivially, and specializing
  the universal with the value `termEval M s t`). Each `hsRest[i]` has
  `source = C[tsRest[i]/x]` by WellFormed, so by IH on each `hsRest[i]`
  (and on `h₀`) we get all `hsRest[i].toFormula` (and `h₀.toFormula`)
  hold at `s`. The conjunction chain holds by
  induction on the ordered suffix list. No model or assignment is changed
  when assembling the children into the right-nested conjunction. -/
theorem cInstance_source_entails_toFormula {L : Language}
    (ci : CInstance L) (hWF : CInstance.WellFormed ci)
    (M : Structure L) (s : Assignment M)
    (hSrc : formulaEvalN M ci.source s) :
    formulaEvalN M ci.toFormula s := by
-- BEGIN PROOF
  match ci with
  | .atom B hAtom =>
    -- source = B, toFormula = B
    simp only [CInstance.toFormula]
    simp only [CInstance.source] at hSrc
    exact hSrc
  | .negAtom B hAtom =>
    -- source = .neg B, toFormula = .neg B
    simp only [CInstance.toFormula]
    simp only [CInstance.source] at hSrc
    exact hSrc
  | .connective true C D H K =>
    -- source = .conj C D, toFormula = .conj H.toFormula K.toFormula
    simp only [CInstance.toFormula]
    simp only [CInstance.source] at hSrc
    -- hWF : H.source = C ∧ K.source = D ∧ WF H ∧ WF K
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSrcH, hSrcK, hWFH, hWFK⟩ := hWF
    have hEvalC : formulaEvalN M C s := hSrc.1
    have hEvalD : formulaEvalN M D s := hSrc.2
    refine ⟨?_, ?_⟩
    · have hH := cInstance_source_entails_toFormula H hWFH M s
      rw [hSrcH] at hH
      exact hH hEvalC
    · have hK := cInstance_source_entails_toFormula K hWFK M s
      rw [hSrcK] at hK
      exact hK hEvalD
  | .connective false C D H K =>
    -- source = .disj C D, toFormula = .disj H.toFormula K.toFormula
    simp only [CInstance.toFormula]
    simp only [CInstance.source] at hSrc
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSrcH, hSrcK, hWFH, hWFK⟩ := hWF
    -- hSrc : formulaEvalN M (FormulaN.disj C D) s = orM = C ∨ D.
    rcases hSrc with hC | hD
    · left
      have hH := cInstance_source_entails_toFormula H hWFH M s
      rw [hSrcH] at hH
      exact hH hC
    · right
      have hK := cInstance_source_entails_toFormula K hWFK M s
      rw [hSrcK] at hK
      exact hK hD
  | .forallInst x C t₀ h₀ tsRest hsRest hGround₀ hGroundRest =>
    -- The universal output is right-nested in the original child order.
    simp only [CInstance.toFormula]
    simp only [CInstance.source] at hSrc
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSrcH₀, hWFh₀, hWFList⟩ := hWF
    -- From hSrc : M, s ⊨ ∀x C, derive for every closed term t,
    -- M, s ⊨ C[t/x].
    have hAll : ∀ a : M.carrier,
        formulaEvalN M C (assignUpdate s x a) := hSrc
    -- Helper: for any closed term t, M, s ⊨ C[t/x].
    have hInst : ∀ (t : Term L),
        LCS.FirstOrder.Basic.Term.isClosed t →
        formulaEvalN M (formulaSubstN C t x) s := by
      intro t htClosed
      rw [formulaSubstEval_closed C t x htClosed s]
      exact hAll (termEval M s t)
    -- Specialize hInst to t₀.
    have hInst₀ : formulaEvalN M (formulaSubstN C t₀ x) s :=
      hInst t₀ hGround₀
    -- By WellFormed: h₀.source = C[t₀/x]. So M, s ⊨ h₀.source.
    have hSrcEval₀ : formulaEvalN M h₀.source s := by
      rw [hSrcH₀]; exact hInst₀
    -- IH on h₀.
    have hTo₀ : formulaEvalN M (CInstance.toFormula h₀) s :=
      cInstance_source_entails_toFormula h₀ hWFh₀ M s hSrcEval₀
    -- Now handle hsRest: we need ∀ f ∈ hsRest.map toFormula, M ⊨ f.
    have hRest : ∀ f ∈ hsRest.map CInstance.toFormula,
        formulaEvalN M f s := by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨h, hMem, heq⟩ := hf
      rw [← heq]
      -- Use WellFormedList to extract (t, h.source = C[t/x], h WF, t closed).
      have hPair : ∃ t ∈ tsRest,
          h.source = formulaSubstN C t x ∧
          CInstance.WellFormed h ∧
          LCS.FirstOrder.Basic.Term.isClosed t := by
        clear heq hSrc hAll hInst hInst₀ hSrcEval₀ hTo₀
        -- Walk tsRest and hsRest in parallel.
        revert hsRest hGroundRest hWFList hMem
        induction tsRest with
        | nil =>
          intro hsRest hGroundRest hWFList hMem
          cases hsRest with
          | nil => exact absurd hMem (by simp)
          | cons _ _ =>
            simp only [CInstance.WellFormedList] at hWFList
        | cons t ts ih =>
          intro hsRest hGroundRest hWFList hMem
          cases hsRest with
          | nil =>
            simp only [CInstance.WellFormedList] at hWFList
          | cons h' hs' =>
            simp only [CInstance.WellFormedList] at hWFList
            obtain ⟨hSrc', hWFh', hWFList'⟩ := hWFList
            rcases List.mem_cons.mp hMem with heq' | hMemRest
            · -- h = h'
              refine ⟨t, ?_, ?_, ?_, ?_⟩
              · exact List.mem_cons_self
              · rw [heq']; exact hSrc'
              · rw [heq']; exact hWFh'
              · exact hGroundRest t List.mem_cons_self
            · have hGroundRest' : ∀ t' ∈ ts,
                  LCS.FirstOrder.Basic.Term.isClosed t' := by
                intro t' ht'
                exact hGroundRest t' (List.mem_cons_of_mem _ ht')
              obtain ⟨t', ht'Mem, hSrc'', hWF'', hClosed''⟩ :=
                ih hs' hGroundRest' hWFList' hMemRest
              exact ⟨t', List.mem_cons_of_mem _ ht'Mem,
                     hSrc'', hWF'', hClosed''⟩
      obtain ⟨t, _htMem, hhSrc, hhWF, hhClosed⟩ := hPair
      have hSrcEvalh : formulaEvalN M h.source s := by
        rw [hhSrc]; exact hInst t hhClosed
      exact cInstance_source_entails_toFormula h hhWF M s hSrcEvalh
    have hFold : ∀ (fs : List (FormulaN L)) (first : FormulaN L),
        formulaEvalN M first s →
        (∀ f ∈ fs, formulaEvalN M f s) →
        formulaEvalN M
          (fs.foldr (fun f rest first => FormulaN.conj first (rest f)) id first) s := by
      intro fs
      induction fs with
      | nil => intro first hFirst _; exact hFirst
      | cons f fs ih =>
          intro first hFirst hFs
          exact ⟨hFirst, ih f (hFs f (by simp))
            (fun g hg => hFs g (List.mem_cons_of_mem f hg))⟩
    exact hFold (hsRest.map CInstance.toFormula) h₀.toFormula hTo₀ hRest
termination_by sizeOf ci
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | (simp_wf
       have := List.sizeOf_lt_of_mem hMem
       omega)

-- ===================================================================
-- Theorem 7.6.1 (companion, part a): shgTheorem_unsat
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.HornEncoding.Proofs
/-- Internal closed-seed core of Theorem 7.6.1(a). The backward
    implication is seed-independent; the forward implication threads
    the caller's exact closed term through the Herbrand construction. -/
theorem shgTheorem_unsat_seed {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t}) :
    ¬ satisfiableN A ↔
      ∃ (C : FormulaN spec.language)
        (ci : CInstance spec.language),
        ci.source = SK spec ∧ ci.toFormula = C ∧
        CInstance.WellFormed ci ∧
        ¬ satisfiableN C := by
-- BEGIN PROOF
  constructor
  · intro hUnsat
    let ci := shg_unsat_cinstance_seed spec A hSource seed hUnsat
    obtain ⟨hSrc, hWF, hC⟩ :=
      shg_unsat_cinstance_seed_spec spec A hSource seed hUnsat
    exact ⟨ci.toFormula, ci, hSrc, rfl, hWF, hC⟩
  · rintro ⟨C, ci, hSrcCi, hToF, hWF, hUnsatC⟩
    intro hSatA
    apply hUnsatC
    have hSatSK : satisfiableN (SK spec) :=
      (skolem_form_sat_iff spec A hSource (SK spec) rfl).mp hSatA
    obtain ⟨M, sN, hEvalSK⟩ := hSatSK
    refine ⟨M, sN, ?_⟩
    rw [← hToF]
    have hEvalSrc : formulaEvalN M ci.source sN := by
      rw [hSrcCi]
      exact hEvalSK
    exact cInstance_source_entails_toFormula ci hWF M sN hEvalSrc

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.SLD.FirstOrder.HornEncoding
/-- Theorem 7.6.1(a): for the rectified NNF sentence A fixed by
spec.source, A is unsatisfiable iff some well-formed c-instance C of SK spec
is unsatisfiable. Both C and its instance data live in spec.language, with
the repaired Skolem constants and ordered right-nested universal output.
The standing base-language constant assumption supplies a closed seed.
The converse uses source entailment and Skolem satisfiability preservation. -/
theorem shgTheorem_unsat {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    ¬ satisfiableN A ↔
      ∃ (C : FormulaN spec.language)
        (ci : CInstance spec.language),
        ci.source = SK spec ∧ ci.toFormula = C ∧
        CInstance.WellFormed ci ∧
        ¬ satisfiableN C := by
-- BEGIN PROOF
  constructor
  · intro hUnsat
    let ci := shg_unsat_cinstance spec A hSource hConst hUnsat
    obtain ⟨hSrc, hWF, hC⟩ :=
      shg_unsat_cinstance_spec spec A hSource hConst hUnsat
    exact ⟨ci.toFormula, ci, hSrc, rfl, hWF, hC⟩
  · -- Backward: ∃ C ci, ci.source = SK spec ∧ ci.toFormula = C ∧
    --          ci.WellFormed ∧ ¬ satisfiableN C  →  ¬ satisfiableN A.
    rintro ⟨C, ci, hSrcCi, hToF, hWF, hUnsatC⟩
    -- Assume satisfiableN A for contradiction.
    intro hSatA
    apply hUnsatC
    -- satisfiableN A ↔ satisfiableN (SK spec) by Lemma 7.6.3.
    have hSatSK : satisfiableN (SK spec) :=
      (skolem_form_sat_iff spec A hSource (SK spec) rfl).mp hSatA
    -- Unpack: M, sN with M ⊨ SK spec.
    obtain ⟨M, sN, hEvalSK⟩ := hSatSK
    refine ⟨M, sN, ?_⟩
    -- We want: formulaEvalN M C sN. Use C = ci.toFormula and
    -- ci.source = SK spec.
    rw [← hToF]
    -- From hEvalSK : M, sN ⊨ SK spec, and hSrcCi : ci.source = SK spec,
    -- get M, sN ⊨ ci.source.
    have hEvalSrc : formulaEvalN M ci.source sN := by
      rw [hSrcCi]; exact hEvalSK
    exact cInstance_source_entails_toFormula ci hWF M sN hEvalSrc

-- ===================================================================
-- Theorem 7.6.1 (companion, part b): shgTheorem_effective
-- ===================================================================



-- ===================================================================
-- Theorem 7.6.1 (Skolem-Herbrand-Godel): shgTheorem
-- ===================================================================

/-- Theorem 7.6.1 (Skolem-Herbrand-Godel, after Andrews): for the
rectified NNF sentence A and fixed Skolem form SK spec, (a) A is unsatisfiable
iff a well-formed compound instance is unsatisfiable, and (b) provability
of A -> gives a quantifier-free compound instance C for which C -> is
provable in the corresponding G1nnf or G1nnf= system over spec.language.
Part (b) specifies the result of effective formula production; its algorithm
remains deferred under OD-A17. The two language branches assert provability
of not C, rather than an additional proof-output algorithm. -/
@[blueprint "chap7__theorem_7_6_1" (main := true)]
theorem shgTheorem {L : Language}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    (¬ satisfiableN A ↔
      ∃ (C : FormulaN spec.language)
        (ci : CInstance spec.language),
        ci.source = SK spec ∧ ci.toFormula = C ∧
        CInstance.WellFormed ci ∧
        ¬ satisfiableN C) ∧
    (∀ hL : L.withoutEquality,
      LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hL
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        G1nnfProvableSet (L := spec.language)
          (show spec.language.withoutEquality from hL)
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) ∧
    (∀ (hL : L.hasEquality = true),
      LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set hL
          (({A} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set
          (L := spec.language) hL
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) 

-- ===================================================================
-- Section 7.6.1: validity/unsatisfiability formulation transfer
-- ===================================================================



/-- Section 7.6.1: an unsatisfiability formulation for not A yields a
validity formulation for A, with the same chosen Skolem form and the
negations of its compound instances as valid witnesses. A may be open.
The formulation hypothesis supplies the correspondence to spec; no equality
between A and a closed or normalized source formula is assumed. -/
@[blueprint "chap7__theorem_7_6_1"]
theorem shgUnsatisfiability_to_validity {L : Language}
    (A : FormulaN L) (spec : SkolemSpec L)
    (hUnsatVersion : ¬ satisfiableN (.neg A) ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ ¬ satisfiableN C) :
    universallyValidN A ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ universallyValidN (.neg C) 

/-- Section 7.6.1, converse transfer: a validity formulation for not A
with negated compound-instance witnesses yields the unsatisfiability
formulation for A. Both the Skolem form and the underlying compound
instances are preserved. A may be open; the hypothesis is a mathematical
formulation, not an encoding of a theorem or an extraction algorithm. -/
@[blueprint "chap7__theorem_7_6_1"]
theorem shgValidity_to_unsatisfiability {L : Language}
    (A : FormulaN L) (spec : SkolemSpec L)
    (hValidVersion : universallyValidN (.neg A) ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ universallyValidN (.neg C)) :
    ¬ satisfiableN A ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ ¬ satisfiableN C 



-- ===================================================================
-- Corollary 7.6.1 (companion def): applyGroundSubstitution
-- ===================================================================

/-- Corollary 7.6.1 (companion def): Applies a list of (variable, closed-term) pairs as a sequential substitution to a formula M. Each pair (xᵢ, tᵢ) contributes a single-variable substitution M[tᵢ/xᵢ], composed left-to-right. When applied to the matrix of a prenex ∀-formula with the closed terms matching the bound variables of the universal prefix, this produces a single ground substitution instance of the matrix. -/
@[blueprint "chap7__theorem_7_6_1"]
def applyGroundSubstitution {L : Language}
    (M : FormulaN L) (substs : List (Nat × Term L)) : FormulaN L :=
  substs.foldl (fun acc p => formulaSubstN acc p.2 p.1) M





-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- Skolemization preserves a prenex source's prefix shape while
eliminating every existential prefix entry. -/
theorem skolemForm_universalPrenex_of_source_prenex
    {L : Language} (spec : SkolemSpec L)
    (hPrenex : isPrenex spec.source) :
    UniversalPrenexFormula (SK spec) := by
  have hLiftQF :
      ∀ A : FormulaN L,
        FirstOrder.SemanticsN.isQuantifierFree A →
        FirstOrder.SemanticsN.isQuantifierFree
          (liftFormulaSkolem
            (skolemRank := spec.skolemRank) A) := by
    intro A hQF
    induction A with
    | predN _ _ => trivial
    | eq_ _ _ _ => trivial
    | neg A ih => exact ih hQF
    | conj A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | disj A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | impl A B ihA ihB =>
      exact ⟨ihA hQF.1, ihB hQF.2⟩
    | all _ _ => exact hQF.elim
    | ex _ _ => exact hQF.elim
  have hLiftPrenex :
      ∀ A : FormulaN L,
        isPrenex A →
        isPrenex
          (liftFormulaSkolem
            (skolemRank := spec.skolemRank) A) := by
    intro A hA
    induction A with
    | predN _ _ => exact hA
    | eq_ _ _ _ => exact hA
    | neg A _ => exact hLiftQF (.neg A) hA
    | conj A B _ _ => exact hLiftQF (.conj A B) hA
    | disj A B _ _ => exact hLiftQF (.disj A B) hA
    | impl A B _ _ => exact hLiftQF (.impl A B) hA
    | all _ A ih => exact ih hA
    | ex _ A ih => exact ih hA
  have hQFDescriptorCount :
      ∀ A : FormulaN spec.language,
        FirstOrder.SemanticsN.isQuantifierFree A →
        skolemDescriptorCount A = 0 := by
    intro A hQF
    induction A with
    | predN _ _ => rfl
    | eq_ _ _ _ => rfl
    | neg _ _ => rfl
    | conj A B ihA ihB =>
      simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
    | disj A B ihA ihB =>
      simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
    | impl _ _ _ _ => rfl
    | all _ _ => exact hQF.elim
    | ex _ _ => exact hQF.elim
  have hTraversalPrenex :
      ∀ (m : Nat) (A : FormulaN spec.language)
        (scope : List Nat) (indices : List (Fin spec.n))
        (B : FormulaN spec.language) (used : Nat),
        formulaQuantCount A = m →
        isPrenex A →
        indices.length = skolemDescriptorCount A →
        skolemFormExactAux spec A scope indices =
          some (B, used) →
        isPrenex B := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro A scope indices B used hCount hAPrenex hLength hRun
      cases A with
      | predN P ts =>
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (by
            simpa [skolemDescriptorCount] using hLength)
        subst indices
        simp only [skolemFormExactAux] at hRun
        cases hRun
        exact trivial
      | eq_ hEq t₁ t₂ =>
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (by
            simpa [skolemDescriptorCount] using hLength)
        subst indices
        simp only [skolemFormExactAux] at hRun
        cases hRun
        exact trivial
      | neg C =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.neg C) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.neg C) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.neg C) scope hZero
        have hEq : B = FormulaN.neg C :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | conj C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.conj C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.conj C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.conj C D) scope hZero
        have hEq : B = FormulaN.conj C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | disj C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.disj C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.disj C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.disj C D) scope hZero
        have hEq : B = FormulaN.disj C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | impl C D =>
        have hQF :
            FirstOrder.SemanticsN.isQuantifierFree
              (FormulaN.impl C D) :=
          hAPrenex
        have hZero :=
          hQFDescriptorCount (.impl C D) hQF
        have hNil : indices = [] :=
          List.length_eq_zero_iff.mp (hLength.trans hZero)
        subst indices
        have hSelf :=
          skolemFormExactAux_eq_self_of_descriptorCount_zero
            spec (.impl C D) scope hZero
        have hEq : B = FormulaN.impl C D :=
          skolemFormExactAux_formula_unique hRun hSelf
        subst B
        exact hQF
      | all x C =>
        have hCountC : formulaQuantCount C < m := by
          simp [formulaQuantCount] at hCount
          omega
        have hLengthC :
            indices.length = skolemDescriptorCount C := by
          simpa [skolemDescriptorCount] using hLength
        have hRunTop := hRun
        simp only [skolemFormExactAux] at hRun
        generalize hRec :
            skolemFormExactAux spec C
              (scope ++ [x]) indices = rec at hRun
        cases rec with
        | none =>
          simp at hRun
        | some result =>
          obtain ⟨C', used'⟩ := result
          have hWrapped :
              skolemFormExactAux spec
                  (FormulaN.all x C) scope indices =
                some (FormulaN.all x C', used') := by
            simp [skolemFormExactAux, hRec]
          have hB : B = FormulaN.all x C' :=
            skolemFormExactAux_formula_unique hRunTop hWrapped
          subst B
          exact
            ih (formulaQuantCount C) hCountC C
              (scope ++ [x]) indices C' used' rfl
              hAPrenex hLengthC hRec
      | ex x C =>
        cases indices with
        | nil =>
          have hImpossible :
              0 = 1 + skolemDescriptorCount C := by
            simpa only [List.length_nil,
              skolemDescriptorCount] using hLength
          omega
        | cons i rest =>
          have hCountSub :
              formulaQuantCount
                  (formulaSubstN C
                    (exactSkolemTerm spec i) x) < m := by
            rw [formulaSubst_quantCount]
            simp [formulaQuantCount] at hCount
            omega
          have hLengthRest :
              rest.length =
                skolemDescriptorCount
                  (formulaSubstN C
                    (exactSkolemTerm spec i) x) := by
            rw [formulaSubstN_descriptorCount]
            simp only [List.length_cons,
              skolemDescriptorCount] at hLength
            omega
          have hPrenexSub :
              isPrenex
                (formulaSubstN C
                  (exactSkolemTerm spec i) x) :=
            isPrenex_formulaSubstN C
              (exactSkolemTerm spec i) x hAPrenex
          have hRunTop := hRun
          simp only [skolemFormExactAux, skolemSubst] at hRun
          generalize hRec :
              skolemFormExactAux spec
                (formulaSubstN C
                  (exactSkolemTerm spec i) x)
                scope rest = rec at hRun
          cases rec with
          | none =>
            simp at hRun
          | some result =>
            obtain ⟨C', used'⟩ := result
            have hWrapped :
                skolemFormExactAux spec
                    (FormulaN.ex x C) scope (i :: rest) =
                  some (C', used' + 1) := by
              simp [skolemFormExactAux, skolemSubst, hRec]
            have hB : B = C' :=
              skolemFormExactAux_formula_unique hRunTop hWrapped
            subst B
            exact
              ih _ hCountSub _ scope rest C' used' rfl
                hPrenexSub hLengthRest hRec
  let lifted :=
    liftFormulaSkolem
      (skolemRank := spec.skolemRank) spec.source
  have hLiftedPrenex : isPrenex lifted :=
    hLiftPrenex spec.source hPrenex
  have hSKPrenex : isPrenex (SK spec) :=
    hTraversalPrenex
      (formulaQuantCount lifted) lifted [] spec.indices
      (SK spec) spec.n rfl hLiftedPrenex
      spec.indices_length_eq_lifted_descriptorCount
      (skolemFormExactAux_top_formula_result spec)
  have hUniversalPrefix :
      ∀ B : FormulaN spec.language,
        isSkolemNormalFormShape B →
        ∀ p, p ∈ prenexPrefix B →
          p.1 = QuantifierKind.universal := by
    intro B
    induction B with
    | predN _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | eq_ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | neg _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | conj _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | disj _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | impl _ _ _ _ =>
      intro _ p hp
      simp [prenexPrefix] at hp
    | all x C ih =>
      intro hShape p hp
      simp only [prenexPrefix, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih hShape p hp
    | ex _ _ _ =>
      intro hShape
      exact hShape.elim
  exact
    ⟨hSKPrenex,
      hUniversalPrefix (SK spec)
        (skolemForm_isSkolemNormalForm' spec).1⟩

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- Exact ordered substitution of every universal prefix binder by a
closed term closes the matrix of a closed universal-prenex source.
Distinct bindings ensure that stripping the current binder commutes
with substitution into the remaining prefix. -/
theorem applyGroundSubstitution_isClosed_of_fullPrefix
    {L : Language} (source : FormulaN L)
    (substitutions : List (Nat × Term L))
    (hComplete :
      substitutions.map Prod.fst =
        (prenexPrefix source).map Prod.snd)
    (hTermsClosed :
      ∀ p ∈ substitutions, Term.isClosed p.2)
    (hSourceClosed : FormulaN.isClosed source)
    (hUniversal : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source) :
    FormulaN.isClosed
      (applyGroundSubstitution
        (prenexMatrix source) substitutions) := by
  have hClose :
      ∀ (m : Nat) (current : FormulaN L)
        (remaining : List (Nat × Term L)),
        formulaQuantCount current = m →
        remaining.map Prod.fst =
          (prenexPrefix current).map Prod.snd →
        (∀ p ∈ remaining, Term.isClosed p.2) →
        FormulaN.isClosed current →
        UniversalPrenexFormula current →
        distinctQuantifierBindings current →
        FormulaN.isClosed
          (applyGroundSubstitution
            (prenexMatrix current) remaining) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro current remaining hCount hKeys hClosedTerms
        hCurrentClosed hCurrentUniversal hCurrentDistinct
      cases current with
      | predN P ts =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | eq_ hEq t₁ t₂ =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | neg C =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | conj C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | disj C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | impl C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | all x C =>
        cases remaining with
        | nil =>
          simp [prenexPrefix] at hKeys
        | cons head rest =>
          obtain ⟨key, term⟩ := head
          simp only [List.map_cons, Prod.fst, prenexPrefix,
            Prod.snd] at hKeys
          have hKey : key = x :=
            (List.cons.inj hKeys).1
          have hRestKeys :
              rest.map Prod.fst =
                (prenexPrefix C).map Prod.snd :=
            (List.cons.inj hKeys).2
          subst key
          have hTermClosed : Term.isClosed term :=
            hClosedTerms (x, term) List.mem_cons_self
          have hRestClosed :
              ∀ p ∈ rest, Term.isClosed p.2 := by
            intro p hp
            exact hClosedTerms p
              (List.mem_cons.mpr (Or.inr hp))
          have hSubClosed :
              FormulaN.isClosed
                (formulaSubstN C term x) := by
            have hSourceFV :
                formulaFVN (FormulaN.all x C) =
                  (∅ : Set Nat) :=
              hCurrentClosed
            have hTermFV :
                termFV term = (∅ : Set Nat) :=
              hTermClosed
            unfold FormulaN.isClosed
            funext y
            apply propext
            constructor
            · intro hy
              rcases
                  LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
                    C term x y hy with
                ⟨hyC, hyNe⟩ | hyTerm
              · have hySource :
                    y ∈ formulaFVN
                      (FormulaN.all x C) :=
                  ⟨hyC, hyNe⟩
                rw [hSourceFV] at hySource
                exact hySource.elim
              · rw [hTermFV] at hyTerm
                exact hyTerm.elim
            · intro hy
              exact hy.elim
          have hBodyUniversal :
              UniversalPrenexFormula C :=
            universalPrenexFormula_body_of_all
              C x hCurrentUniversal
          have hSubUniversal :
              UniversalPrenexFormula
                (formulaSubstN C term x) :=
            universalPrenexFormula_formulaSubstN
              C term x hBodyUniversal
          have hSubDistinct :
              distinctQuantifierBindings
                (formulaSubstN C term x) :=
            Herbrand.distinctQuantifierBindings_of_formulaSubstN
              C term x hCurrentDistinct.1
          have hSubCount :
              formulaQuantCount
                  (formulaSubstN C term x) =
                formulaQuantCount C :=
            formulaSubst_quantCount C term x
          have hSubLt :
              formulaQuantCount
                  (formulaSubstN C term x) < m := by
            rw [hSubCount]
            simp [formulaQuantCount] at hCount
            omega
          have hRestKeysSub :
              rest.map Prod.fst =
                (prenexPrefix
                  (formulaSubstN C term x)).map Prod.snd := by
            rw [prenexPrefix_formulaSubstN]
            exact hRestKeys
          have hClosedRest :=
            ih
              (formulaQuantCount
                (formulaSubstN C term x))
              hSubLt (formulaSubstN C term x) rest rfl
              hRestKeysSub hRestClosed hSubClosed
              hSubUniversal hSubDistinct
          have hMatrix :
              prenexMatrix (formulaSubstN C term x) =
                formulaSubstN (prenexMatrix C) term x :=
            Herbrand.prenexMatrix_formulaSubstN_of_not_bv
              C term x hCurrentDistinct.2
          rw [hMatrix] at hClosedRest
          simpa only [prenexMatrix, applyGroundSubstitution,
            List.foldl_cons] using hClosedRest
      | ex x C =>
        have hImpossible :
            QuantifierKind.existential =
              QuantifierKind.universal :=
          hCurrentUniversal.2
            (QuantifierKind.existential, x)
            (by simp [prenexPrefix])
        cases hImpossible
  exact
    hClose (formulaQuantCount source) source substitutions rfl
      hComplete hTermsClosed hSourceClosed hUniversal hDistinct

-- ===================================================================
-- Corollary 7.6.1 (companion structure): GroundMatrixInstance
-- ===================================================================

/-- A proof-coupled ground instance of the matrix of `B`.

The substitution keys cover the prenex prefix exactly, in
outermost-to-innermost order. Every replacement term is closed, and the
computed matrix instance is recorded as closed. The latter condition also
rejects residual free variables which do not belong to the prefix. -/
@[blueprint "chap7__theorem_7_6_1"]
structure GroundMatrixInstance {L : Language} (B : FormulaN L) where
  substitution : List (Nat × Term L)
  complete :
    substitution.map Prod.fst =
      (LCS.Herbrand.PrenexForm.prenexPrefix B).map Prod.snd
  termsClosed :
    ∀ p ∈ substitution, Term.isClosed p.2
  leafClosed :
    FormulaN.isClosed
      (applyGroundSubstitution
        (LCS.Herbrand.PrenexForm.prenexMatrix B)
        substitution)

end LCS.Herbrand.SHGTheorem.Main
end

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution
namespace GroundMatrixInstance

/-- The formula carried by one complete ground matrix instance. -/
@[blueprint "chap7__theorem_7_6_1"]
def toFormula {L : Language} {B : FormulaN L}
    (g : GroundMatrixInstance B) : FormulaN L :=
  applyGroundSubstitution
    (LCS.Herbrand.PrenexForm.prenexMatrix B)
    g.substitution



end GroundMatrixInstance
end LCS.Herbrand.SHGTheorem.Main
end

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

/-- Proof-relevant flattening of a binary conjunction into its ordered
leaves. The `leaf` constructor may stop at any formula, so a conjunction
which is itself one matrix instance is not split accidentally. The `conj`
constructor preserves order and multiplicity while allowing either binary
bracketing of the same leaf list. -/
@[blueprint "chap7__theorem_7_6_1"]
inductive ConjunctionFlattening {L : Language} :
    FormulaN L → List (FormulaN L) → Prop where
  | leaf (A : FormulaN L) :
      ConjunctionFlattening A [A]
  | conj {A B : FormulaN L} {as bs : List (FormulaN L)} :
      ConjunctionFlattening A as →
      ConjunctionFlattening B bs →
      ConjunctionFlattening (.conj A B) (as ++ bs)

end LCS.Herbrand.SHGTheorem.Main
end

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution
namespace ConjunctionFlattening

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A conjunction flattening always has at least one leaf. -/
theorem nonempty {L : Language} {F : FormulaN L}
    {leaves : List (FormulaN L)}
    (flattening : ConjunctionFlattening F leaves) :
    leaves ≠ [] := by
  induction flattening with
  | leaf A => exact List.cons_ne_nil A []
  | conj _ _ nonemptyLeft _ =>
    intro hEmpty
    exact nonemptyLeft (List.append_eq_nil_iff.mp hEmpty).1



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Evaluation of a represented conjunction is equivalent to evaluation
of every leaf in its ordered list. -/
theorem formulaEvalN_iff_all_leaves {L : Language}
    {F : FormulaN L} {leaves : List (FormulaN L)}
    (flattening : ConjunctionFlattening F leaves)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M F s ↔
      ∀ A ∈ leaves, formulaEvalN M A s := by
  induction flattening with
  | leaf A =>
    constructor
    · intro hA C hC
      simp only [List.mem_singleton] at hC
      subst C
      exact hA
    · intro hAll
      exact hAll A List.mem_cons_self
  | @conj A B as bs flatteningA flatteningB evalA evalB =>
    simp only [formulaEvalN]
    constructor
    · rintro ⟨hA, hB⟩ C hC
      rcases List.mem_append.mp hC with hCA | hCB
      · exact (evalA.mp hA) C hCA
      · exact (evalB.mp hB) C hCB
    · intro hAll
      exact
        ⟨evalA.mpr (fun C hC =>
            hAll C (List.mem_append.mpr (Or.inl hC))),
         evalB.mpr (fun C hC =>
            hAll C (List.mem_append.mpr (Or.inr hC)))⟩







end ConjunctionFlattening
end LCS.Herbrand.SHGTheorem.Main
end

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

/-- Corollary 7.6.1 (companion def): `F` is a nonempty finite
conjunction of complete, ordered, closed ground substitution instances of
the matrix of the universal-prenex NNF formula `B`. Distinct quantifier
bindings make the sequential prefix positions unambiguous. The
proof-relevant flattening preserves leaf order and multiplicity but does
not impose one global conjunction association. -/
@[blueprint "chap7__theorem_7_6_1"]
def isFiniteGroundConjunctionOfMatrix {L : Language}
    (F : FormulaN L) (B : FormulaN L) : Prop :=
  LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula B ∧
  FormulaN.isNNF B ∧
  LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings B ∧
  ∃ instances : List (GroundMatrixInstance B),
    ConjunctionFlattening F
      (instances.map GroundMatrixInstance.toFormula)

-- ===================================================================
-- Theorem 7.6.1: CInstance-to-ground-conjunction bridge
-- ===================================================================

/- Enumerate the complete substitution paths represented by a
`CInstance`. A non-universal root contributes exactly the singleton
empty path: in particular, a quantifier-free conjunctive matrix remains
one matrix leaf rather than being split into its connective children.
At a universal node, every child path is retained in constructor order
and extended by the current binder and its chosen closed term. -/
-- ATTACH-BLOCKER: mutual
mutual
def cInstanceGroundSubstitutionPaths {L : Language} :
    CInstance L → List (List (Nat × Term L))
  | .forallInst x _ t₀ h₀ tsRest hsRest _ _ =>
    (cInstanceGroundSubstitutionPaths h₀).map
        (fun path => (x, t₀) :: path) ++
      cInstanceGroundSubstitutionPathsList x tsRest hsRest
  | _ => [[]]

def cInstanceGroundSubstitutionPathsList {L : Language}
    (x : Nat) :
    List (Term L) → List (CInstance L) →
      List (List (Nat × Term L))
  | [], _ => []
  | _ :: _, [] => []
  | t :: tsRest, h :: hsRest =>
    (cInstanceGroundSubstitutionPaths h).map
        (fun path => (x, t) :: path) ++
      cInstanceGroundSubstitutionPathsList x tsRest hsRest
end

-- ATTACH-BLOCKER: private declaration
private theorem cInstanceGroundSubstitutionPaths_ne_nil
    {L : Language} :
    ∀ ci : CInstance L,
      cInstanceGroundSubstitutionPaths ci ≠ []
  | .atom _ _ => by
    simp [cInstanceGroundSubstitutionPaths]
  | .negAtom _ _ => by
    simp [cInstanceGroundSubstitutionPaths]
  | .connective _ _ _ _ _ => by
    simp [cInstanceGroundSubstitutionPaths]
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest => by
    have hHead :=
      cInstanceGroundSubstitutionPaths_ne_nil h₀
    cases hPaths : cInstanceGroundSubstitutionPaths h₀ with
    | nil =>
      exact absurd hPaths hHead
    | cons path paths =>
      simp [cInstanceGroundSubstitutionPaths, hPaths]

/- Every term recorded in an enumerated substitution path is one of the
closed choices carried by a `forallInst` constructor. -/
-- ATTACH-BLOCKER: mutual
mutual
theorem cInstanceGroundSubstitutionPaths_termsClosed
    {L : Language} :
    ∀ (ci : CInstance L)
      (path : List (Nat × Term L)),
      path ∈ cInstanceGroundSubstitutionPaths ci →
      ∀ p ∈ path, Term.isClosed p.2
  | .atom _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .negAtom _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .connective _ _ _ _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround₀
      · exact
          cInstanceGroundSubstitutionPaths_termsClosed
            h₀ tail hTail p hp
    · exact
        cInstanceGroundSubstitutionPathsList_termsClosed
          x tsRest hsRest hGroundRest path hRest

private theorem cInstanceGroundSubstitutionPathsList_termsClosed
    {L : Language} (x : Nat) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      (∀ t ∈ ts, Term.isClosed t) →
      ∀ path ∈
          cInstanceGroundSubstitutionPathsList x ts hs,
        ∀ p ∈ path, Term.isClosed p.2
  | [], _, _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | _ :: _, [], _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | t :: tsRest, h :: hsRest, hGround, path, hPath => by
    simp only [cInstanceGroundSubstitutionPathsList,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround t List.mem_cons_self
      · exact
          cInstanceGroundSubstitutionPaths_termsClosed
            h tail hTail p hp
    · exact
        cInstanceGroundSubstitutionPathsList_termsClosed
          x tsRest hsRest
          (fun t' ht' =>
            hGround t' (List.mem_cons_of_mem _ ht'))
          path hRest
end

/- Well-formedness aligns every enumerated path with the exact ordered
universal prefix of the represented source. -/
-- ATTACH-BLOCKER: mutual
mutual
theorem cInstanceGroundSubstitutionPaths_complete
    {L : Language} :
    ∀ (ci : CInstance L),
      CInstance.WellFormed ci →
      UniversalPrenexFormula ci.source →
      ∀ path ∈ cInstanceGroundSubstitutionPaths ci,
        path.map Prod.fst =
          (prenexPrefix ci.source).map Prod.snd
  | .atom B hAtom, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simpa [CInstance.source] using
      Herbrand.isQuantifierFree_prenexPrefix_eq_nil
        B (isAtomic_isQuantifierFree B hAtom)
  | .negAtom B hAtom, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp [CInstance.source, prenexPrefix]
  | .connective star C D H K, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    cases star <;> simp [CInstance.source, prenexPrefix]
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest, hWF, hUniversal, path, hPath => by
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSource₀, hWF₀, hWFRest⟩ := hWF
    change
      UniversalPrenexFormula (FormulaN.all x C)
        at hUniversal
    have hBodyUniversal :
        UniversalPrenexFormula C :=
      universalPrenexFormula_body_of_all
        C x hUniversal
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · have hChildUniversal :
          UniversalPrenexFormula h₀.source := by
        rw [hSource₀]
        exact
          universalPrenexFormula_formulaSubstN
            C t₀ x hBodyUniversal
      have hTailComplete :=
        cInstanceGroundSubstitutionPaths_complete
          h₀ hWF₀ hChildUniversal tail hTail
      rw [hSource₀, prenexPrefix_formulaSubstN]
        at hTailComplete
      simpa [CInstance.source, prenexPrefix] using
        congrArg (List.cons x) hTailComplete
    · exact
        cInstanceGroundSubstitutionPathsList_complete
          x C hBodyUniversal tsRest hsRest hWFRest
          path hRest

private theorem cInstanceGroundSubstitutionPathsList_complete
    {L : Language} (x : Nat) (C : FormulaN L)
    (hBodyUniversal : UniversalPrenexFormula C) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      CInstance.WellFormedList x C ts hs →
      ∀ path ∈
          cInstanceGroundSubstitutionPathsList x ts hs,
        path.map Prod.fst =
          (prenexPrefix (FormulaN.all x C)).map Prod.snd
  | [], [], _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | [], _ :: _, hWF, _, _ => by
    exact hWF.elim
  | _ :: _, [], hWF, _, _ => by
    exact hWF.elim
  | t :: tsRest, h :: hsRest, hWF, path, hPath => by
    simp only [CInstance.WellFormedList] at hWF
    obtain ⟨hSource, hWFHead, hWFTail⟩ := hWF
    simp only [cInstanceGroundSubstitutionPathsList,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · have hChildUniversal :
          UniversalPrenexFormula h.source := by
        rw [hSource]
        exact
          universalPrenexFormula_formulaSubstN
            C t x hBodyUniversal
      have hTailComplete :=
        cInstanceGroundSubstitutionPaths_complete
          h hWFHead hChildUniversal tail hTail
      rw [hSource, prenexPrefix_formulaSubstN]
        at hTailComplete
      simpa [prenexPrefix] using
        congrArg (List.cons x) hTailComplete
    · exact
        cInstanceGroundSubstitutionPathsList_complete
          x C hBodyUniversal tsRest hsRest hWFTail
          path hRest
end

end LCS.Herbrand.SHGTheorem.Main
end

