import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
import Attach
import LCS.Herbrand.SHGTheorem.Main.SkolemHerbrandGodel.ProofsStamp

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
-- Theorem 7.6.1 (part a, helper): g1nnf_provable_of_unsat
-- ===================================================================

/-- Completeness bridge for an unsatisfiable formula in a language without
 equality: the singleton antecedent sequent is G1nnf-provable. -/
theorem g1nnf_provable_of_unsat {L : Language}
    (hL : L.withoutEquality)
    (A : FormulaN L)
    (_hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  -- DEBT(completeness bridge: an unsatisfiable sentence of an equality-free language has a G1nnf proof of A →; pre-existing placeholder, chapter 7 proof-closing pass)
  sorry

/-- Completeness bridge for an unsatisfiable formula in a language with
 equality: the singleton antecedent sequent is G1nnf=-provable. -/
theorem g1nnfEq_provable_of_unsat {L : Language}
    (hL : L.hasEquality = true)
    (A : FormulaN L)
    (_hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  -- REPAIR(T6-21d): proof pending (G1nnf= completeness for the SHG with-equality case)
  sorry

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- No-equality, closed-NNF completeness bridge for a singleton
antecedent.  The closedness hypothesis discharges the cross-formula
free/bound-variable condition of `g1nnf_completeness`; the resulting
set-level derivation is converted to the indexed proof-tree presentation
consumed by the Chapter 7/8 Herbrand infrastructure. -/
theorem g1nnf_provable_of_unsat_closed_nnf_noeq {L : Language}
    [DecidableEq (FormulaN L)]
    (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (hNNF : FormulaN.isNNF A)
    (hClosed : FormulaN.isClosed A)
    (hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hNoEq
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  let s : G1nnfSequent L hNoEq :=
    { ante := fun F => F = A
      succ := Set.empty
      ante_nnf := by
        intro F hF
        exact hF ▸ hNNF
      succ_nnf := by
        intro F hF
        exact hF.elim
      ante_finite := ⟨[A], fun F => by simp⟩
      succ_finite := Set.Finite.empty }
  have hsValid : s.isValid := by
    intro M σ hAnte
    exact (hUnsat ⟨M, σ, hAnte A rfl⟩).elim
  have hsNoFreeBound :
      ∀ x : Nat,
        (∃ F, (F ∈ s.ante ∨ F ∈ s.succ) ∧
          x ∈ formulaFVN F) →
        (∀ B, (B ∈ s.ante ∨ B ∈ s.succ) →
          x ∉ formulaBVN B) := by
    intro x hx
    have hxFalse : False := by
      change
        (∃ F : FormulaN L,
          (F = A ∨ False) ∧ x ∈ formulaFVN F) at hx
      obtain ⟨F, hF, hxF⟩ := hx
      rcases hF with hFA | hF
      · subst F
        rw [hClosed] at hxF
        exact hxF
      · exact hF
    exact hxFalse.elim
  have hSetDerivable :
      LCS.CutElim.Hauptsatz.Completeness.G1nnfSetDerivable
        s.ante s.succ :=
    LCS.CutElim.Hauptsatz.Completeness.g1nnf_completeness
      hNoEq s hsValid hsNoFreeBound
  have hAnte :
      ∀ F, F ∈ ({A} : LCS.Finset (FormulaN L)) ↔ s.ante F := by
    intro F
    exact LCS.Finset.mem_singleton F A
  have hSucc :
      ∀ F, F ∈ (∅ : LCS.Finset (FormulaN L)) ↔ s.succ F := by
    intro F
    exact LCS.Finset.mem_empty F
  have hFinsetNNF :
      G1nnfFinsetSequent.IsNNF
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ hNNF
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  exact
    LCS.CutElim.Hauptsatz.g1nnfProofTree_of_setDerivable
      hSetDerivable hAnte hSucc hFinsetNNF

-- ===================================================================
-- Theorem 7.6.1 (part a, required companion): shg_unsat_cinstance
-- ===================================================================

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Internal closed-seed core of the forward direction of Theorem 7.6.1.
    Chapter 7 obtains this seed from its standing base-language constant
    assumption; later callers may instead supply a closed term already
    living in the selected Skolem language. The language equality flag selects
    G1nnf completeness and the G1nnf half lemma, or their equality-system
    counterparts. -/
noncomputable def shg_unsat_cinstance_seed {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hUnsat : ¬ satisfiableN A) :
    CInstance spec.language :=
  if hL : L.hasEquality = true then
    let hProv := g1nnfEq_provable_of_unsat hL A hUnsat
    let hEx :=
      Herbrand.herbrand_half_lemma_G1nnfEq_seed hL spec A hSource seed hProv
    Classical.choose (Classical.choose_spec hEx).1
  else
    have hNoEq : L.withoutEquality := by
      cases h : L.hasEquality <;> simp_all [Language.withoutEquality]
    let hProv := g1nnf_provable_of_unsat hNoEq A hUnsat
    let hEx :=
      Herbrand.herbrand_half_lemma_G1nnf_seed hNoEq spec A hSource seed hProv
    Classical.choose (Classical.choose_spec hEx).1

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Specification of the internal closed-seed c-instance constructor. -/
theorem shg_unsat_cinstance_seed_spec {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hUnsat : ¬ satisfiableN A) :
    (shg_unsat_cinstance_seed spec A hSource seed hUnsat).source = SK spec ∧
    CInstance.WellFormed
      (shg_unsat_cinstance_seed spec A hSource seed hUnsat) ∧
    ¬ satisfiableN
      (shg_unsat_cinstance_seed spec A hSource seed hUnsat).toFormula := by
  unfold shg_unsat_cinstance_seed
  split
  · rename_i hL
    have hEx :=
      Herbrand.herbrand_half_lemma_G1nnfEq_seed hL spec A hSource seed
        (g1nnfEq_provable_of_unsat hL A hUnsat)
    obtain ⟨hCinstOf, _hQF, hG2⟩ := Classical.choose_spec hEx
    obtain ⟨hSrc, hToF, hWF⟩ := Classical.choose_spec hCinstOf
    refine ⟨hSrc, hWF, ?_⟩
    rw [hToF]
    intro hSat
    obtain ⟨M, s, hEval⟩ := hSat
    have hValid :=
      LCS.Herbrand.NNFHauptsatz.Equality.g2nnfEq_provable_implies_valid
        (L := spec.language) hL _ _ hG2
    obtain ⟨B, hB, _⟩ := hValid M s (by
      intro A' hA'
      have hEq := (LCS.Finset.mem_singleton A' (Classical.choose hEx)).mp hA'
      exact hEq ▸ hEval)
    exact LCS.Finset.not_mem_empty hB
  · rename_i hL
    have hNoEq : L.withoutEquality := by
      cases h : L.hasEquality <;> simp_all [Language.withoutEquality]
    have hEx :=
      LCS.Herbrand.SHGTheorem.Herbrand.herbrand_half_lemma_G1nnf_seed
        hNoEq spec A hSource seed (g1nnf_provable_of_unsat hNoEq A hUnsat)
    have hCprop := Classical.choose_spec hEx
    obtain ⟨hCinstOf, _hQF, hG2⟩ := hCprop
    have hCiProp := Classical.choose_spec hCinstOf
    obtain ⟨hSrc, hToF, hWF⟩ := hCiProp
    refine ⟨hSrc, hWF, ?_⟩
    rw [hToF]
    intro hSat
    obtain ⟨M, s, hEval⟩ := hSat
    have hValid :
        LCS.Herbrand.NNFHauptsatz.Soundness.setSequentValid
          ({Classical.choose hEx} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language)) :=
      LCS.Herbrand.NNFHauptsatz.Soundness.g2nnf_provable_implies_valid
        (show spec.language.withoutEquality from hNoEq) _ _ hG2
    have hImpossible :
        ∃ B, Membership.mem
            (∅ : LCS.Finset (FormulaN spec.language)) B ∧
          formulaEvalN M B s := by
      apply hValid M s
      intro A' hA'
      have hAeq : A' = Classical.choose hEx :=
        (LCS.Finset.mem_singleton (α := FormulaN spec.language)
          A' (Classical.choose hEx)).mp hA'
      rw [hAeq]
      exact hEval
    obtain ⟨B, hB, _hEvalB⟩ := hImpossible
    exact absurd hB LCS.Finset.not_mem_empty

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Theorem 7.6.1 (part a, required companion): Given an unsatisfiable rectified L-sentence A in NNF with Skolem spec `spec` (so `A = spec.source`), constructs a compound instance of `SK spec` that is unsatisfiable. The closed-seed construction selects G1nnf or G1nnf= completeness and the corresponding Herbrand half lemma according to the language equality flag. -/
noncomputable def shg_unsat_cinstance {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hUnsat : ¬ satisfiableN A) :
    CInstance spec.language :=
  let seed : {t : Term spec.language // Term.isClosed t} :=
    ⟨.const (.inl (Classical.choice hConst)), by
      simp [Term.isClosed, termFV]⟩
  shg_unsat_cinstance_seed spec A hSource seed hUnsat

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Spec lemma for `shg_unsat_cinstance`: the produced c-instance has
source `SK spec`, is WellFormed, and its extracted quantifier-free
formula is unsatisfiable. -/
theorem shg_unsat_cinstance_spec {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hUnsat : ¬ satisfiableN A) :
    (shg_unsat_cinstance spec A hSource hConst hUnsat).source = SK spec ∧
    CInstance.WellFormed
      (shg_unsat_cinstance spec A hSource hConst hUnsat) ∧
    ¬ satisfiableN
      (shg_unsat_cinstance spec A hSource hConst hUnsat).toFormula := by
  unfold shg_unsat_cinstance
  exact shg_unsat_cinstance_seed_spec spec A hSource _ hUnsat

-- ===================================================================
-- Theorem 7.6.1 (helper): closed terms evaluate assignment-independently
-- ===================================================================

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Helper: a closed term is free for any variable in any formula. -/
theorem isFreeForN_of_closed {L : Language}
    (t : Term L) (hClosed : LCS.FirstOrder.Basic.Term.isClosed t)
    (x : Nat) (A : FormulaN L) :
    isFreeForN t x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => simp [isFreeForN]
  | eq_ _ _ _ => simp [isFreeForN]
  | neg _ ih => simp [isFreeForN]; exact ih
  | conj _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | all y _ ih =>
    simp [isFreeForN]
    by_cases hxy : x = y
    · left; exact hxy
    · right
      refine ⟨?_, ih⟩
      intro hy
      rw [hClosed] at hy
      exact hy
  | ex y _ ih =>
    simp [isFreeForN]
    by_cases hxy : x = y
    · left; exact hxy
    · right
      refine ⟨?_, ih⟩
      intro hy
      rw [hClosed] at hy
      exact hy

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Helper: for a closed term `t`, the evaluation of `A[t/x]` at
`s` equals the evaluation of `A` at `s[x := termEval M s t]`. -/
theorem formulaSubstEval_closed {L : Language} {M : Structure L}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hClosed : LCS.FirstOrder.Basic.Term.isClosed t)
    (s : Assignment M) :
    formulaEvalN M (formulaSubstN A t x) s ↔
    formulaEvalN M A (assignUpdate s x (termEval M s t)) :=
-- BEGIN PROOF
  formulaSubstEvalDirectN s A t x (isFreeForN_of_closed t hClosed x A)

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

end LCS.Herbrand.SHGTheorem.Main
end
