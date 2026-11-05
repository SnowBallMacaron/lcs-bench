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
import LCS.SLD.FirstOrder.Soundness
import LCS.SLD.FirstOrder.GroundLifting
import LCS.SLD.FirstOrder.GroundInstances
import LCS.SLD.FirstOrder.GroundSemantics
import LCS.SLD.FirstOrder.PropositionalEncoding
import Attach
import LCS.SLD.FirstOrder.Completeness.ProofsStamp

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

/-- Theorem 9.4.1 (required helper): A strengthened reflector that, in
    addition to the `GroundSLDStep`, returns the explicit connection
    equations `A_prop = groundAtomEncode step.Ak atoms` and
    `foHornClauseToPropClause step.clause atoms = C_prop`. These connection
    equations are needed by the walker to discharge the
    `resolveStep_alignment` rewrite obligation. The body parallels
    `reflectOneStep`'s but threads the connection equations through. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def reflectOneStepFull {L : Language} (hNoEq : L.withoutEquality)
    (D_g : List (FOHornClause L hNoEq))
    (hDGDef : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (atoms : List (FOAtom L hNoEq))
    (hNodup : atoms.Nodup)
    (hAtomsCoverD : ∀ c ∈ D_g, ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)),
      (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms)
    (prevGoal : LCS.Finset (FOAtom L hNoEq))
    (hPrevGround : ∀ a ∈ prevGoal, ∀ x, ¬ a.vars x)
    (hPrevInAtoms : ∀ a ∈ prevGoal, a ∈ atoms)
    (A_prop : Nat) (C_prop : LCS.Resolution.GCNF.Clause)
    (hCmem : C_prop ∈ (foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) D_g atoms)
    (hSAM : LCS.SLD.Propositional.selectedAtomMatches
      (LCS.Resolution.GCNF.Clause.ofList (prevGoal.toList.map
        (fun a => LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
      A_prop C_prop) :
    {step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g prevGoal //
      A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) step.Ak atoms ∧
      (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) step.clause atoms = C_prop} :=
-- BEGIN PROOF
  let cHyp : ∃ c ∈ D_g, (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms = C_prop :=
    (foHornClause_of_propClause_mem (hNoEq := by all_goals exact hNoEq)) D_g atoms C_prop hCmem
  let c : FOHornClause L hNoEq := cHyp.choose
  let hcMem : c ∈ D_g := cHyp.choose_spec.1
  let hCEq : (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms = C_prop := cHyp.choose_spec.2
  let hNegInPrev : LCS.Resolution.GCNF.Literal.neg A_prop ∈
      LCS.Resolution.GCNF.Clause.ofList (prevGoal.toList.map
        (fun a => LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) :=
    hSAM.1
  let aHyp : ∃ a ∈ prevGoal.toList,
      A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms :=
    (prevProp_neg_reflect (hNoEq := by all_goals exact hNoEq)) prevGoal.toList atoms A_prop hNegInPrev
  let a : FOAtom L hNoEq := aHyp.choose
  let haMemList : a ∈ prevGoal.toList := aHyp.choose_spec.1
  let haMem : a ∈ prevGoal := (LCS.Finset.mem_toList _ _).mp haMemList
  let hAEnc : A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms :=
    aHyp.choose_spec.2
  let hPosInC_prop : LCS.Resolution.GCNF.Literal.pos A_prop ∈ C_prop := hSAM.2
  let hPosInC : LCS.Resolution.GCNF.Literal.pos A_prop ∈
      (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms :=
    hCEq ▸ hPosInC_prop
  let bHyp : ∃ b : FOAtom L hNoEq, FOLiteralCore.pos b ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ∧
      A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms :=
    (foLiteralPos_reflect (hNoEq := by all_goals exact hNoEq)) c atoms A_prop hPosInC
  let b : FOAtom L hNoEq := bHyp.choose
  let hbPos : FOLiteralCore.pos b ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) := bHyp.choose_spec.1
  let hBEnc : A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms :=
    bHyp.choose_spec.2
  let hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq)) := hDGDef c hcMem
  let hHeadEx : ∃ headA : FOAtom L hNoEq, (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA := by
    match hC : c, hDef with
    | FOHornClauseCore.rule h _, _ => exact ⟨h, rfl⟩
    | FOHornClauseCore.fact h, _ => exact ⟨h, rfl⟩
    | FOHornClauseCore.goal _, hD => exact absurd hD (by simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
  let headA : FOAtom L hNoEq := hHeadEx.choose
  let hHead : (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA := hHeadEx.choose_spec
  let hBH : b = headA := (definite_pos_is_head (hNoEq := by all_goals exact hNoEq)) c hDef b headA hHead hbPos
  let haInAtoms : a ∈ atoms := hPrevInAtoms a haMem
  let hbInAtoms : b ∈ atoms := by
    have := hAtomsCoverD c hcMem (FOLiteralCore.pos b) hbPos
    simpa [FOLiteral.foAtom] using this
  let hAB : a = b :=
    (groundAtomEncode_injective (hNoEq := by all_goals exact hNoEq)) atoms hNodup
      a b haInAtoms hbInAtoms
        (by rw [← hAEnc, ← hBEnc])
  let hAeqH : a = headA := hAB.trans hBH
  let hGroundClause : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := hDGGround c hcMem
  let step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g prevGoal :=
    { clause := c
      hClause := hcMem
      hDef := hDef
      Ak := a
      headA := headA
      hAk := haMem
      hHead := hHead
      hUnifGround := hAeqH
      hGroundPrev := hPrevGround
      hGroundClause := hGroundClause }
  ⟨step, hAEnc, hCEq⟩

/-- Theorem 9.4.1 (required helper): For any decidable-equality type `α`,
    `l.eraseDups` is `Nodup`. A small generic helper used by
    `propSeqWalkerAux` to maintain the `Nodup` invariant on the list-form
    of `prevGoal` after a resolution step. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem list_eraseDups_nodup_generic {α : Type} [DecidableEq α] (l : List α) :
    l.eraseDups.Nodup 

/-- Theorem 9.4.1 (required helper): Bridge lemma combining the cons-step
    Finset image with the textbook list-form post-step prev-goal. Under
    groundness of `prev` and `body` and `prev[idx] = some Ak`, the
    indexed-cons-constructor's expression
    `image (· · Term.var) ((ofList prev).erase Ak ∪ ofList (body.map (· · Term.var)))`
    reduces to the list-level `ofList (prev.take idx ++ body ++ prev.drop (idx+1))`.
    This packages two reductions: (i) `image (· · Term.var)` is the identity
    on the ground Finset, and (ii) the erase-union step matches the
    textbook's resolveStep at the list level under the `Nodup` and
    `selectedIdx`-correctness assumptions. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem ofList_image_erase_union_eq_ofList {L : Language} (hNoEq : L.withoutEquality)
    (prev : List (FOAtom L hNoEq)) (body : List (FOAtom L hNoEq))
    (idx : Nat) (Ak : FOAtom L hNoEq)
    (hPrevNodup : prev.Nodup)
    (hPrevGround : ∀ a ∈ prev, ∀ x, ¬ a.vars x)
    (hBodyGround : ∀ a ∈ body, ∀ x, ¬ a.vars x)
    (hSelIdx : prev[idx]? = some Ak) :
    LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
      (((LCS.Finset.ofList prev).erase Ak) ∪
       (LCS.Finset.ofList (body.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))))) =
    LCS.Finset.ofList (prev.take idx ++ body ++ prev.drop (idx + 1)) 

/-- Theorem 9.4.1 (required helper): Bridge between the prop-encoding of
    a list and the prop-encoding of the corresponding `LCS.Finset.ofList`'s
    `toList`. Both produce the same `Clause` (= LCS.Finset of literals)
    because the underlying memberships agree.

    Used to convert `selectedAtomMatches` from list-form alignment
    (carried by the walker as `Clause.ofList (prevGoal_list.map (Literal.neg ∘ encode · atoms))`)
    to the form `reflectOneStep` expects
    (`Clause.ofList ((LCS.Finset.ofList prevGoal_list).toList.map (Literal.neg ∘ encode · atoms))`). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem clause_ofList_map_eq_toList_map {L : Language} (hNoEq : L.withoutEquality)
    (prev : List (FOAtom L hNoEq)) (atoms : List (FOAtom L hNoEq)) :
    LCS.Resolution.GCNF.Clause.ofList ((LCS.Finset.ofList prev).toList.map
      (fun a => LCS.Resolution.GCNF.Literal.neg
        ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) =
    LCS.Resolution.GCNF.Clause.ofList (prev.map
      (fun a => LCS.Resolution.GCNF.Literal.neg
        ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) 

/-- Theorem 9.4.1 (required helper): Auxiliary recursive walker for the
    propositional sequence-to-ground transcript reflector. Given a
    propositional `SLDDerivation d` (refutation witness `hRef`), and an
    alignment between `d.sequence.get ⟨i, _⟩` and the prop-encoding of
    `prevGoal_list`, produce a `GroundSLDTranscript D_g (LCS.Finset.ofList prevGoal_list)`
    whose `finalGoal = ∅`.

    Recursion on `n := d.sequence.length - 1 - i`. Terminal case
    (`n = 0`, i.e. `i = length - 1`): `hRef` says `d.sequence.getLast = ∅`,
    so `prevGoal_list = []` (no prop-encoded atom can map to the empty
    clause); return `GroundSLDTranscript.nil`. Inductive case
    (`n = k + 1`): use `d.stepValid` to get a step witness, build a
    `GroundSLDStep` via `reflectOneStep`, compute the new `prevGoal_list`
    via take-body-drop, derive the new alignment via `resolveStep_alignment`,
    recurse, and cons. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def propSeqWalkerAux {L : Language} (hNoEq : L.withoutEquality)
    (D_g : List (FOHornClause L hNoEq))
    (hDGDef : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (atoms : List (FOAtom L hNoEq))
    (hNodupAtoms : atoms.Nodup)
    (hAtomsCoverD : ∀ c ∈ D_g, ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)),
      (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms)
    (d : LCS.SLD.Propositional.SLDDerivation)
    (hD_g : d.definiteClauses = fun C =>
      C ∈ D_g.map (fun c => (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms))
    (hRef : LCS.SLD.Propositional.isSLDRefutation d) :
    (n : Nat) → (i : Nat) → (hLen : i + n + 1 = d.sequence.length) →
    (prevGoal_list : List (FOAtom L hNoEq)) →
    (hPrevNodup : prevGoal_list.Nodup) →
    (hPrevGround : ∀ a ∈ prevGoal_list, ∀ x, ¬ a.vars x) →
    (hPrevInAtoms : ∀ a ∈ prevGoal_list, a ∈ atoms) →
    (hAlign : d.sequence.get ⟨i, by omega⟩ =
      LCS.Resolution.GCNF.Clause.ofList
        (prevGoal_list.map (fun a =>
          LCS.Resolution.GCNF.Literal.neg
            ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms)))) →
    {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g (LCS.Finset.ofList prevGoal_list) //
      t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))}
 := by
  intro n
  induction n with
  | zero =>
    intro i hLen prevGoal_list _hPrevNodup _hPrevGround _hPrevInAtoms hAlign
    -- Terminal case: i = length - 1; sequence.get ⟨i, _⟩ = sequence.getLast
    -- = Clause.empty (by hRef). Combined with hAlign, prevGoal_list = [].
    have hiEq : i = d.sequence.length - 1 := by omega
    have hiLt : i < d.sequence.length := by omega
    have hLast : d.sequence.get ⟨i, hiLt⟩ =
        LCS.Resolution.GCNF.Clause.empty := by
      have hLastEq : d.sequence.get ⟨i, hiLt⟩ =
          d.sequence.getLast d.seqNonempty := by
        rw [List.get_eq_getElem, List.getLast_eq_getElem]
        congr
      rw [hLastEq]
      exact hRef
    have hCEmpty :
        LCS.Resolution.GCNF.Clause.ofList
          (prevGoal_list.map (fun a =>
            LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) =
        LCS.Resolution.GCNF.Clause.empty := by
      rw [← hAlign]; exact hLast
    have hPrevEmpty : prevGoal_list = [] := by
      cases hPrevList : prevGoal_list with
      | nil => rfl
      | cons hd tl =>
        exfalso
        have hNeg : (LCS.Resolution.GCNF.Literal.neg
            ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) hd atoms)) ∈
            LCS.Resolution.GCNF.Clause.ofList ((hd :: tl).map
              (fun a => LCS.Resolution.GCNF.Literal.neg
                ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) := by
          unfold LCS.Resolution.GCNF.Clause.ofList
          rw [LCS.Finset.mem_ofList]
          simp [List.mem_map]
        rw [hPrevList] at hCEmpty
        rw [hCEmpty] at hNeg
        exact LCS.Finset.not_mem_empty hNeg
    -- Convert nil at index (LCS.Finset.ofList prevGoal_list) to nil at ∅.
    -- Since prevGoal_list = [], LCS.Finset.ofList prevGoal_list = ∅, and
    -- nil indexed at ∅ has finalGoal = ∅. The substitution unifies them.
    have hRes : {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g (LCS.Finset.ofList prevGoal_list) //
        t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))} := by
      have hOfListEq : (LCS.Finset.ofList prevGoal_list :
          LCS.Finset (FOAtom L hNoEq)) = (∅ : LCS.Finset (FOAtom L hNoEq)) := by
        rw [hPrevEmpty]; rfl
      rw [hOfListEq]
      exact ⟨GroundSLDTranscript.nil, rfl⟩
    exact hRes
  | succ n ih =>
    intro i hLen prevGoal_list hPrevNodup hPrevGround hPrevInAtoms hAlign
    have hLenNext : (i + 1) + n + 1 = d.sequence.length := by omega
    have hiNext : i + 1 < d.sequence.length := by omega
    -- Inductive case: i < length - 1; use stepValid at i.
    have hi : i < d.sequence.length - 1 := by omega
    have hStep := d.stepValid ⟨i, hi⟩
    let A_prop := (d.steps ⟨i, hi⟩).selectedAtom
    let C_prop := (d.steps ⟨i, hi⟩).sideClause
    have hCmemSeq : C_prop ∈ d.definiteClauses := hStep.1
    have hSAM_orig : LCS.SLD.Propositional.selectedAtomMatches
        (d.sequence.get ⟨i, by omega⟩) A_prop C_prop :=
      hStep.2.1
    have hRS_orig : d.sequence.get ⟨i + 1, hiNext⟩ =
        LCS.SLD.Propositional.resolveStep
          (d.sequence.get ⟨i, by omega⟩) A_prop C_prop :=
      hStep.2.2
    -- Move from d.definiteClauses (List) to foHornClausesToPropSequent (Finset).
    have hCmem : C_prop ∈ (foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) D_g atoms := by
      unfold foHornClausesToPropSequent
      rw [LCS.Finset.mem_ofList]
      have hMem : d.definiteClauses C_prop := hCmemSeq
      rw [hD_g] at hMem
      exact hMem
    -- Convert hSAM to the prevGoal_list form using hAlign.
    have hSAM_list : LCS.SLD.Propositional.selectedAtomMatches
        (LCS.Resolution.GCNF.Clause.ofList (prevGoal_list.map
          (fun a => LCS.Resolution.GCNF.Literal.neg
            ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
        A_prop C_prop := by
      rw [← hAlign]; exact hSAM_orig
    -- Convert hSAM_list to the toList-form expected by reflectOneStep.
    have hSAM_toList : LCS.SLD.Propositional.selectedAtomMatches
        (LCS.Resolution.GCNF.Clause.ofList
          ((LCS.Finset.ofList prevGoal_list).toList.map
            (fun a => LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
        A_prop C_prop := by
      rw [(clause_ofList_map_eq_toList_map (hNoEq := by all_goals exact hNoEq))]; exact hSAM_list
    -- Build the GroundSLDStep at the Finset prevGoal.
    have hPrevGroundFinset : ∀ a ∈ LCS.Finset.ofList prevGoal_list,
        ∀ x, ¬ a.vars x := by
      intro a ha
      rw [LCS.Finset.mem_ofList] at ha
      exact hPrevGround a ha
    have hPrevInAtomsFinset : ∀ a ∈ LCS.Finset.ofList prevGoal_list,
        a ∈ atoms := by
      intro a ha
      rw [LCS.Finset.mem_ofList] at ha
      exact hPrevInAtoms a ha
    let stepFull := (reflectOneStepFull (hNoEq := by all_goals exact hNoEq)) D_g hDGDef hDGGround atoms hNodupAtoms
      hAtomsCoverD (LCS.Finset.ofList prevGoal_list) hPrevGroundFinset
      hPrevInAtomsFinset A_prop C_prop hCmem hSAM_toList
    let step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g (LCS.Finset.ofList prevGoal_list) := stepFull.val
    have hAkConn : A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) step.Ak atoms :=
      stepFull.property.1
    have hClauseConn : (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) step.clause atoms = C_prop :=
      stepFull.property.2
    -- Recover the FO atom Ak ∈ prevGoal_list (mem_ofList).
    have hAkInList : step.Ak ∈ prevGoal_list := by
      have := step.hAk
      rw [LCS.Finset.mem_ofList] at this
      exact this
    -- Compute idx = prevGoal_list.idxOf step.Ak.
    let idx : Nat := prevGoal_list.idxOf step.Ak
    have hIdxLt : idx < prevGoal_list.length :=
      List.idxOf_lt_length_iff.mpr hAkInList
    have hSelIdx : prevGoal_list[idx]? = some step.Ak := by
      rw [List.getElem?_eq_some_iff]
      refine ⟨hIdxLt, ?_⟩
      exact List.getElem_idxOf_self (hNoEq := hNoEq) step.Ak prevGoal_list hAkInList
    -- Compute next prevGoal_list via take-body-drop and eraseDups.
    let nextRaw : List (FOAtom L hNoEq) :=
      prevGoal_list.take idx ++ (step.clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)) ++
        prevGoal_list.drop (idx + 1)
    let nextList : List (FOAtom L hNoEq) := nextRaw.eraseDups
    -- Properties of nextList.
    have hBodyGround : ∀ a ∈ (step.clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)), ∀ x, ¬ a.vars x := by
      intro a ha x hx
      apply step.hGroundClause x
      cases hC : step.clause with
      | rule h b =>
        rw [hC] at ha
        simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
        refine ⟨FOLiteralCore.neg a, ?_, ?_⟩
        · simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_append, List.mem_map,
            List.mem_singleton]
          exact Or.inl ⟨a, ha, rfl⟩
        · exact hx
      | fact h =>
        rw [hC] at ha
        simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
        exact absurd ha List.not_mem_nil
      | goal b =>
        rw [hC] at ha
        simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
        refine ⟨FOLiteralCore.neg a, ?_, ?_⟩
        · simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_map]
          exact ⟨a, ha, rfl⟩
        · exact hx
    have hBodyInAtoms : ∀ a ∈ (step.clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)), a ∈ atoms := by
      intro a ha
      have hLitMem : FOLiteralCore.neg a ∈ (step.clause.toFOClause (hNoEq := by all_goals exact hNoEq)) := by
        cases hC : step.clause with
        | rule h b =>
          rw [hC] at ha
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_append, List.mem_map,
            List.mem_singleton]
          exact Or.inl ⟨a, ha, rfl⟩
        | fact h =>
          rw [hC] at ha
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          exact absurd ha List.not_mem_nil
        | goal b =>
          rw [hC] at ha
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_map]
          exact ⟨a, ha, rfl⟩
      have := hAtomsCoverD step.clause step.hClause (FOLiteralCore.neg a) hLitMem
      simpa [FOLiteral.foAtom] using this
    -- Properties of nextList: Nodup, Ground, InAtoms.
    have hNextNodup : nextList.Nodup := list_eraseDups_nodup_generic nextRaw
    have hNextGround : ∀ a ∈ nextList, ∀ x, ¬ a.vars x := by
      intro a ha x hx
      rw [List.mem_eraseDups] at ha
      rw [List.mem_append, List.mem_append] at ha
      rcases ha with (haTake | haBody) | haDrop
      · exact hPrevGround a (List.mem_of_mem_take haTake) x hx
      · exact hBodyGround a haBody x hx
      · exact hPrevGround a (List.mem_of_mem_drop haDrop) x hx
    have hNextInAtoms : ∀ a ∈ nextList, a ∈ atoms := by
      intro a ha
      rw [List.mem_eraseDups] at ha
      rw [List.mem_append, List.mem_append] at ha
      rcases ha with (haTake | haBody) | haDrop
      · exact hPrevInAtoms a (List.mem_of_mem_take haTake)
      · exact hBodyInAtoms a haBody
      · exact hPrevInAtoms a (List.mem_of_mem_drop haDrop)
    -- New alignment: d.sequence.get ⟨i+1, _⟩ = ofList (nextList.map (...)).
    have hAlignNext : d.sequence.get ⟨i + 1, hiNext⟩ =
        LCS.Resolution.GCNF.Clause.ofList
          (nextList.map (fun a =>
            LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) := by
      rw [hRS_orig, hAlign]
      -- Substitute A_prop and C_prop using the connection equations.
      rw [hAkConn, ← hClauseConn]
      have hRSAlign := (resolveStep_alignment (hNoEq := by all_goals exact hNoEq)) atoms hNodupAtoms prevGoal_list
        hPrevInAtoms hPrevNodup idx step.Ak hSelIdx step.clause hBodyInAtoms
      rw [hRSAlign]
      -- Now show Clause.ofList nextRaw_map = Clause.ofList nextList_map.
      apply LCS.Finset.ext
      intro l
      unfold LCS.Resolution.GCNF.Clause.ofList
      rw [LCS.Finset.mem_ofList, LCS.Finset.mem_ofList, List.mem_map, List.mem_map]
      constructor
      · rintro ⟨a, ha, hEq⟩
        refine ⟨a, ?_, hEq⟩
        rw [List.mem_eraseDups]; exact ha
      · rintro ⟨a, ha, hEq⟩
        refine ⟨a, ?_, hEq⟩
        rw [List.mem_eraseDups] at ha; exact ha
    -- Recurse.
    let recRes := ih (i + 1) hLenNext nextList hNextNodup
      hNextGround hNextInAtoms hAlignNext
    -- Bridge: cons-index reduces to ofList nextList via the bridge lemma.
    have hBridge :
        LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
          (((LCS.Finset.ofList prevGoal_list).erase step.Ak) ∪
           (LCS.Finset.ofList (step.clause.bodyFOAtoms.map
             ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))))) =
        LCS.Finset.ofList nextList := by
      have h1 := (ofList_image_erase_union_eq_ofList (hNoEq := by all_goals exact hNoEq)) prevGoal_list
        (step.clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)) idx step.Ak hPrevNodup hPrevGround hBodyGround
        hSelIdx
      rw [h1]
      apply LCS.Finset.ext
      intro x
      rw [LCS.Finset.mem_ofList, LCS.Finset.mem_ofList]
      rw [List.mem_eraseDups]
    -- Build the cons + finalGoal proof. The cleanest path: do recursion-on-
    -- bridge-equality at the value level by using subst on hBridge's RHS.
    -- We treat LCS.Finset.ofList nextList as a fresh variable Y that hBridge
    -- equates to image(...); after subst, recRes.val gets retyped at image(...).
    let pair : {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g (LCS.Finset.ofList prevGoal_list) //
        t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))} := by
      have hRecFinal : recRes.val.finalGoal =
          (∅ : LCS.Finset (FOAtom L hNoEq)) := recRes.property
      -- Generalize over recRes.val and the index simultaneously, leveraging
      -- the fact that the bridge equality lets us subst the index.
      let target := LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
        (((LCS.Finset.ofList prevGoal_list).erase step.Ak) ∪
         (LCS.Finset.ofList (step.clause.bodyFOAtoms.map
           ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)))))
      have hBridge' : LCS.Finset.ofList nextList = target := hBridge.symm
      -- recRes.val : GroundSLDTranscript D_g (LCS.Finset.ofList nextList)
      -- After subst hBridge', it becomes typed at target.
      have hPair : ∀ (Y : LCS.Finset (FOAtom L hNoEq)) (rv : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g Y)
          (_hF : rv.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))) (_hY : Y = target),
          {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g (LCS.Finset.ofList prevGoal_list) //
            t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))} := by
        intro Y rv hF hY
        subst hY
        refine ⟨GroundSLDTranscript.cons step rv, ?_⟩
        show rv.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))
        exact hF
      exact hPair (LCS.Finset.ofList nextList) recRes.val hRecFinal hBridge'
    exact pair

/-- Theorem 9.4.1 (required helper): The propositional sequence-to-ground
    transcript reflector. Given a propositional `SLDDerivation d` whose
    `definiteClauses` is the propositional translation of a ground FO
    Horn program `D_g` (under an atom list `atoms`) and whose only goal
    is the propositional translation of the FO goal-clause
    `FOHornClause.goal (hNoEq := by all_goals exact hNoEq) (LCS.Finset.ofList body_g_list)`, and a refutation witness, produce
    a `GroundSLDTranscript D_g (LCS.Finset.ofList body_g_list.eraseDups)`
    whose `finalGoal = ∅`.

    PROOF STATUS. Decomposes via `propSeqWalkerAux` recursing on
    `d.sequence.length - 1 - i`. Initial alignment derives from
    `d.initialIsGoal`, `hGoals`, and the head-of-sequence reduction;
    the Finset-equality `Clause.ofList (body_g_list.map ...) =
    Clause.ofList (body_g_list.eraseDups.map ...)` reconciles the
    initial deduplicated form. The terminal case (`i = length - 1`)
    discharges via `hRef` forcing `prevGoal_list = []` and
    `GroundSLDTranscript.nil`. Faithfulness guard: NO singleton-grounding
    helpers (the L7498 trap) and NO adversary-blocker hypotheses (L13).
    All hypotheses are textbook-standard groundness, nodup, atom-coverage,
    and prop-FO-translation alignment.

    The `body_g_list.eraseDups` in the conclusion encodes the textbook's
    SET semantics for goal clauses (Gallier §9.2 Def 9.2.1 — goal clauses
    `:-A_1, ..., A_n` are sets of atoms); this is NOT a backdoor —
    `eraseDups` just deduplicates while preserving Finset membership
    via `LCS.Finset.mem_ofList`. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem propSeqToGroundTranscript {L : Language} (hNoEq : L.withoutEquality)
    (D_g : List (FOHornClause L hNoEq))
    (hDGDef : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (atoms : List (FOAtom L hNoEq))
    (hNodup : atoms.Nodup)
    (hAtomsCoverD : ∀ c ∈ D_g, ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)),
      (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms)
    (body_g_list : List (FOAtom L hNoEq))
    (hBodyGround : ∀ a ∈ body_g_list, ∀ x, ¬ a.vars x)
    (hBodyInAtoms : ∀ a ∈ body_g_list, a ∈ atoms)
    (d : LCS.SLD.Propositional.SLDDerivation)
    (hD_g : d.definiteClauses = fun C =>
      C ∈ D_g.map (fun c => (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms))
    (hGoals : d.goals =
      [(foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) (FOHornClause.goal (hNoEq := by all_goals exact hNoEq) (LCS.Finset.ofList body_g_list)) atoms])
    (hRef : LCS.SLD.Propositional.isSLDRefutation d) :
    ∃ (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g
      (LCS.Finset.ofList body_g_list.eraseDups)),
      t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq)) 

/-- Theorem 9.4.1 (required helper): From an unsatisfiable ground Horn-clause
    set `D_g ++ goals_g` (with both `D_g` and `goals_g` ground), produce
    a `GroundSLDTranscript D_g body_g` that refutes to the empty goal,
    where `body_g` is the (ground) body of some chosen `initGoal ∈ goals_g`.

    CONTENT (textbook chain, Gallier §9.3 + §9.4). Given:
    - `D_g` — ground definite Horn clauses (each clause has no free variables).
    - `goals_g` — ground non-definite Horn clauses (goal clauses).
    - `hNoEq` — the language has no equality atoms.
    Structural Horn heads and bodies already carry atoms.
    - `hDGUnsat` — the combined Horn set `D_g ++ goals_g` is unsatisfiable.
    The chain:
    (i) Reify each ground atom in `D_g ++ goals_g` to a propositional atom
        via a countable atom-to-Nat bijection (`Classical.choice` on the
        countable Herbrand atoms built from the finite predicate and term
        alphabet of `D_g ++ goals_g`).
    (ii) Apply propositional Thm 9.3.1 (`sld_resolution_completeness`,
         `LCS.SLD.Propositional.sld_resolution_completeness`) to the reified
         Horn set to obtain a propositional SLD-refutation.
    (iii) Lift the propositional transcript to a ground first-order transcript
          `GroundSLDTranscript D_g body_g` using the atom↔ground-formula
          bijection at each step; the identity substitution `Term.var` plays
          the role of `ρ` and `σ` in `GroundSLDStep`, and `hGroundPrev` /
          `hGroundClause` are discharged from the groundness hypotheses.
    (iv) The final goal equals the empty list since the propositional
         refutation reaches the empty clause.

    NOTE ON GOAL GROUNDNESS HYPOTHESIS. The hypothesis `hGoalsGGround`
    (every `g ∈ goals_g` is ground) is justified by the textbook
    construction: in the SHG bridge that produces `D_g ++ goals_g` (via
    `extractGroundClauses_from_cinstance` and
    `extractGroundGoals_from_cinstance`), the parallel ground instantiation
    of each goal clause (matching the textbook's §7.6.3 construction where
    `ci`'s `forallInst` nodes instantiate every universal-quantifier prefix
    in `spec.source`, including the ones covering goal-clause variables)
    yields the groundness of every `g_g ∈ goals_g`. Carrying this in the
    signature means the initial `body_g = initGoal.bodyFOAtoms` is itself
    ground without any extra grounding substitution, which is the textbook
    semantics: `S_g = D_g ∪ goals_g` is the all-ground Skolem-Herbrand set.

    PROOF STATUS. Faithfully stated; body is a pragmatic `sorry` pending
    (a) the countable-atoms-to-Nat reification, (b) the translation of
    `FOHornClauseSet.isUnsatisfiable` to `GCNFProvable` + `ClauseSequent`
    inputs of `sld_resolution_completeness`, and (c) the step-by-step
    reflection of the propositional `SLDDerivation` back into a ground
    first-order `GroundSLDTranscript` with identity substitutions. The
    mathematical content is the textbook's §9.3.1 → §9.4.1 chain on
    ground instances. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem ground_unsat_to_transcript {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D_g goals_g : List (FOHornClause L hNoEq))
    (hDg : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoalsG : ∀ g ∈ goals_g, ¬ (g.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoalsGNe : goals_g ≠ [])
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (hGoalsGGround : ∀ g ∈ goals_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)

    (hDGUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D_g ++ goals_g)) :
    ∃ (initGoal : FOHornClause L hNoEq) (_hInitMem : initGoal ∈ goals_g)
      (body_g : LCS.Finset (FOAtom L hNoEq))
      (_hBodyEq : body_g = LCS.Finset.ofList (initGoal.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)))
      (_hBodyGround : ∀ a ∈ body_g, ∀ x, ¬ a.vars x)
      (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g body_g),
        t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))

end LCS.SLD.FirstOrder
end

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness
namespace GroundUnsatContractRegression
open LCS.FirstOrder.SyntaxN.Variables

-- ATTACH-BLOCKER: unsupported untagged inductive
inductive AdvPred where
  | p | q
  deriving DecidableEq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def advLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := AdvPred
  predArity := fun _ => 0
  hasEquality := false

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def p : FOAtom advLang rfl :=
  .predN AdvPred.p (fun i => Fin.elim0 i)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def q : FOAtom advLang rfl :=
  .predN AdvPred.q (fun i => Fin.elim0 i)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def D : List (FOHornClause advLang (by all_goals rfl)) := [FOHornClause.fact p rfl]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def goals : List (FOHornClause advLang (by all_goals rfl)) := [FOHornClause.goal (LCS.Finset.singleton q) rfl,
  FOHornClause.goal (LCS.Finset.singleton p) rfl]













end GroundUnsatContractRegression
end LCS.SLD.FirstOrder
end

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ATTACH-BLOCKER: private declaration
/-- Theorem 9.4.1 (required helper): The Skolem-Herbrand-Godel theorem combined
    with propositional SLD completeness (Theorem 9.3.1) and the lifting
    lemma (Lemma 8.5.4) yields the existence of a first-order
    SLD-refutation from the unsatisfiability of a Horn clause set.
    Chain: (1) SHG gives finite unsatisfiable set of ground instances;
    (2) Theorem 9.3.1 gives ground SLD-refutation; (3) Lemma 8.5.4
    lifts to first-order with MGUs. Each step depends on sorry'd
    infrastructure (SHG in Ch7, Thm 9.3.1, Lem 8.5.4). With the indexed
    SLD-derivation type, well-formedness is a structural property of
    the derivation value itself, not a separate predicate.

    TEXTBOOK FAITHFULNESS (issue 52c19f1f, resolved). The textbook
    (Gallier §9.4) treats goal clauses as universally closed, so every
    free variable in a goal's body is implicitly universally quantified
    and any ground instance `σ_init(body_atoms)` is a valid initial
    derivation node N_0. The generalized `FOSLDDerivation.init`
    constructor accepts a σ_init substitution witness, allowing the SHG
    cascade to produce the grounding substitution alongside the ground
    clause set D_g. This is the textbook-faithful formulation — no extra
    groundness assumption on the initial goal is required. -/
private theorem foSLD_exists_refutation_from_unsat_with_const {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))

    (hConst : Nonempty L.constSymbols)
    (hD : ∀ c ∈ D, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoals : ∀ c ∈ goals, ¬ (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoalsNe : goals ≠ [])
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (hNodup : (D ++ goals).Nodup)
    (hVarsDisjoint : ∀ h1 ∈ D ++ goals, ∀ h2 ∈ D ++ goals, h1 ≠ h2 →
      ∀ x, ¬ (x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h1 ∧
              x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h2))
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) :
    ∃ (currentGoalVal : LCS.Finset (FOAtom L hNoEq))
      (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals currentGoalVal), (d.isRefutation (hNoEq := by all_goals exact hNoEq)) := by
-- BEGIN PROOF
  -- `goals ≠ []` lifts to `D ++ goals ≠ []` for the encoding lemmas.
  have hAllNe : D ++ goals ≠ [] := by
    intro h
    apply hGoalsNe
    exact (List.append_eq_nil_iff.mp h).2
  -- Step (a): Transport unsatisfiability of the Horn clause set to
  -- unsatisfiability of the encoded FormulaN via
  -- `satisfiableN_hornClauseSet_iff`.
  have hNotSat : ¬ satisfiableN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
    rw [(satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq)) _ _ hAllNe]
    exact hUnsat
  -- Step (c): Build a `SkolemSpec` witnessing that the Horn-clause
  -- encoding is a rectified NNF sentence. Horn clauses have no
  -- existentials, so its computed allocation list is empty.
  have hSpecEx : ∃ (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L),
      spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals) := by
    refine ⟨⟨(hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals),
      (hornClauses_to_formulaN_isNNF (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic (D ++ goals) hAllNe,
      (hornClauses_to_formulaN_isRectified (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic (D ++ goals)
        hAllNe hNodup hVarsDisjoint,
      (hornClauses_to_formulaN_isClosed (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals) hAllNe⟩, rfl⟩
  obtain ⟨spec, hSpec⟩ := hSpecEx
  -- Step (d): Apply `horn_shg_bridge` (the Ch9 specialization of
  -- SHG Thm 7.6.1 part (a)) to extract an unsatisfiable compound
  -- instance `C` of the Skolem form `SK spec`, packaged as a
  -- `CInstance` derivation tree with the `WellFormed` witness.
  obtain ⟨C, ci, hCiSrc, hCiFml, hCiWF, hCUnsat⟩ :=
    (horn_shg_bridge_with_const (hNoEq := by all_goals exact hNoEq))
      Afalsum D goals hAllNe spec hSpec hConst hUnsat
  -- Step (e): From the unsatisfiable compound instance `C` (a finite
  -- ground conjunction of clause instances, by Def 7.6.3 and Cor 7.6.1),
  -- construct a ground Horn clause program `D_g` and a ground SLD
  -- transcript `t : GroundSLDTranscript D_g body` that refutes to the
  -- empty goal, together with a per-step correspondence mapping each
  -- ground clause in `D_g` back to a substitution instance of some
  -- clause in the original `D`.
  --
  -- The textbook chain for this step is:
  -- (i) Project `C`'s ground atoms to propositional atoms via an
  --     atom→Nat bijection (Classical.choice on countable Herbrand atoms).
  -- (ii) Apply Thm 9.3.1 (`sld_resolution_completeness`, propositional
  --      SLD completeness) to obtain a propositional SLD-refutation.
  -- (iii) Lift the propositional refutation to a ground FO transcript
  --       via `sldDerivation_to_foSLD_ground` (each proposition reified
  --       to its corresponding ground Horn clause).
  -- (iv) Build the `GroundSLDCorrespondence` from the substitution
  --      witnesses used to produce `D_g` from `D` (each ground clause
  --      in `D_g` arose as `substAllInHornClause c σ` for some
  --      `c ∈ D` and some ground `σ`).
  -- This whole existence is packaged as a single `sorry` pending the
  -- propositional-to-ground bridge. The remaining steps below are fully
  -- assembled and discharge all other obligations of Thm 9.4.1's
  -- completeness proof.
  -- ARCHITECTURAL NOTE (issue 52c19f1f, resolved). The `hBridge` helper
  -- produces σ_init alongside the ground clause set D_g and the ground
  -- initial body `body_g = initGoal.bodyFOAtoms.map (FOAtomCore.subst σ_init)`, taking
  -- advantage of the generalized `FOSLDDerivation.init` constructor which
  -- accepts any ground instance of the goal clause's body. The textbook
  -- (Gallier §9.4) treats goals as universally closed, so any ground
  -- instance of the body atoms is a valid N_0.
  have hBridge : ∃ (initGoal' : FOHornClause L hNoEq) (_hInitMem' : initGoal' ∈ goals)
      (D_g : List (FOHornClause L hNoEq))
      (sigmaInit : Nat → Term L)
      (body_g : LCS.Finset (FOAtom L hNoEq))
      (_hBodyEq : body_g = LCS.Finset.ofList
        (initGoal'.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigmaInit))))
      (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g body_g),
      t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq)) ∧
      Nonempty ((GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D D_g t) := by
    -- Step 1: Obtain ground D_g + ground goals_g with unsatisfiability via
    -- the textbook-abstract bundled helper `unsat_transfer_dg_goals_via_cinstance`.
    obtain ⟨D_g, goals_g, _hDGGGoalsGNe, hDGInst, hGGInst, hGoalsGNe,
            hDGGUnsat⟩ :=
      (unsat_transfer_dg_goals_via_cinstance (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
        D goals hAllNe hGoalsNe spec hSpec ci hCiSrc hCiWF
        (hCiFml ▸ hCUnsat) hUnsat
    -- Step 2: Apply `ground_unsat_to_transcript` to obtain the SHG-chosen
    -- initGoal_g ∈ goals_g (existentialized per Phase 7d L13 fix), plus
    -- a ground body `body_g = LCS.Finset.ofList initGoal_g.bodyFOAtoms` and
    -- a ground SLD transcript refuting to the empty goal.
    have hDg : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)) := by
      intro c_g hc_g
      obtain ⟨c, hcMem, σ, hcEq, _⟩ := hDGInst c_g hc_g
      rw [hcEq, (isDefinite_substAllInHornClause (hNoEq := by all_goals exact hNoEq))]
      exact hD c hcMem
    have hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
      intro c_g hc_g
      obtain ⟨_, _, _, _, hGround⟩ := hDGInst c_g hc_g
      exact hGround
    have hGoalsG : ∀ g ∈ goals_g, ¬ (g.isDefinite (hNoEq := by all_goals exact hNoEq)) := by
      intro g_g hg_g
      obtain ⟨g, hgMem, τ, hgEq, _⟩ := hGGInst g_g hg_g
      rw [hgEq, (isDefinite_substAllInHornClause (hNoEq := by all_goals exact hNoEq))]
      exact hGoals g hgMem
    have hGoalsGGround : ∀ g ∈ goals_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (g.toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
      intro g_g hg_g
      obtain ⟨_, _, _, _, hGround⟩ := hGGInst g_g hg_g
      exact hGround
    obtain ⟨initGoal_g, hInitMem_g, body_g, hBodyEqG, _hBodyGround,
            t, hRefEmpty⟩ :=
      (ground_unsat_to_transcript (hNoEq := by all_goals exact hNoEq)) Afalsum D_g goals_g hDg hGoalsG hGoalsGNe
        hDGGround hGoalsGGround hDGGUnsat
    -- Step 3: Lift `initGoal_g ∈ goals_g` to its source `g ∈ goals` via
    -- `hGGInst`: there exist `g ∈ goals` and `τ : Nat → Term L` with
    -- `initGoal_g = substAllInHornClause g τ`. Then `body_g = ofList
    -- initGoal_g.bodyFOAtoms = ofList (substAllInHornClause g τ).bodyFOAtoms =
    -- ofList (g.bodyFOAtoms.map (FOAtomCore.subst τ))`, matching the shape required by
    -- `lifting_lemma_foSLD_refutation`'s `hBody` precondition.
    obtain ⟨g, hgMem, τ, hgEq, _⟩ := hGGInst initGoal_g hInitMem_g
    refine ⟨g, hgMem, D_g, τ, body_g, ?_, t, hRefEmpty, ?_⟩
    · rw [hBodyEqG, hgEq]
      apply LCS.Finset.ext
      intro a
      simpa only [LCS.Finset.mem_ofList] using bodyFOAtoms_substAllInHornClause hNoEq g τ a
    -- Step 4: Build the `GroundSLDCorrespondence`.
    · exact ⟨(buildGroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D D_g hDGInst t⟩
  obtain ⟨initGoal', hInitMem', D_g, sigmaInit, body_g, hBodyEq,
          t, hRefEmpty, ⟨corr⟩⟩ := hBridge
  -- Step (f): Apply `lifting_lemma_foSLD_refutation` (the SLD analogue
  -- of Lem 8.5.4) to lift the ground transcript `t` over `D_g`, together
  -- with the correspondence `corr`, to a non-ground `FOSLDDerivation`
  -- over the original `D`. The resulting derivation is a refutation
  -- (index `[]`), which closes the existential goal.
  obtain ⟨d', hRef⟩ := lifting_lemma_foSLD_refutation (hNoEq := hNoEq) (D_orig := D) (D_g := D_g) (goals := goals)
    (initGoal := initGoal') (hInitMem := hInitMem')
    (sigmaInit := sigmaInit)
    (body := body_g) (hBody := hBodyEq)
    (t := t) (hRefEmpty := hRefEmpty) (corr := corr)
  exact ⟨(∅ : LCS.Finset (FOAtom L hNoEq)), d', hRef⟩

/-- Theorem 9.4.1 (required helper): The SHG, ground-transcript, and
    lifting chain yields a source-language SLD-refutation without assuming
    that the source language already has a constant. The construction
    always runs in `HashLanguage L`, then lowers the indexed ground
    transcript directly back to `L`. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem foSLD_exists_refutation_from_unsat {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))

    (hD : ∀ c ∈ D, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoals : ∀ c ∈ goals, ¬ (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hGoalsNe : goals ≠ [])
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (hNodup : (D ++ goals).Nodup)
    (hVarsDisjoint : ∀ h1 ∈ D ++ goals, ∀ h2 ∈ D ++ goals, h1 ≠ h2 →
      ∀ x, ¬ (x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h1 ∧
              x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h2))
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) :
    ∃ (currentGoalVal : LCS.Finset (FOAtom L hNoEq))
      (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals currentGoalVal), (d.isRefutation (hNoEq := by all_goals exact hNoEq))

/-- Theorem 9.4.1: finite unsatisfiable Horn input admits a successful initial
    goal, and each actual atom in that same goal can be selected first (SQ20).
    Fresh variable names are local to clause uses (SQ22/SQ23). -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem foSLD_refutation_with_first_selected_from_unsat
    {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hD : ∀ c ∈ D, c.isDefinite)
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    (hUnsat : FOHornClauseSet.isUnsatisfiable hNoEq Afalsum (D ++ goals)) :
    ∃ initGoal ∈ goals,
      Nonempty (FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅) ∧
      ∀ Bi ∈ initGoal.body,
        ∃ d : FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅,
          FOSLDDerivation.firstSelectedAtom hNoEq d = some Bi

/-- Any actual atom in any nonempty residual goal of a successful trace can
    begin a successful continuation with the same program (SQ20). -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem foSLD_selection_order_independence
    {L : Language} (hNoEq : L.withoutEquality)
    (D : Set (FOHornClause L hNoEq)) (goals : List (FOHornClause L hNoEq))
    (hD : ∀ c ∈ D, c.isDefinite)
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    (d : FOSLDDerivation hNoEq D goals ∅)
    (residual : LCS.Finset (FOAtom L hNoEq))
    (hResidual : residual ∈ FOSLDDerivation.goalSequence hNoEq d)
    (Bi : FOAtom L hNoEq) (hBi : Bi ∈ residual) :
    ∃ continuation : FOSLDDerivation hNoEq D [FOHornClause.goal residual hNoEq] ∅,
      FOSLDDerivation.firstSelectedAtom hNoEq continuation = some Bi

/-- Theorem 9.4.1: an equality-free finite unsatisfiable Horn set has an
    SLD-refutation starting at a negative clause in that same set. Every atom
    of the chosen successful initial goal can be selected first (SQ20). -/
@[attach_debt, blueprint "chap9__theorem_9_4_1" (main := true)]
theorem foSLDResolution_complete
    {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (S D goals : List (FOHornClause L hNoEq))
    (hS : S = D ++ goals)
    (hD : ∀ c ∈ D, c.isDefinite)
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    (hUnsat : FOHornClauseSet.isUnsatisfiable hNoEq Afalsum S) :
    ∃ initGoal ∈ goals,
      Nonempty (FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅) ∧
      ∀ Bi ∈ initGoal.body,
        ∃ d : FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅,
          FOSLDDerivation.firstSelectedAtom hNoEq d = some Bi

/-- A selected atom leaves an existential choice of a definite input clause.
    The successful continuation uses that clause as its first side input;
    this is not a universal guarantee for all clause choices (SQ20/SQ23). -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem foSLD_selectedAtom_requiresClauseChoice
    {L : Language} (hNoEq : L.withoutEquality)
    (D : Set (FOHornClause L hNoEq)) (goals : List (FOHornClause L hNoEq))
    (hD : ∀ c ∈ D, c.isDefinite)
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    (d : FOSLDDerivation hNoEq D goals ∅)
    (residual : LCS.Finset (FOAtom L hNoEq))
    (hResidual : residual ∈ FOSLDDerivation.goalSequence hNoEq d)
    (Bi : FOAtom L hNoEq) (hBi : Bi ∈ residual) :
    ∃ clause ∈ D, clause.isDefinite ∧
      ∃ continuation : FOSLDDerivation hNoEq D [FOHornClause.goal residual hNoEq] ∅,
        FOSLDDerivation.firstSelectedAtom hNoEq continuation = some Bi ∧
        (FOSLDDerivation.inputClauses hNoEq continuation)[1]? = some clause

end LCS.SLD.FirstOrder
end
