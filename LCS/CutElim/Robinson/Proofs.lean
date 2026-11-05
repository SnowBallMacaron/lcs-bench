import LCS.CutElim.Robinson

namespace LCS.CutElim.Robinson

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax (peanoLanguage)

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.FirstOrder.Completeness.MetaTheorems

open LCS.FirstOrder.Equality.MetaTheorems

open LCS.FirstOrder.Equality

open Classical

open LCS.FirstOrder.SemanticsN

helper /-- Restrict a structure over the amalgamated language to L1. -/
def restrictLeft {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (M : Structure (languageAmalgam hI)) : Structure L1 where
  carrier := M.carrier
  carrierNonempty := M.carrierNonempty
  interpFunc := fun f ts => M.interpFunc (Quot.mk _ (.inl f))
    (fun i => ts (Fin.cast (by rfl) i))
  interpConst := fun c => M.interpConst (Quot.mk _ (.inl c))
  interpPred := fun P ts => M.interpPred (Quot.mk _ (.inl P))
    (fun i => ts (Fin.cast (by rfl) i))

helper /-- Restrict a structure over the amalgamated language to L2. -/
def restrictRight {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (M : Structure (languageAmalgam hI)) : Structure L2 where
  carrier := M.carrier
  carrierNonempty := M.carrierNonempty
  interpFunc := fun f ts => M.interpFunc (Quot.mk _ (.inr f))
    (fun i => ts (Fin.cast (by rfl) i))
  interpConst := fun c => M.interpConst (Quot.mk _ (.inr c))
  interpPred := fun P ts => M.interpPred (Quot.mk _ (.inr P))
    (fun i => ts (Fin.cast (by rfl) i))

helper /-- When the amalgamated language has a formula, inconsistency of
setUnion S1 S2 yields a validity witness. -/
theorem setUnion_inconsistent_valid {L L1 L2 : Language}
    {hI : LanguageIntersection L L1 L2}
    [Nonempty (FormulaN (languageAmalgam hI))]
    {S1 : Set (FormulaN L1)} {S2 : Set (FormulaN L2)}
    (h : ¬isConsistentSetUnified (setUnion hI S1 S2)) :
    ∃ (cs : List (FormulaN (languageAmalgam hI))),
      (∀ c, c ∈ cs → setUnion hI S1 S2 c) ∧
      sequentValid (Sequent.mk cs []) := by
-- BEGIN PROOF
  unfold isConsistentSetUnified at h
  split at h <;> rename_i heq
  · -- hasEquality = true: inconsistency via G_=-provability
    have hEmpty : ¬ isConsistentSetEqEmptySucc heq (setUnion hI S1 S2) :=
      fun hEmpty => h ((isConsistentSetEq_iff_emptySucc heq
        (setUnion hI S1 S2)).mpr hEmpty)
    obtain ⟨cs, hcs⟩ := Classical.not_forall.mp hEmpty
    obtain ⟨hmem, hprov⟩ := Classical.not_imp.mp hcs
    exact ⟨cs, hmem, soundnessGEq heq _
      (Classical.byContradiction fun hc => hprov hc)⟩
  · -- hasEquality = false: inconsistency via G-provability
    have hEmpty : ¬ LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSetEmptySucc
        (setUnion hI S1 S2) := fun hEmpty => h
      ((LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSet_iff_emptySucc
        (setUnion hI S1 S2)).mpr hEmpty)
    obtain ⟨cs, hcs⟩ := Classical.not_forall.mp hEmpty
    obtain ⟨hmem, hprov⟩ := Classical.not_imp.mp hcs
    exact ⟨cs, hmem, soundnessG_Ext _
      (Classical.byContradiction fun hc => hprov hc)⟩

proof_of robinson_joint_consistency := by
  -- BEGIN PROOF
    exact Classical.byContradiction fun hIncons => by
      letI : Nonempty (FormulaN (languageAmalgam hIntersect)) := ⟨Countable.enumerate 0⟩
      obtain ⟨cs, hcs_mem, hcs_valid⟩ := setUnion_inconsistent_valid hIncons
      have hsat : satisfiableSetN (setUnion hIntersect S1 S2) :=
        setUnion_satisfiable hIntersect hCase S1 S2
          hSent1 hSent2 hCons1 hCons2 hComplete
      obtain ⟨M, s, hMs⟩ := hsat
      obtain ⟨B, hB, _⟩ := hcs_valid M s
        (fun A hA => hMs A (hcs_mem A hA))
      simp at hB


proof_of union_consistency_not_necessary := by
  intro hUnion
  let L : Language :=
    { funSymbols := Empty
      funArity := Empty.elim
      constSymbols := Empty
      predSymbols := Unit
      predArity := fun _ => 0
      hasEquality := false }
  let e : LanguageExpansion L L :=
    { predEmbed := id
      predArityPreserve := fun _ => rfl
      predInj := fun _ _ h => h
      funEmbed := id
      funArityPreserve := fun _ => rfl
      funInj := fun _ _ h => h
      constEmbed := id
      constInj := fun _ _ h => h
      eqPreserve := id }
  let hI : LanguageIntersection L L L :=
    { expand1 := e
      expand2 := e
      eqExact1 := rfl
      eqExact2 := rfl
      predDecL1 := fun P => isTrue ⟨P, rfl⟩
      predDecL2 := fun P => isTrue ⟨P, rfl⟩
      funDecL1 := fun f => isTrue ⟨f, rfl⟩
      funDecL2 := fun f => isTrue ⟨f, rfl⟩
      constDecL1 := fun c => isTrue ⟨c, rfl⟩
      constDecL2 := fun c => isTrue ⟨c, rfl⟩ }
  let C : FormulaN L := .predN () (fun i => Fin.elim0 i)
  let S1 : Set (FormulaN L) := Set.singleton C
  let S2 : Set (FormulaN L) := Set.singleton (FormulaN.neg C)
  let M (b : Bool) : Structure L :=
    { carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => b = true }
  have hClosed : formulaFVN C = ∅ := by
    funext x
    apply propext
    exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, False.elim⟩
  have hSent1 : isSentenceSet S1 := by
    intro A hA
    change A = C at hA
    subst A
    exact hClosed
  have hSent2 : isSentenceSet S2 := by
    intro A hA
    change A = FormulaN.neg C at hA
    subst A
    exact hClosed
  letI : Nonempty (FormulaN L) := ⟨C⟩
  have hCons1 : isConsistentSetUnified S1 := by
    have hSat : satisfiableSetN S1 := by
      refine ⟨M true, fun _ => (), ?_⟩
      intro A hA
      change A = C at hA
      subst A
      exact rfl
    simpa [isConsistentSetUnified, L] using satisfiable_implies_consistentN S1 hSat
  have hCons2 : isConsistentSetUnified S2 := by
    have hSat : satisfiableSetN S2 := by
      refine ⟨M false, fun _ => (), ?_⟩
      intro A hA
      change A = FormulaN.neg C at hA
      subst A
      change ¬ (false = true)
      decide
    simpa [isConsistentSetUnified, L] using satisfiable_implies_consistentN S2 hSat
  have hCons := hUnion L L L hI S1 S2 hSent1 hSent2 hCons1 hCons2
  have hK : (languageAmalgam hI).hasEquality = false := rfl
  have hCons' : LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSet
      (setUnion hI S1 S2) := by
    simpa [isConsistentSetUnified, hK] using hCons
  let D := formulaLiftN (amalgamExpansionLeft hI) C
  have hLift : formulaLiftN (amalgamExpansionRight hI) C = D := by
    have hPred : (Quot.mk (predSymbolRel hI) (Sum.inr ())) =
        Quot.mk (predSymbolRel hI) (Sum.inl ()) := Quot.sound ⟨(), rfl, rfl⟩
    have hCong {p q : (languageAmalgam hI).predSymbols} (hp : p = q)
        (hz : (languageAmalgam hI).predArity p = 0)
        (ts : Fin ((languageAmalgam hI).predArity p) → Term (languageAmalgam hI))
        (us : Fin ((languageAmalgam hI).predArity q) → Term (languageAmalgam hI)) :
        FormulaN.predN p ts = FormulaN.predN q us := by
      subst q
      congr 1
      funext i
      exact Fin.elim0 (Fin.cast hz i)
    exact hCong hPred rfl _ _
  have hD : D ∈ setUnion hI S1 S2 := Or.inl ⟨C, rfl, rfl⟩
  have hNegD : FormulaN.neg D ∈ setUnion hI S1 S2 := by
    refine Or.inr ⟨FormulaN.neg C, rfl, ?_⟩
    change FormulaN.neg (formulaLiftN (amalgamExpansionRight hI) C) = FormulaN.neg D
    exact congrArg FormulaN.neg hLift
  obtain ⟨B, hB⟩ := hCons'
  apply hB [D, FormulaN.neg D]
    (by intro A hA; simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl <;> assumption)
  exact ⟨GProofTreeExt.onePremise (GentzenStep1Ext.negLeft [D] [] [B] D)
    (GProofTreeExt.axiom_ _ ⟨D, by simp, by simp⟩)⟩


proof_of incomplete_consistent_extensions := by
  -- REPAIR(T6-64): proof pending
  sorry


proof_of goedel_union_failure := by
  obtain ⟨C, hClosed, hUndecidable⟩ := h
  exact ⟨C, hClosed, hUndecidable,
    peano_undecidable_consistent_extensions C hClosed hUndecidable⟩


end LCS.CutElim.Robinson
