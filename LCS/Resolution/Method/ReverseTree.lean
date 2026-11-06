import LCS.Resolution.Method.Erase
import Attach
import LCS.Resolution.Method.ReverseTree.ProofsStamp

/-! # Constructive reverse conversion on resolution trees

The tree is the unfolding used to execute a finite DAG's recursion.  The
conversion carries its actual GCNF′ output and proves a bound on that output's
leaves.  Contraction during literal erasure handles redundant resolution steps.
-/

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

/-- Change the root to an ordinary containing sequent, retaining every node. -/
@[blueprint "chap4__theorem_4_3_3"]
def weakenTo {S : ClauseSequent} (t : GCNFProofTree S)
    (T : ClauseSequent) (hT : T.isOrdinary) (hSub : LCS.Finset.Subset S T) :
    GCNFProofTree T :=
  LCS.Finset.union_eq_right hSub ▸ t.weaken T hT

@[blueprint "chap4__theorem_4_3_3", simp] theorem weakenTo_leafCount {S : ClauseSequent}
    (t : GCNFProofTree S) (T : ClauseSequent) (hT : T.isOrdinary)
    (hSub : LCS.Finset.Subset S T) :
    (weakenTo t T hT hSub).leafCount = t.leafCount 

namespace ResolutionTree

/-- The actual output object, with its leaf count bounded by the number of
resolution occurrences in the input tree. -/
@[blueprint "chap4__theorem_4_3_3"]
abbrev Conversion (T : ResolutionTree) :=
  { t : GCNFProofTree T.inputs // t.leafCount ≤ T.treeStepCount }



/-- In a genuine final resolution to □, the premises are conjugate units. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem units_of_empty {A B : ResolutionTree} {L : Literal}
    (hWF : (resolve A B L).IsWellFormed)
    (hEmpty : (resolve A B L).label = GCNF.Clause.empty) :
    A.label = GCNF.Clause.single L ∧
      B.label = GCNF.Clause.single L.conjugate 

@[blueprint "chap4__theorem_4_3_3"]
theorem unit_refutation_label (A B : ResolutionTree) (L : Literal)
    (hA : A.label = GCNF.Clause.single L)
    (hB : B.label = GCNF.Clause.single L.conjugate) :
    (resolve A B L).label = GCNF.Clause.empty 

@[blueprint "chap4__theorem_4_3_3"]
def unit_axiom (S : ClauseSequent) (L : Literal)
    (hS : S.isOrdinary) (hL : GCNF.Clause.single L ∈ S)
    (hR : GCNF.Clause.single L.conjugate ∈ S) : GCNFProofTree S := by
  apply GCNFProofTree.axiom_ S hS
  cases L with
  | pos P => exact ⟨P, hL, hR⟩
  | neg P => exact ⟨P, hR, hL⟩

@[blueprint "chap4__theorem_4_3_3"]
def oldInputs (U : ResolutionTree) (S : ClauseSequent) : ClauseSequent :=
  LCS.Finset.filter (fun C => decide (C ∈ S)) U.inputs

@[blueprint "chap4__theorem_4_3_3"]
def newInputs (U : ResolutionTree) (S : ClauseSequent) : ClauseSequent :=
  LCS.Finset.filter (fun C => decide (C ∉ S)) U.inputs

@[blueprint "chap4__theorem_4_3_3"]
theorem inputs_partition (U : ResolutionTree) (S : ClauseSequent) :
    LCS.Finset.union (oldInputs U S) (newInputs U S) = U.inputs 

@[blueprint "chap4__theorem_4_3_3"]
theorem subset_of_newInputs_empty (U : ResolutionTree) (S : ClauseSequent)
    (h : newInputs U S = LCS.Finset.empty) : LCS.Finset.Subset U.inputs S 

/-- One recursive case. The chosen unit premise is nonterminal.  Its literal
is erased for the first recursive call; the second call cuts that premise to
a unit input.  Existing inputs permit exactly the two source weakening cases. -/
@[blueprint "chap4__theorem_4_3_3"]
def convertSplit (A B : ResolutionTree) (L : Literal)
    (S : ClauseSequent) (hS : S.isOrdinary)
    (hAS : LCS.Finset.Subset A.inputs S) (hBS : LCS.Finset.Subset B.inputs S)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hALabel : A.label = GCNF.Clause.single L)
    (hBLabel : B.label = GCNF.Clause.single L.conjugate)
    (hPos : 0 < A.treeStepCount)
    (rec : ∀ U : ResolutionTree,
      U.treeStepCount < 1 + A.treeStepCount + B.treeStepCount →
      U.IsWellFormed → U.label = GCNF.Clause.empty →
      U.inputs.isOrdinary → Conversion U) :
    {t : GCNFProofTree S // t.leafCount ≤ 1 + A.treeStepCount + B.treeStepCount} := by
  let cut := resolve (axiom_ (GCNF.Clause.single L)) B L
  have hCutWF : cut.IsWellFormed :=
    ⟨True.intro, hB, (LCS.Finset.mem_singleton _ _).mpr rfl,
      hBLabel ▸ (LCS.Finset.mem_singleton _ _).mpr rfl⟩
  have hCutEmpty : cut.label = GCNF.Clause.empty :=
    unit_refutation_label _ B L rfl hBLabel
  have hCutOrd : cut.inputs.isOrdinary := by
    apply ClauseSequent.ordinary_union
    · exact ClauseSequent.ordinary_single (GCNF.Clause.single_ordinary L)
    · exact ClauseSequent.ordinary_subset hS hBS
  have hCutLt : cut.treeStepCount < 1 + A.treeStepCount + B.treeStepCount := by
    simp only [cut, treeStepCount]
    omega
  let second := rec cut hCutLt hCutWF hCutEmpty hCutOrd
  if hUnit : GCNF.Clause.single L ∈ S then
    have hCutSub : LCS.Finset.Subset cut.inputs S := by
      intro C hC
      rcases LCS.Finset.mem_union.mp hC with hC | hC
      · exact (LCS.Finset.mem_singleton _ _).mp hC ▸ hUnit
      · exact hBS C hC
    exact ⟨weakenTo second.val S hS hCutSub, by
      rw [weakenTo_leafCount]
      exact Nat.le_trans second.property (Nat.le_of_lt hCutLt)⟩
  else
    let erased := A.eraseLiteral L
    have hErasedOrd : erased.inputs.isOrdinary :=
      eraseLiteral_inputs_ordinary A L (ClauseSequent.ordinary_subset hS hAS)
        (fun h => hUnit (hAS _ h))
    have hErasedLt : erased.treeStepCount < 1 + A.treeStepCount + B.treeStepCount := by
      change (A.eraseLiteral L).treeStepCount < _
      have hle := eraseLiteral_treeStepCount_le A L
      omega
    let first := rec erased hErasedLt (eraseLiteral_isWellFormed A L hA)
      (eraseLiteral_unit_label A L hALabel) hErasedOrd
    if hOld : newInputs erased S = LCS.Finset.empty then
      exact ⟨weakenTo first.val S hS (subset_of_newInputs_empty erased S hOld), by
        rw [weakenTo_leafCount]
        exact Nat.le_trans first.property (Nat.le_of_lt hErasedLt)⟩
    else
      let Cs := newInputs erased S
      let Gamma1 := oldInputs erased S
      have hCsSub : LCS.Finset.Subset Cs erased.inputs :=
        fun _ h => (LCS.Finset.mem_filter.mp h).1
      have hRestore : LCS.Finset.Subset
          (ClauseSequent.mapSet Cs (fun C => clauseWithLiteral C L)) S := by
        intro C hC
        obtain ⟨D, hD, rfl⟩ := LCS.Finset.mem_image.mp hC
        have hD' := LCS.Finset.mem_filter.mp hD
        have hNotS : D ∉ S := of_decide_eq_true hD'.2
        exact hAS _ (eraseLiteral_novel_input_restore A L D hD'.1
          (fun h => hNotS (hAS D h)))
      have hConclusion : LCS.Finset.union S
          (ClauseSequent.mapSet Cs (fun C => clauseWithLiteral C L)) = S := by
        rw [LCS.Finset.union_comm]
        exact LCS.Finset.union_eq_right hRestore
      have hGamma1 : LCS.Finset.Subset Gamma1 S := by
        intro C hC
        exact of_decide_eq_true (LCS.Finset.mem_filter.mp hC).2
      have hLeftEq : LCS.Finset.union Gamma1 Cs = erased.inputs :=
        inputs_partition erased S
      have hRightEq : LCS.Finset.union B.inputs
          (ClauseSequent.single (GCNF.Clause.single L)) = cut.inputs :=
        LCS.Finset.union_comm _ _
      let tree := GCNFProofTree.rule S Cs L Cs Gamma1 B.inputs hS
        (ClauseSequent.ordinary_subset hErasedOrd hCsSub)
        (hLeftEq.symm ▸ first.val) (hRightEq.symm ▸ second.val)
        (LCS.Finset.nonempty_of_ne_empty Cs hOld) (fun _ h => h)
        (fun C h => hConclusion.symm ▸ hGamma1 C h)
        (fun C h => hConclusion.symm ▸ hBS C h)
      refine ⟨hConclusion ▸ tree, ?_⟩
      simp only [GCNFProofTree.leafCount_cast, tree, GCNFProofTree.leafCount]
      have hf := first.property
      change first.val.leafCount ≤ (A.eraseLiteral L).treeStepCount at hf
      have hs := second.property
      have he := eraseLiteral_treeStepCount_le A L
      simp only [cut, treeStepCount] at hs
      omega

/-- Proof of Theorem 4.3.3, ordinary-input reading: an executable recursive
conversion. Its return value is the proof tree, together with a bound on the
actual number of axiom occurrences. The source's deletion step is corrected
by `eraseLiteral`, which contracts inferences with a vanished pivot. -/
@[blueprint "chap4__theorem_4_3_3"]
def toGCNF (T : ResolutionTree) (hWF : T.IsWellFormed)
    (hEmpty : T.label = GCNF.Clause.empty) (hOrdinary : T.inputs.isOrdinary) :
    Conversion T := by
  cases hT : T with
  | axiom_ C =>
    simp only [hT] at hWF hEmpty hOrdinary ⊢
    exact (hOrdinary C ((LCS.Finset.mem_singleton _ _).mpr rfl) hEmpty).elim
  | resolve A B L =>
    simp only [hT] at hWF hEmpty hOrdinary ⊢
    have hUnits := units_of_empty hWF hEmpty
    have hAS : LCS.Finset.Subset A.inputs (resolve A B L).inputs :=
      fun _ h => LCS.Finset.mem_union.mpr (Or.inl h)
    have hBS : LCS.Finset.Subset B.inputs (resolve A B L).inputs :=
      fun _ h => LCS.Finset.mem_union.mpr (Or.inr h)
    cases A with
    | axiom_ C =>
      cases B with
      | axiom_ D =>
        let t := unit_axiom (resolve (axiom_ C) (axiom_ D) L).inputs L hOrdinary
          (hUnits.1 ▸ hAS C ((LCS.Finset.mem_singleton _ _).mpr rfl))
          (hUnits.2 ▸ hBS D ((LCS.Finset.mem_singleton _ _).mpr rfl))
        refine ⟨t, ?_⟩
        cases L <;> exact Nat.le_refl 1
      | resolve B1 B2 P =>
        have hConj : L.conjugate.conjugate = L := by cases L <;> rfl
        let result := convertSplit (resolve B1 B2 P) (axiom_ C) L.conjugate
          (resolve (axiom_ C) (resolve B1 B2 P) L).inputs hOrdinary hBS hAS
          hWF.2.1 hWF.1 hUnits.2 (hConj.symm ▸ hUnits.1)
          (by simp only [treeStepCount]; omega)
          (fun U hu hU he ho => toGCNF U hU he ho)
        refine ⟨result.val, ?_⟩
        have h := result.property
        simpa only [treeStepCount, Nat.add_zero, Nat.zero_add] using h
    | resolve A1 A2 P =>
      exact convertSplit (resolve A1 A2 P) B L
        (resolve (resolve A1 A2 P) B L).inputs hOrdinary hAS hBS
        hWF.1 hWF.2.1 hUnits.1 hUnits.2
        (by simp only [treeStepCount]; omega)
        (fun U hu hU he ho => toGCNF U hU he ho)
termination_by T.treeStepCount
decreasing_by
  all_goals simp only [hT, treeStepCount] at *; omega






-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
-- ATTACH-BLOCKER: used by LCS.Resolution.Method.Reverse
/-- The returned tree is the object counted in the reverse size estimate. -/
theorem toGCNF_leafCount_le (T : ResolutionTree) (hWF : T.IsWellFormed)
    (hEmpty : T.label = GCNF.Clause.empty) (hOrdinary : T.inputs.isOrdinary) :
    (toGCNF T hWF hEmpty hOrdinary).val.leafCount ≤ T.treeStepCount :=
  (toGCNF T hWF hEmpty hOrdinary).property

end ResolutionTree
end LCS.Resolution.Method
