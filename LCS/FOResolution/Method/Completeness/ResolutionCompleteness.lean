import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.FOResolution.Method.Completeness.LiftingLemma
import LCS.FOResolution.Method.Completeness.RefutationLifting
import Attach
import LCS.FOResolution.Method.Completeness.ResolutionCompleteness.ProofsStamp

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical

-- ===================================================================
-- Theorem 8.5.1 (helper): certified ground-tree bridge
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- A ground clause has no free variables in the sense used by separating
    substitutions. -/
theorem clauseFV_eq_empty_of_ground {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (hGround : C.isGround) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) C = Set.empty := by
  ext x
  constructor
  · rintro ⟨lit, hLit, hVar⟩
    have : (FOClause.vars hNoEq C) x := ⟨lit, hLit, hVar⟩
    dsimp only [FOClause.vars] at this; rw [hGround] at this
    exact this
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Identity substitutions separate two ground clauses because both clauses
    have empty free-variable sets. -/
theorem identity_isSeparatingPair_of_ground {L : Language} (hNoEq : L.withoutEquality)
    (A B : FOClause L hNoEq)
    (hA : A.isGround) (hB : B.isGround) :
    (IsSeparatingPair (hNoEq := by all_goals exact hNoEq))
      (fun n => Term.var n) (fun n => Term.var n) A B := by
  unfold IsSeparatingPair
  rw [show (clauseFV (hNoEq := by all_goals exact hNoEq)) A = Set.empty from (clauseFV_eq_empty_of_ground (hNoEq := by all_goals exact hNoEq)) A hA,
      show (clauseFV (hNoEq := by all_goals exact hNoEq)) B = Set.empty from (clauseFV_eq_empty_of_ground (hNoEq := by all_goals exact hNoEq)) B hB]
  simp [substIsVarOnSet, substInjectiveOnSet]
  ext n
  constructor
  · rintro ⟨⟨x, hx, _⟩, _⟩
    exact hx.elim
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Leaf provenance is monotone under implication of source predicates. -/
theorem methodTree_leavesFrom_mono {L : Language} (hNoEq : L.withoutEquality)
    (T : FOResolutionTree L hNoEq)
    {S S' : FOClause L hNoEq → Prop}
    (hLeaves : (T.leavesFrom (hNoEq := by all_goals exact hNoEq)) S)
    (hMono : ∀ C, S C → S' C) :
    (T.leavesFrom (hNoEq := by all_goals exact hNoEq)) S' := by
  induction T with
  | axiom_ C =>
      exact hMono C hLeaves
  | resolve T1 T2 resolvedA resolvedB rho rho' sigma ih1 ih2 =>
      exact ⟨ih1 hLeaves.1, ih2 hLeaves.2⟩

/-- Convert a proof-relevant pivot-based ground-resolution tree into the
    separating-pair tree used by the first-order resolution method.  The
    conversion preserves leaves and root membership extensionally; every
    generated node carries the exact `IsResolventVia` certificate. -/
theorem groundTree_to_method {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (T : LCS.FOResolution.GroundResolution.FOResolutionTree L hNoEq)
    (C : FOClause L hNoEq)
    (hSpec :
      (LCS.FOResolution.GroundResolution.FOResolutionTree.labelSpec (hNoEq := by all_goals exact hNoEq)) T C)
    (S : FOClause L hNoEq → Prop)
    (hLeaves :
      (LCS.FOResolution.GroundResolution.FOResolutionTree.leavesFrom (hNoEq := by all_goals exact hNoEq)) T S) :
    ∃ H : FOResolutionTree L hNoEq,
      (H.leavesFrom (hNoEq := by all_goals exact hNoEq)) S ∧
      (H.isWellFormed (hNoEq := by all_goals exact hNoEq)) ∧
      (LCS.FOResolution.Method.Completeness.FOResolutionTree.allLabelsGround (hNoEq := by all_goals exact hNoEq)) H ∧
      (∀ lit, lit ∈ (H.label (hNoEq := by all_goals exact hNoEq)) ↔ lit ∈ C) := by
  induction T generalizing C with
  | axiom_ source =>
      refine ⟨.axiom_ source, hLeaves, trivial, hSpec.2, ?_⟩
      intro lit
      simp [FOResolutionTree.label, hSpec.1]
  | resolve T1 T2 pivot ih1 ih2 =>
      obtain ⟨C1, C2, hSpec1, hSpec2, hPivot, hConj,
        hCGround, hCmem⟩ := hSpec
      obtain ⟨hLeaves1, hLeaves2⟩ := hLeaves
      obtain ⟨H1, hH1Leaves, hH1WF, hH1Ground, hH1mem⟩ :=
        ih1 C1 hSpec1 hLeaves1
      obtain ⟨H2, hH2Leaves, hH2WF, hH2Ground, hH2mem⟩ :=
        ih2 C2 hSpec2 hLeaves2
      have hGround1 : (FOClause.isGround (by all_goals exact hNoEq)) (H1.label (hNoEq := by all_goals exact hNoEq)) :=
        (FOResolutionTree.allLabelsGround_label (hNoEq := by all_goals exact hNoEq)) H1 hH1Ground
      have hGround2 : (FOClause.isGround (by all_goals exact hNoEq)) (H2.label (hNoEq := by all_goals exact hNoEq)) :=
        (FOResolutionTree.allLabelsGround_label (hNoEq := by all_goals exact hNoEq)) H2 hH2Ground
      have hSub1 : IsSublist [pivot] (H1.label (hNoEq := by all_goals exact hNoEq)) := by
        intro lit hLit
        simp only [List.mem_singleton] at hLit
        subst lit
        exact (hH1mem pivot).2 hPivot
      have hSub2 : IsSublist [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot] (H2.label (hNoEq := by all_goals exact hNoEq)) := by
        intro lit hLit
        simp only [List.mem_singleton] at hLit
        subst lit
        exact (hH2mem ((FOLiteral.conjugate (by all_goals exact hNoEq)) pivot)).2 hConj
      have hSameSign : (LitSetSameSign (hNoEq := by all_goals exact hNoEq)) [pivot] := by
        cases pivot with
        | pos atom =>
            left
            intro lit hLit
            simp only [List.mem_singleton] at hLit
            subst lit
            exact ⟨atom, rfl⟩
        | neg atom =>
            right
            intro lit hLit
            simp only [List.mem_singleton] at hLit
            subst lit
            exact ⟨atom, rfl⟩
      have hOpposite : (LitSetOppositeSign (hNoEq := by all_goals exact hNoEq))
          [pivot] [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot] := by
        cases pivot with
        | pos atom =>
            left
            constructor
            · intro lit hLit
              simp only [List.mem_singleton] at hLit
              subst lit
              exact ⟨atom, rfl⟩
            · intro lit hLit
              simp only [List.mem_singleton] at hLit
              subst lit
              exact ⟨atom, rfl⟩
        | neg atom =>
            right
            constructor
            · intro lit hLit
              simp only [List.mem_singleton] at hLit
              subst lit
              exact ⟨atom, rfl⟩
            · intro lit hLit
              simp only [List.mem_singleton] at hLit
              subst lit
              exact ⟨atom, rfl⟩
      have hSamePred :
          (LitSetSamePred (hNoEq := by all_goals exact hNoEq))
            ([pivot] ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot]) := by
        cases pivot with
        | pos atom =>
            cases atom with
            | predN P args =>
                refine ⟨P, ?_⟩
                intro lit hLit
                simp [LitSetConjugate, FOLiteral.conjugate, FOLiteralCore.conjugate] at hLit
                subst lit
                exact ⟨args, rfl⟩
            | eq_ hEq lhs rhs =>
                have : False := by
                  cases hNoEq.symm.trans hEq
                exact this.elim
        | neg atom =>
            cases atom with
            | predN P args =>
                refine ⟨P, ?_⟩
                intro lit hLit
                simp [LitSetConjugate, FOLiteral.conjugate, FOLiteralCore.conjugate] at hLit
                subst lit
                exact ⟨args, rfl⟩
            | eq_ hEq lhs rhs =>
                have : False := by
                  cases hNoEq.symm.trans hEq
                exact this.elim
      have hSep := (identity_isSeparatingPair_of_ground (hNoEq := by all_goals exact hNoEq))
        (H1.label (hNoEq := by all_goals exact hNoEq)) (H2.label (hNoEq := by all_goals exact hNoEq)) hGround1 hGround2
      have hPairData :
          ∃ pairs : List (Term L × Term L),
            (litSetUnifPairs (hNoEq := by all_goals exact hNoEq))
              ((LitSetAbs (hNoEq := by all_goals exact hNoEq))
                ((substLits (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) [pivot] ++
                 (substLits (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n)
                   ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot]))) =
              some pairs ∧
            IsPairwiseUnifier (fun n => Term.var n) pairs := by
        cases pivot with
        | pos atom =>
            cases atom with
            | predN P args =>
                refine ⟨List.ofFn (fun i => (args i, args i)), ?_, ?_⟩
                · simp [(substLits_id (hNoEq := by all_goals exact hNoEq)), LitSetAbs, LitSetConjugate,
                    FOLiteral.conjugate, FOLiteralCore.conjugate, litSetUnifPairs,
                    litSetUnifPairsAgainst, literalAtom, atomUnifPairs?]
                · intro pair hPair
                  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hPair
                  rfl
            | eq_ hEq lhs rhs =>
                have : False := by
                  cases hNoEq.symm.trans hEq
                exact this.elim
        | neg atom =>
            cases atom with
            | predN P args =>
                refine ⟨List.ofFn (fun i => (args i, args i)), ?_, ?_⟩
                · simp [(substLits_id (hNoEq := by all_goals exact hNoEq)), LitSetAbs, LitSetConjugate,
                    FOLiteral.conjugate, FOLiteralCore.conjugate, litSetUnifPairs,
                    litSetUnifPairsAgainst, literalAtom, atomUnifPairs?]
                · intro pair hPair
                  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hPair
                  rfl
            | eq_ hEq lhs rhs =>
                have : False := by
                  cases hNoEq.symm.trans hEq
                exact this.elim
      obtain ⟨pairs, hPairs, hIdUnif⟩ := hPairData
      obtain ⟨mu, hMuUnif, hMuMGU⟩ :=
        mgu_exists_of_pairwise_unifiable pairs
          (fun n => Term.var n) hIdUnif
      let H := FOResolutionTree.resolve H1 H2
        [pivot] [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot]
        (fun n => Term.var n) (fun n => Term.var n) mu
      have hLeftGround :
          (FOClause.isGround (by all_goals exact hNoEq)) (listDiff (H1.label (hNoEq := by all_goals exact hNoEq)) [pivot]) :=
        (isGround_of_sublist (hNoEq := by all_goals exact hNoEq)) (H1.label (hNoEq := by all_goals exact hNoEq)) _ hGround1
          (fun lit hLit => (List.mem_filter.mp hLit).1)
      have hRightGround :
          (FOClause.isGround (by all_goals exact hNoEq))
            (listDiff (H2.label (hNoEq := by all_goals exact hNoEq)) [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot]) :=
        (isGround_of_sublist (hNoEq := by all_goals exact hNoEq)) (H2.label (hNoEq := by all_goals exact hNoEq)) _ hGround2
          (fun lit hLit => (List.mem_filter.mp hLit).1)
      have hBaseGround :
          (FOClause.isGround (by all_goals exact hNoEq))
            (listDiff (H1.label (hNoEq := by all_goals exact hNoEq)) [pivot] ++
             listDiff (H2.label (hNoEq := by all_goals exact hNoEq)) [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot]) :=
        (isGround_append (hNoEq := by all_goals exact hNoEq)) _ _ hLeftGround hRightGround
      have hLabel :
          (H.label (hNoEq := by all_goals exact hNoEq)) =
            listDiff (H1.label (hNoEq := by all_goals exact hNoEq)) [pivot] ++
            listDiff (H2.label (hNoEq := by all_goals exact hNoEq)) [(FOLiteral.conjugate (by all_goals exact hNoEq)) pivot] := by
        simp only [H, FOResolutionTree.label, (substLits_id (hNoEq := by all_goals exact hNoEq))]
        exact (substLits_ground_id (hNoEq := by all_goals exact hNoEq)) _ mu hBaseGround
      refine ⟨H, ⟨hH1Leaves, hH2Leaves⟩, ?_, ?_, ?_⟩
      · refine ⟨hH1WF, hH2WF, ?_⟩
        exact ⟨hSub1, hSub2, by simp, by simp, hSameSign, hOpposite,
          hSamePred, hSep, ⟨pairs, hPairs, hMuUnif, hMuMGU⟩, fun _ => Iff.rfl⟩
      · exact ⟨hH1Ground, hH2Ground, hLabel ▸ hBaseGround⟩
      · intro lit
        rw [hLabel]
        simpa [listDiff, hH1mem, hH2mem] using (hCmem lit).symm

-- ===================================================================
-- Theorem 8.5.1: Completeness of first-order resolution
-- ===================================================================

/-- Proof of Theorem 8.5.1 (conditional endpoint): an exact midsequent of the
    canonical clause sentence yields a resolution refutation in the original
    language. -/
theorem clauseSentence_midsequent_resolution_refutation
    {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FormulaN L)]
    [DecidableEq (FOLiteral L hNoEq)]
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hP : (ClauseSentenceProperties (hNoEq := by all_goals exact hNoEq)) A S head tail)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail))
      LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    ∃ D : FOResolutionDAG L hNoEq,
      (FOResolutionDAG.isResolutionRefutation (hNoEq := by all_goals exact hNoEq)) D S := by
  classical
  have hFreshNoEq : (FreshGroundLanguage L).withoutEquality :=
    (FreshGroundLanguage.withoutEquality_iff L).2
      hP.language_without_equality
  obtain ⟨Sg, hSgGround, hSgInstances, hSgUnsat⟩ :=
    (clauseSentence_midsequent_groundInstances (hNoEq := by all_goals exact hNoEq))
      A S head tail hP mid hMid
  obtain ⟨groundTree, _hGroundSource, hGroundLeaves, hGroundRoot⟩ :=
    (LCS.FOResolution.GroundResolution.ground_resolution_completeness (hNoEq := by all_goals exact hNoEq))
      hFreshNoEq Sg hSgGround hSgUnsat
  obtain ⟨methodTree, hMethodLeaves, hMethodWF, hMethodGround,
      hMethodRoot⟩ :=
    (groundTree_to_method (hNoEq := hFreshNoEq)) groundTree [] hGroundRoot
      (fun c => c ∈ Sg) hGroundLeaves
  have hMethodLeaves' :
      (methodTree.leavesFrom (hNoEq := by all_goals exact hNoEq))
        (fun c =>
          ∃ (Cfresh : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
            (sigma : Nat → Term (FreshGroundLanguage L)),
            (∃ C : FOClause L hNoEq,
              S C ∧ Cfresh = (FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C) ∧
            (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma Cfresh) ∧
            c = (substLits (hNoEq := by all_goals exact hNoEq)) sigma Cfresh) := by
    apply (methodTree_leavesFrom_mono (hNoEq := by all_goals exact hNoEq)) methodTree hMethodLeaves
    intro c hc
    obtain ⟨C, sigma, hSC, hEq⟩ := hSgInstances c hc
    refine ⟨(FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C, sigma,
      ⟨C, hSC, rfl⟩, ?_, hEq⟩
    rw [← hEq]
    exact hSgGround c hc
  have hMethodLabel : (methodTree.label (hNoEq := by all_goals exact hNoEq)) = [] := by
    cases hLabel : (methodTree.label (hNoEq := by all_goals exact hNoEq)) with
    | nil => rfl
    | cons lit rest =>
        have hLit : lit ∈ (methodTree.label (hNoEq := by all_goals exact hNoEq)) := by
          rw [hLabel]
          exact List.mem_cons_self
        have : lit ∈
            ([] : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :=
          (hMethodRoot lit).1 hLit
        exact (List.not_mem_nil this).elim
  -- REPAIR(T8-80): proof pending
  -- Pass the ground tree through the finite quotient-family lifting theorem,
  -- then transport its empty-root component back to the tree endpoint.
  sorry

/-- Theorem 8.5.1: (Completeness of resolution, without equality) If a
    finite clause set S is unsatisfiable under direct clause semantics,
    there is a resolution refutation for S. This includes the singleton
    empty clause in an atomless language. -/
@[blueprint "chap8__theorem_8_5_1" (main := true)]
theorem resolution_completeness_fo {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (hFinite : Set.Finite S)
    (hUnsat : (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) S)
    :
    ∃ (D : FOResolutionDAG L hNoEq),
      (FOResolutionDAG.isResolutionRefutation (hNoEq := by all_goals exact hNoEq)) D S

end LCS.FOResolution.Method.Completeness
end
