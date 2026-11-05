import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.FOResolution.Method.Completeness.Substitutions
import LCS.FOResolution.Method.Completeness.Lifting
import Attach
import LCS.FOResolution.Method.Completeness.Completeness.ProofsStamp

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
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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
-- Lemma 8.5.4: Lifting lemma for resolution refutations
-- ===================================================================

/-- Lemma 8.5.4 (companion): a finite quotient DAG is a resolution DAG
    for S when its leaves belong to S and each internal occurrence has
    exactly two ordered premises and a lawful resolvent. The two premises
    may represent the same quotient vertex. Clause-only labels use the
    simplified convention following Definition 8.5.3. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionDAGFor {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (H : LCS.Resolution.Method.DAG (FOClause L hNoEq))
    (S : FOClause L hNoEq → Prop) : Prop :=
  Set.Finite H.tree.domain.dom ∧
  (∀ a, a ∈ H.tree.domain.dom → ∀ i, a ++ [i] ∈ H.tree.domain.dom → i < 2) ∧
  (∀ a, a ∈ H.tree.domain.dom →
    a ++ [0] ∈ H.tree.domain.dom → a ++ [1] ∈ H.tree.domain.dom) ∧
  (∀ a (ha : a ∈ H.tree.domain.dom),
    (¬ a ++ [0] ∈ H.tree.domain.dom) → S (H.tree.label a ha)) ∧
  (∀ a (ha : a ∈ H.tree.domain.dom)
    (h0 : a ++ [0] ∈ H.tree.domain.dom)
    (h1 : a ++ [1] ∈ H.tree.domain.dom),
    IsResolvent hNoEq (H.tree.label a ha)
      (H.tree.label (a ++ [0]) h0) (H.tree.label (a ++ [1]) h1))

/-- Lemma 8.5.4 (companion): every actual node of the ground DAG carries
    a ground clause, including internal nodes and the root. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionDAGGround {L : Language} (hNoEq : L.withoutEquality)
    (H : LCS.Resolution.Method.DAG (FOClause L hNoEq)) : Prop :=
  ∀ u C, FOResolutionDAGLabel hNoEq H u C → FOClause.isGround hNoEq C

/-- Lemma 8.5.4 (companion): an allowed ground instance of a clause of S.
    The caller may select the allowed substitutions. Their moved support is
    finite, moved images are closed, and the resulting clause is ground;
    clauses are compared by literal membership. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOSelectedGroundInstance {L : Language} (hNoEq : L.withoutEquality)
    (S : FOClause L hNoEq → Prop)
    (select : FOClause L hNoEq → (Nat → Term L) → Prop)
    (C_g : FOClause L hNoEq) : Prop :=
  ∃ (C : FOClause L hNoEq) (sigma : Nat → Term L) (support : List Nat),
    S C ∧ select C sigma ∧
    (∀ x, x ∉ support → sigma x = Term.var x) ∧
    (∀ x, sigma x ≠ Term.var x → termFV (sigma x) = Set.empty) ∧
    FOClause.isGround hNoEq C_g ∧
    (∀ lit, lit ∈ C_g ↔ lit ∈ substLits hNoEq sigma C)

/-- Lemma 8.5.4: every finite family of finite ground resolution DAGs for
    selected ground instances of S lifts to a finite family of lawful
    resolution DAGs for S. Every target component is the rooted, onto image
    of a lifted component, with the node-local ground substitutions carried
    by FOResolutionTreeHom; every lifted component maps to a target component.
    S itself may be arbitrary: only the displayed derivations are finite. -/
@[attach_debt, blueprint "chap8__lemma_8_5_4" (main := true)]
theorem lifting_lemma_refutation {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (groundInstances : FOClause L hNoEq → (Nat → Term L) → Prop)
    (G_g : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)))
    (hFinite : Set.Finite G_g)
    (hWF : ∀ H_g, G_g H_g →
      FOResolutionDAGFor hNoEq H_g (FOSelectedGroundInstance hNoEq S groundInstances))
    (hAllGround : ∀ H_g, G_g H_g → FOResolutionDAGGround hNoEq H_g) :
    ∃ G : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)),
      Set.Finite G ∧
      (∀ H, G H → FOResolutionDAGFor hNoEq H S) ∧
      (∀ H_g, G_g H_g → ∃ H, G H ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g)) ∧
      (∀ H, G H → ∃ H_g, G_g H_g ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g))

/-- Lemma 8.5.4 (companion): the finite-family lifting conclusion retains
    lawfulness of every lifted component together with the full node maps. -/
@[blueprint "chap8__lemma_8_5_4"]
theorem lifting_lemma_refutation_wf {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (groundInstances : FOClause L hNoEq → (Nat → Term L) → Prop)
    (G_g : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)))
    (hFinite : Set.Finite G_g)
    (hWF : ∀ H_g, G_g H_g →
      FOResolutionDAGFor hNoEq H_g (FOSelectedGroundInstance hNoEq S groundInstances))
    (hAllGround : ∀ H_g, G_g H_g → FOResolutionDAGGround hNoEq H_g) :
    ∃ G : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)),
      Set.Finite G ∧
      (∀ H, G H → FOResolutionDAGFor hNoEq H S) ∧
      (∀ H_g, G_g H_g → ∃ H, G H ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g)) ∧
      (∀ H, G H → ∃ H_g, G_g H_g ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g))

-- ===================================================================
-- Theorem 8.5.1: Completeness of first-order resolution
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Theorem 8.5.1 (endpoint helper): a well-formed refutation in
    the conservative fresh extension whose leaves are lifted clauses descends
    to a refutation in the original language. -/
theorem lower_fresh_resolution_refutation {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (S : FOClause L hNoEq → Prop)
    (H : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hLeaves :
      (H.leavesFrom (hNoEq := by all_goals exact hNoEq))
        (fun C => ∃ D, S D ∧ C = (FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) D))
    (hWF : (H.isWellFormed (hNoEq := by all_goals exact hNoEq)))
    (hEmpty : (H.label (hNoEq := by all_goals exact hNoEq)) = []) :
    ∃ D : FOResolutionDAG L hNoEq,
      (FOResolutionDAG.isResolutionRefutation (hNoEq := by all_goals exact hNoEq)) D S := by
  have hOriginalLeaves :
      (H.leavesFrom (hNoEq := by all_goals exact hNoEq)) (FreshGroundLanguage.IsOriginalClause (hNoEq := by all_goals exact hNoEq)) := by
    apply (methodTree_leavesFrom_mono (hNoEq := by all_goals exact hNoEq)) H hLeaves
    rintro C ⟨D, _, rfl⟩
    exact (FreshGroundLanguage.liftClause_isOriginal (hNoEq := by all_goals exact hNoEq)) D
  have hOriginal : (FOResolutionTree.AllOriginal (hNoEq := by all_goals exact hNoEq)) H :=
    (FOResolutionTree.AllOriginal.of_wellFormed (hNoEq := by all_goals exact hNoEq)) hOriginalLeaves hWF
  let U := (FOResolutionTree.lower (hNoEq := by all_goals exact hNoEq)) H hOriginal
  refine ⟨[U], U, rfl, ?_, ?_, ?_⟩
  · exact (FOResolutionTree.lower_leavesFrom (hNoEq := by all_goals exact hNoEq)) hOriginal hLeaves
  · exact (FOResolutionTree.lower_isWellFormed (hNoEq := by all_goals exact hNoEq)) H hOriginal hWF
  · rw [(FOResolutionTree.lower_label (hNoEq := by all_goals exact hNoEq)) H hOriginal]
    apply (FreshGroundLanguage.liftClause_injective (hNoEq := by all_goals exact hNoEq))
    rw [(FreshGroundLanguage.liftClause_lowerClause (hNoEq := by all_goals exact hNoEq))]
    exact hEmpty
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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
namespace Formula

/-- Theorem 8.5.2 (companion): Predicate that a formula is in prenex
    form: all quantifiers appear at the front, preceding the
    quantifier-free matrix. -/
@[blueprint "chap8__theorem_8_5_2"]
def isPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => Formula.isPrenex A
  | .ex _ A => Formula.isPrenex A
  | A => ¬ (∃ i B, A = FormulaN.all i B ∨ A = FormulaN.ex i B) ∧
         formulaQuantifierFree A
where
  /-- A formula is quantifier-free if it contains no quantifiers. -/
  formulaQuantifierFree {L : Language} : FormulaN L → Prop
    | .predN _ _ => True
    | .eq_ _ _ _ => True
    | .neg A => formulaQuantifierFree A
    | .conj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .disj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .impl A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .all _ _ => False
    | .ex _ _ => False

end Formula
end LCS.FOResolution.Method.Completeness
end

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
namespace Formula

/-- Theorem 8.5.2 (companion): Canonical wrapper for the clause-form
    module's predicate that strips a leading quantifier prefix and
    requires the remaining matrix to be in conjunctive normal form. -/
@[blueprint "chap8__theorem_8_5_2"]
def matrixIsCNF {L : Language} (A : FormulaN L) : Prop :=
  LCS.FOResolution.ClauseForm.Formula.matrixIsCNF A

end Formula
end LCS.FOResolution.Method.Completeness
end

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

/-- Theorem 8.5.2 (companion): Predicate that the sequent (A ->) is
    LK-provable. Per Gallier §8.5.2, this means the sequent with A on
    the antecedent and empty succedent has an LK proof. Wired to the
    real LK proof system `folkProvable` from Chapter 6. -/
@[blueprint "chap8__theorem_8_5_2"]
def isLKProvable {L : Language} (A : FormulaN L) : Prop :=
  folkProvable (Sequent.mk [A] [])

end LCS.FOResolution.Method.Completeness
end

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
namespace FOClauseForm
-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Convert a proof-certified disjunction of literals into a clause.
    Invalid formula shapes have no fallback branch: their certification
    hypotheses are contradictory. -/
noncomputable def clauseOfDisj {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (hDisj :
      LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals A) :
    FOClause L hNoEq := by
  induction A with
  | predN P args => exact [.pos (.predN P args)]
  | eq_ hL lhs rhs => exact [.pos (.eq_ hL lhs rhs)]
  | neg B _ =>
      cases B with
      | predN P args => exact [.neg (.predN P args)]
      | eq_ hL lhs rhs => exact [.neg (.eq_ hL lhs rhs)]
      | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
          simp [LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals,
            LCS.FOResolution.ClauseForm.Formula.isClauseLiteral] at hDisj
  | disj B C ihB ihC => exact ihB hDisj.1 ++ ihC hDisj.2
  | conj _ _ _ _
  | impl _ _ _ _
  | all _ _ _
  | ex _ _ _ =>
      simp [LCS.FOResolution.ClauseForm.Formula.isDisjunctionOfLiterals,
        LCS.FOResolution.ClauseForm.Formula.isClauseLiteral] at hDisj
-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Flatten a proof-certified CNF matrix into its clauses. -/
noncomputable def ofCNFMatrix {L : Language} (hNoEq : L.withoutEquality) :
    (A : FormulaN L) →
      LCS.FOResolution.ClauseForm.Formula.isCNFMatrix A →
      FOClauseForm L hNoEq
  | .conj A B, hCNF =>
      (ofCNFMatrix (hNoEq := by all_goals exact hNoEq)) A hCNF.1 ++ (ofCNFMatrix (hNoEq := by all_goals exact hNoEq)) B hCNF.2
  | .predN P args, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.predN P args) hCNF]
  | .eq_ hL lhs rhs, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.eq_ hL lhs rhs) hCNF]
  | .neg A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.neg A) hCNF]
  | .disj A B, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.disj A B) hCNF]
  | .impl A B, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.impl A B) hCNF]
  | .all i A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.all i A) hCNF]
  | .ex i A, hCNF => [(clauseOfDisj (hNoEq := by all_goals exact hNoEq)) (.ex i A) hCNF]

/-- Theorem 8.5.2 (companion): clauses extracted from the actual Skolem
    form of A in its canonical fresh-signature extension. The specification
    has source A itself. Only the universal prefix of its Skolem form is
    stripped, and the remaining CNF matrix is flattened by the certified
    structural extractor. -/
@[blueprint "chap8__theorem_8_5_2"]
def ofFormula {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (clauses : FOClauseForm spec.language hNoEq) : Prop :=
  spec.source = A ∧
    ∃ hCNF : LCS.FOResolution.ClauseForm.Formula.isCNFMatrix
        (LCS.FOResolution.ClauseForm.Formula.stripAllPrenex
          (LCS.Herbrand.SHGTheorem.skolemForm spec)).2,
      clauses = ofCNFMatrix (L := spec.language) hNoEq
        (LCS.FOResolution.ClauseForm.Formula.stripAllPrenex
          (LCS.Herbrand.SHGTheorem.skolemForm spec)).2 hCNF

end FOClauseForm
end LCS.FOResolution.Method.Completeness
end

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
/-- Theorem 8.5.2: a supplied LK proof of A ⇒ ∅, for a rectified
    prenex sentence A with CNF matrix, yields a resolution refutation of
    its actual Skolem clauses in the fresh Skolem signature. This states
    existence; the uniform executable proof-to-refutation converter is
    deferred under OD-A17. -/
@[attach_debt, blueprint "chap8__theorem_8_5_2" (main := true)]
theorem herbrand_resolution {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (hPrenex : Formula.isPrenex A)
    (hCNF : Formula.matrixIsCNF A)
    (hSent : formulaFVN A = ∅)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A)
    (proof : FOLKProofTree (Sequent.mk [A] [])) :
    ∃ (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
      (clauses : FOClauseForm spec.language hNoEq)
      (D : FOResolutionDAG spec.language hNoEq),
      FOClauseForm.ofFormula hNoEq A spec clauses ∧
      @FOResolutionDAG.isResolutionRefutation spec.language hNoEq
        (fun _ _ => Classical.propDecidable _) D (fun c => c ∈ clauses)

end LCS.FOResolution.Method.Completeness
end
