import LCS.Resolution.Method.Completeness.Conversion

section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper @[simp] theorem Completeness.replay_length (g : FiniteGraph)
    (f : Clause → Clause) : (replay g f).table.length = g.table.length := by
  simp [replay]

helper @[simp] theorem Completeness.replay_node (g : FiniteGraph)
    (f : Clause → Clause) (i : Fin g.table.length) :
    (replay g f).node i =
      some { g.table[i] with clause := replayLabel g f i } := by
  simp [FiniteGraph.node, replay]

helper /-- The replay remains a resolution graph: adding literals never removes the
existing pivot witnesses. -/
theorem Completeness.replay_allRowsWellFormed (g : FiniteGraph) (hg : g.AllRowsWellFormed)
    (f : Clause → Clause) (B : Literal)
    (hf : ∀ C, LCS.Finset.Subset C (f C) ∧ ∀ x ∈ f C, x ∈ C ∨ x = B) :
    (replay g f).AllRowsWellFormed := by
  constructor
  · simpa [replay] using hg.1
  · intro i n hi r hr
    have hi' : i < g.table.length := by
      have h := List.getElem?_eq_some_iff.mp hi
      simpa [replay] using h.1
    let ii : Fin g.table.length := ⟨i, hi'⟩
    have hn := replay_node g f ii
    have heq : n = {g.table[ii] with clause := replayLabel g f ii} :=
      Option.some.inj (hi.symm.trans hn)
    subst n
    have hrow := hg.2 i g.table[ii] (table_node g ii) r hr
    obtain ⟨a, b, ha, hb, hL, hLc, hres⟩ := hrow.2.2
    let il : Fin g.table.length := ⟨r.left, Nat.lt_trans hrow.1 hi'⟩
    let ir : Fin g.table.length := ⟨r.right, Nat.lt_trans hrow.2.1 hi'⟩
    have hae : a = g.table[il] := Option.some.inj (ha.symm.trans (table_node g il))
    have hbe : b = g.table[ir] := Option.some.inj (hb.symm.trans (table_node g ir))
    subst a; subst b
    refine ⟨hrow.1, hrow.2.1,
      {g.table[il] with clause := replayLabel g f il},
      {g.table[ir] with clause := replayLabel g f ir},
      replay_node g f il, replay_node g f ir,
      (replayLabel_bounds g hg f B hf il).1 _ hL,
      (replayLabel_bounds g hg f B hf ir).1 _ hLc, ?_⟩
    change g.table[ii].inference = some r at hr
    change replayLabel g f ii = _
    rw [replayLabel]
    split
    · rename_i hn
      have : (none : Option FiniteGraph.Inference) = some r := hn.symm.trans hr
      cases this
    · rename_i r' hr'
      have he : r' = r := Option.some.inj (hr'.symm.trans hr)
      subst r'
      exact dite_eq_left ⟨hrow.1, hrow.2.1⟩

helper @[simp] theorem Completeness.replay_next (g : FiniteGraph)
    (f : Clause → Clause) (i p : Nat) :
    (replay g f).next i p = g.next i p := by
  by_cases hi : i < g.table.length
  · have ho := table_node g ⟨i, hi⟩
    have hn := replay_node g f ⟨i, hi⟩
    simp only [FiniteGraph.next, ho, hn]
    rfl
  · have ho : g.node i = none := List.getElem?_eq_none (Nat.le_of_not_gt hi)
    have hn : (replay g f).node i = none := by
      apply List.getElem?_eq_none
      simpa using (Nat.le_of_not_gt hi)
    simp [FiniteGraph.next, ho, hn]

helper theorem Completeness.replay_reachableFrom (g : FiniteGraph)
    (f : Clause → Clause) (depth i : Nat) :
    (replay g f).reachableFrom depth i = g.reachableFrom depth i := by
  induction depth generalizing i with
  | zero => rfl
  | succ depth ih => simp only [FiniteGraph.reachableFrom, replay_next, ih]

helper @[simp] theorem Completeness.replay_vertexIds (g : FiniteGraph)
    (f : Clause → Clause) : (replay g f).vertexIds = g.vertexIds := by
  simp only [FiniteGraph.vertexIds, replay_length, replay_reachableFrom]
  rfl

helper @[simp] theorem Completeness.replay_isInternal (g : FiniteGraph)
    (f : Clause → Clause) (i : Nat) :
    (replay g f).isInternal i = g.isInternal i := by
  by_cases hi : i < g.table.length
  · have ho := table_node g ⟨i, hi⟩
    have hn := replay_node g f ⟨i, hi⟩
    simp only [FiniteGraph.isInternal, ho, hn]
    rfl
  · have ho : g.node i = none := List.getElem?_eq_none (Nat.le_of_not_gt hi)
    have hn : (replay g f).node i = none := by
      apply List.getElem?_eq_none
      simpa using (Nat.le_of_not_gt hi)
    simp [FiniteGraph.isInternal, ho, hn]

helper @[simp] theorem Completeness.replay_leafIds (g : FiniteGraph)
    (f : Clause → Clause) : (replay g f).leafIds = g.leafIds := by
  simp [FiniteGraph.leafIds]

helper @[simp] theorem Completeness.replay_stepCount (g : FiniteGraph)
    (f : Clause → Clause) : (replay g f).stepCount = g.stepCount := by
  simp only [FiniteGraph.stepCount, FiniteGraph.stepIds, replay_vertexIds]
  congr 1
  exact List.filter_congr (fun i _ => replay_isInternal g f i)

helper theorem Completeness.complementary_resolvent (L : Literal) :
    GCNF.Clause.union (GCNF.Clause.remove (Clause.single L) L)
      (GCNF.Clause.remove (Clause.single L.conjugate) L.conjugate) = Clause.empty := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.union, GCNF.Clause.remove, Clause.single, Clause.empty,
    LCS.Finset.mem_erase, GCNF.Clause.empty, LCS.Finset.mem_union,
    LCS.Finset.mem_singleton, and_not_self, or_self, false_iff]
  exact LCS.Finset.not_mem_empty

helper theorem Completeness.complementaryGraph_allRowsWellFormed (L : Literal) :
    (complementaryGraph L).AllRowsWellFormed := by
  constructor
  · exact Nat.lt_succ_self 2
  · intro i n hi r hr
    cases i with
    | zero => simp [FiniteGraph.node, complementaryGraph] at hi; subst n; cases hr
    | succ i => cases i with
      | zero => simp [FiniteGraph.node, complementaryGraph] at hi; subst n; cases hr
      | succ i => cases i with
        | zero =>
          simp [FiniteGraph.node, complementaryGraph] at hi
          subst n
          cases hr
          refine ⟨Nat.zero_lt_succ _, Nat.lt_succ_self _, ⟨_, none⟩, ⟨_, none⟩, rfl, rfl, ?_, ?_, ?_⟩
          · simp [Clause.single]
          · simp [Clause.single, Literal.conjugate]
          · exact (complementary_resolvent L).symm
        | succ i => simp [FiniteGraph.node, complementaryGraph] at hi

helper @[simp] theorem Completeness.complementaryGraph_rootLabel (L : Literal) :
    (complementaryGraph L).rootLabel = some Clause.empty := rfl

helper theorem Completeness.complementaryGraph_leavesFrom (L : Literal) (S : ClauseSequent)
    (hp : Clause.single L ∈ S) (hn : Clause.single L.conjugate ∈ S) :
    (complementaryGraph L).LeavesFrom S := by
  intro i hi
  change i ∈ [0, 1] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨_, rfl, hp⟩
  · exact ⟨_, rfl, hn⟩

helper theorem Completeness.leavesIn_iff (g : FiniteGraph) (S : ClauseSequent) :
    leavesIn g S = true ↔ g.LeavesFrom S := by
  simp only [leavesIn, List.all_eq_true, FiniteGraph.LeavesFrom]
  constructor
  · intro h i hi
    have hh := h i hi
    cases hc : g.label i with
    | none => simp [hc] at hh
    | some C => exact ⟨C, rfl, of_decide_eq_true (by simpa [hc] using hh)⟩
  · intro h i hi
    obtain ⟨C, hc, hC⟩ := h i hi
    simp [hc, hC]

helper theorem Completeness.missingLift_bounds (S : ClauseSequent) (B : Literal) (C : Clause) :
    LCS.Finset.Subset C (missingLift S B C) ∧
      ∀ x ∈ missingLift S B C, x ∈ C ∨ x = B := by
  unfold missingLift
  split
  · exact ⟨fun _ h => h, fun _ h => Or.inl h⟩
  · constructor
    · intro x hx
      exact LCS.Finset.mem_insert.mpr (Or.inr hx)
    · intro x hx
      exact (LCS.Finset.mem_insert.mp hx).elim Or.inr Or.inl

helper theorem Completeness.replay_leaf_label (g : FiniteGraph)
    (f : Clause → Clause) (i : Nat) (hi : i ∈ g.leafIds)
    (C : Clause) (hC : g.label i = some C) :
    (replay g f).label i = some (f C) := by
  cases hn : g.node i with
  | none => simp [FiniteGraph.label, hn] at hC
  | some n =>
    have hCe : n.clause = C := by simpa [FiniteGraph.label, hn] using hC
    have hi' := (List.getElem?_eq_some_iff.mp hn).1
    let ii : Fin g.table.length := ⟨i, hi'⟩
    have hne : n = g.table[ii] := Option.some.inj (hn.symm.trans (table_node g ii))
    subst n
    have hnone : g.table[ii].inference = none := by
      have h := (List.mem_filter.mp hi).2
      simp only [FiniteGraph.isInternal, hn, Option.bind_some] at h
      cases he : g.table[ii].inference <;> simp_all
    change ((replay g f).node i).map FiniteGraph.Node.clause = some (f C)
    rw [replay_node g f ii]
    simp only [Option.map_some]
    congr 1
    rw [replayLabel]
    split
    · exact congrArg f hCe
    · rename_i r hr
      have : (none : Option FiniteGraph.Inference) = some r := hnone.symm.trans hr
      cases this

helper theorem Completeness.replay_leavesFrom (g : FiniteGraph)
    (f : Clause → Clause) (S : ClauseSequent)
    (h : ∀ i ∈ g.leafIds, ∃ C, g.label i = some C ∧ f C ∈ S) :
    (replay g f).LeavesFrom S := by
  intro i hi
  rw [replay_leafIds] at hi
  obtain ⟨C, hC, hfC⟩ := h i hi
  exact ⟨f C, replay_leaf_label g f i hi C hC, hfC⟩

helper theorem Completeness.missingLift_leavesFrom (g : FiniteGraph)
    (Gamma Cs As S : ClauseSequent) (B : Literal)
    (hLeaves : g.LeavesFrom (LCS.Finset.union Gamma Cs))
    (hG : LCS.Finset.Subset Gamma S) (hCs : LCS.Finset.Subset Cs As)
    (hAs : ∀ C ∈ As, clauseWithLiteral C B ∈ S) :
    (replay g (missingLift S B)).LeavesFrom S := by
  apply replay_leavesFrom
  intro i hi
  obtain ⟨C, hC, hmem⟩ := hLeaves i hi
  refine ⟨C, hC, ?_⟩
  unfold missingLift
  split
  · assumption
  · rename_i hNot
    rcases LCS.Finset.mem_union.mp hmem with hIn | hIn
    · exact (hNot (hG C hIn)).elim
    · exact hAs C (hCs C hIn)

helper theorem Completeness.replay_empty_root (g : FiniteGraph) (hg : g.AllRowsWellFormed)
    (f : Clause → Clause) (B : Literal)
    (hf : ∀ C, LCS.Finset.Subset C (f C) ∧ ∀ x ∈ f C, x ∈ C ∨ x = B)
    (hr : g.rootLabel = some GCNF.Clause.empty) :
    (replay g f).rootLabel = some GCNF.Clause.empty ∨
    (replay g f).rootLabel = some (Clause.single B) := by
  let i : Fin g.table.length := ⟨g.root, hg.1⟩
  have he : g.table[i].clause = GCNF.Clause.empty := by
    change (g.node i).map FiniteGraph.Node.clause = some GCNF.Clause.empty at hr
    rw [table_node g i] at hr
    exact Option.some.inj hr
  have hb := (replayLabel_bounds g hg f B hf i).2
  have hb' : ∀ x ∈ replayLabel g f i, x = B := by
    intro x hx
    rcases hb x hx with h | h
    · rw [he] at h
      exact (LCS.Finset.not_mem_empty h).elim
    · exact h
  have hlabel : (replay g f).rootLabel = some (replayLabel g f i) := by
    change ((replay g f).node g.root).map _ = _
    rw [replay_node g f i]
    rfl
  by_cases hm : B ∈ replayLabel g f i
  · right
    rw [hlabel]
    congr 1
    apply LCS.Finset.ext
    intro x
    constructor
    · intro hx
      exact (LCS.Finset.mem_singleton _ _).mpr (hb' x hx)
    · intro hx
      have heq := (LCS.Finset.mem_singleton x B).mp hx
      exact heq ▸ hm
  · left
    rw [hlabel]
    congr 1
    apply LCS.Finset.ext
    intro x
    constructor
    · intro hx
      exact (hm (hb' x hx ▸ hx)).elim
    · intro hx
      exact (LCS.Finset.not_mem_empty hx).elim

helper theorem Completeness.unitInputs_of_leaf (g : FiniteGraph) (B : Literal)
    (i : Nat) (hi : i ∈ g.leafIds) (C : Clause) (hC : g.label i = some C) :
    unitInputs g B i = decide (C = Clause.single B) := by
  cases hn : g.node i with
  | none => simp [FiniteGraph.label, hn] at hC
  | some n =>
    have he : n.clause = C := by simpa [FiniteGraph.label, hn] using hC
    have hnone : n.inference = none := by
      have h := (List.mem_filter.mp hi).2
      simp only [FiniteGraph.isInternal, hn, Option.bind_some] at h
      cases hni : n.inference <;> simp_all
    cases n with | mk clause inference =>
      dsimp only at he hnone
      subst clause; subst inference
      simp [unitInputs, hn]

helper theorem Completeness.unitInputs_compatible (donor recipient : FiniteGraph) (B : Literal)
    (hroot : donor.rootLabel = some (Clause.single B)) :
    LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.GraftCompatible donor recipient (unitInputs recipient B) := by
  intro i n hn hi
  cases n with | mk C inference =>
    cases inference with
    | some r => simp [unitInputs, hn] at hi
    | none =>
      have he : C = Clause.single B := by simpa [unitInputs, hn] using hi
      exact ⟨rfl, he ▸ hroot⟩

proof_of gcnfProofToResolution_spec := open LCS.Resolution.Method.Completeness.Conversion.Proofs.Completeness in
  by
    let rec spec : {S : ClauseSequent} → (T : GCNFProofTree S) →
        let g := gcnfProofToResolution T pick
        g.AllRowsWellFormed ∧ g.LeavesFrom S ∧
          g.rootLabel = some GCNF.Clause.empty ∧ g.stepCount ≤ T.leafCount
      | S, .axiom_ _ hOrdinary hTriv => by
        dsimp only [gcnfProofToResolution]
        let witness := pick S hTriv
        exact ⟨
          complementaryGraph_allRowsWellFormed _,
          complementaryGraph_leavesFrom _ S witness.property.1 witness.property.2,
          complementaryGraph_rootLabel _, Nat.le_refl 1⟩
      | _, .rule Gamma As B Cs Gamma1 Gamma2 hGamma hAs left right hCsNe hCsSub hG1 hG2 => by
        have ihLeft := spec left
        have ihRight := spec right
        let S := LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))
        let d1 := gcnfProofToResolution left pick
        obtain ⟨hw1, hl1, hr1, hc1⟩ := ihLeft
        let d2 := gcnfProofToResolution right pick
        obtain ⟨hw2, hl2, hr2, hc2⟩ := ihRight
        dsimp only [gcnfProofToResolution]
        if h1 : leavesIn d1 S = true then
          rw [ite_eq_left h1]
          exact ⟨hw1, (leavesIn_iff d1 S).mp h1, hr1,
            Nat.le_trans hc1 (Nat.le_add_right _ _)⟩
        else
          rw [ite_eq_right h1]
          if h2 : leavesIn d2 S = true then
            rw [ite_eq_left h2]
            exact ⟨hw2, (leavesIn_iff d2 S).mp h2, hr2,
              Nat.le_trans hc2 (Nat.le_add_left _ _)⟩
          else
            rw [ite_eq_right h2]
            let lifted := replay d1 (missingLift S B)
            have hwl : lifted.AllRowsWellFormed :=
              replay_allRowsWellFormed d1 hw1 (missingLift S B) B (missingLift_bounds S B)
            have hll : lifted.LeavesFrom S := by
              apply missingLift_leavesFrom d1 Gamma1 Cs As S B hl1 hG1 hCsSub
              intro C hC
              exact LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_image.mpr ⟨C, hC, rfl⟩))
            have hcl : lifted.stepCount ≤ left.leafCount := by
              simpa only [lifted, replay_stepCount] using hc1
            if he : lifted.rootLabel = some GCNF.Clause.empty then
              rw [ite_eq_left he]
              exact ⟨hwl, hll, he, Nat.le_trans hcl (Nat.le_add_right _ _)⟩
            else
              rw [ite_eq_right he]
              have hlroot : lifted.rootLabel = some (Clause.single B) :=
                (replay_empty_root d1 hw1 (missingLift S B) B (missingLift_bounds S B) hr1).resolve_left he
              let select := unitInputs d2 B
              have hcompatible := unitInputs_compatible lifted d2 B hlroot
              let grafted := FiniteGraph.graft lifted d2 select
              have hwg : grafted.AllRowsWellFormed :=
                LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.graft_allRowsWellFormed hwl hw2 select hcompatible
              have hlg : grafted.LeavesFrom S := by
                apply LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.graft_leavesFrom hwl hw2 select hll
                intro i hi hNot
                obtain ⟨C, hC, hm⟩ := hl2 i hi
                refine ⟨C, hC, ?_⟩
                rcases LCS.Finset.mem_union.mp hm with hIn | hIn
                · exact hG2 C hIn
                · have hEq : C = Clause.single B := (LCS.Finset.mem_singleton _ _).mp hIn
                  have hSel := unitInputs_of_leaf d2 B i hi C hC
                  simp only [hEq, decide_true] at hSel
                  have : false = true := hNot.symm.trans hSel
                  cases this
              have hrg : grafted.rootLabel = some GCNF.Clause.empty :=
                (LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.graft_rootLabel hwl hw2 select hcompatible).trans hr2
              let merged := grafted.coalesceInputLeaves
              refine ⟨FiniteGraph.coalesceInputLeaves_allRowsWellFormed grafted hwg,
                FiniteGraph.coalesceInputLeaves_leavesFrom grafted S hlg,
                (FiniteGraph.coalesceInputLeaves_rootLabel grafted).trans hrg, ?_⟩
              have hcg := LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.graft_stepCount_le hwl hw2 select
              have hcm := FiniteGraph.coalesceInputLeaves_stepCount_le grafted
              change merged.stepCount ≤ left.leafCount + right.leafCount
              exact Nat.le_trans hcm (Nat.le_trans hcg (Nat.add_le_add hcl hc2))
    have h := spec T
    exact ⟨⟨h.1.wellFormed, h.2.1, h.2.2.1⟩, h.2.2.2⟩

proof_of gcnfToResolution_nodeBound := open LCS.Resolution.Method.Completeness.Conversion.Proofs.Completeness in
  by
    have hs := gcnfProofToResolution_spec T pick
    have hlow := LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.stepCount_add_one_le_nodeCount _ hs.1.1
    have hupp := LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.nodeCount_le_two_stepCount_add_one (gcnfProofToResolution T pick)
    have ht := LCS.Resolution.GCNF.Proofs.GCNFProofTree.nodeCount_eq_two_leafCount_sub_one T
    exact ⟨hlow, by omega⟩

proof_of resolution_completeness := open LCS.Resolution.Method.Completeness.Conversion.Proofs.Completeness in
  by
    constructor
    · intro hUnsat
      by_cases hEmpty : GCNF.Clause.empty ∈ S
      · refine ⟨ResolutionDAG.mk_axiom GCNF.Clause.empty, ?_, ?_⟩
        · exact (ResolutionDAG.leavesFrom_axiom _ _).mpr hEmpty
        · exact LCS.Resolution.Method.ResolutionDAGs.Proofs.rootLabel_axiom _
      · have hValid : ClauseSequent.isValid S := by
          intro ⟨v, hSat⟩
          exact hUnsat ⟨v, hSat⟩
        have hNe : ∀ C ∈ S, C ≠ GCNF.Clause.empty := fun C hC he => hEmpty (he ▸ hC)
        obtain ⟨T⟩ := (gcnf_completeness S hValid hNe).1
        have hRef := (gcnfProofToResolution_spec T).1
        exact ⟨(gcnfProofToResolution T).toResolutionDAG hRef.1,
          (LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.toResolutionDAG_isRefutationFor _ hRef.1 S).mpr hRef⟩
    · rintro ⟨D, hRef⟩
      exact resolution_soundness S D hRef

open LCS.Resolution.GCNF

helper theorem Completeness.transportGCNF_leafCount {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) : (h ▸ t : GCNFProofTree T).leafCount = t.leafCount := by
  cases h
  rfl

end LCS.Resolution.Method.Completeness
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper @[simp] theorem Completeness.gcnfProofToResolution_transport {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) (pick : AxiomPolicy) :
    gcnfProofToResolution (h ▸ t : GCNFProofTree T) pick = gcnfProofToResolution t pick := by
  cases h
  rfl

helper @[simp] theorem Completeness.gcnfProofToResolution_axiom (Γ : ClauseSequent)
    (hOrd : Γ.isOrdinary) (hTriv) (pick : AxiomPolicy) :
    gcnfProofToResolution (.axiom_ Γ hOrd hTriv) pick =
      complementaryGraph (pick Γ hTriv).val := rfl

helper theorem Completeness.gcnfProofToResolution_rule (Γ As : ClauseSequent) (B : Literal)
    (Cs Γ1 Γ2 : ClauseSequent) (hΓ : Γ.isOrdinary) (hAs : As.isOrdinary)
    (left : GCNFProofTree (LCS.Finset.union Γ1 Cs))
    (right : GCNFProofTree (LCS.Finset.union Γ2 (ClauseSequent.single (Clause.single B))))
    (hNe) (hCs) (h1) (h2) (pick : AxiomPolicy) :
    gcnfProofToResolution (.rule Γ As B Cs Γ1 Γ2 hΓ hAs left right hNe hCs h1 h2) pick =
      let S := LCS.Finset.union Γ (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))
      let d1 := gcnfProofToResolution left pick
      let d2 := gcnfProofToResolution right pick
      if leavesIn d1 S then d1 else if leavesIn d2 S then d2 else
        let lifted := replay d1
          (missingLift S B)
        if lifted.rootLabel = some GCNF.Clause.empty then lifted
        else (FiniteGraph.graft lifted d2 (unitInputs d2 B)).coalesceInputLeaves := by
  rfl

helper @[simp] theorem Completeness.leavesIn_complementaryGraph (L : Literal) (Γ : ClauseSequent) :
    leavesIn (complementaryGraph L) Γ =
      (decide (Clause.single L ∈ Γ) && decide (Clause.single L.conjugate ∈ Γ)) := by
  change (decide (Clause.single L ∈ Γ) && (decide (Clause.single L.conjugate ∈ Γ) && true)) = _
  simp

helper theorem Completeness.coalesceInputLeaves_compute (g : FiniteGraph) :
    g.coalesceInputLeaves =
      ⟨g.table.map (fun n => { n with inference := n.inference.map fun r =>
        { r with left := g.canonicalInput r.left, right := g.canonicalInput r.right } }),
        g.canonicalInput g.root⟩ := rfl

helper theorem Completeness.empty_clauseList : GCNF.Clause.empty = Clause.ofList [] := rfl

helper theorem Completeness.methodEmpty_clauseList : Clause.empty = Clause.ofList [] := rfl

helper theorem Completeness.clauseList_eq_iff (xs ys : List Literal) :
    Clause.ofList xs = Clause.ofList ys ↔
      (∀ x ∈ xs, x ∈ ys) ∧ (∀ y ∈ ys, y ∈ xs) := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply LCS.Finset.mem_ofList.mp
      change x ∈ Clause.ofList ys
      rw [← h]
      exact LCS.Finset.mem_ofList.mpr hx
    · intro y hy
      apply LCS.Finset.mem_ofList.mp
      change y ∈ Clause.ofList xs
      rw [h]
      exact LCS.Finset.mem_ofList.mpr hy
  · intro h
    apply LCS.Finset.ext
    intro L
    exact ⟨fun hm => LCS.Finset.mem_ofList.mpr (h.1 L (LCS.Finset.mem_ofList.mp hm)),
      fun hm => LCS.Finset.mem_ofList.mpr (h.2 L (LCS.Finset.mem_ofList.mp hm))⟩

helper theorem Completeness.clauseWithLiteral_list (xs : List Literal) (L : Literal) :
    clauseWithLiteral (Clause.ofList xs) L = Clause.ofList (L :: xs) := by
  apply LCS.Finset.ext
  intro M
  simp [clauseWithLiteral, Clause.ofList]

helper theorem Completeness.remove_clauseList (xs : List Literal) (L : Literal) :
    GCNF.Clause.remove (Clause.ofList xs) L =
      Clause.ofList (xs.filter fun M => decide (M ≠ L)) := by
  apply LCS.Finset.ext
  intro M
  simp [GCNF.Clause.remove, Clause.ofList]

helper theorem Completeness.union_clauseList (xs ys : List Literal) :
    GCNF.Clause.union (Clause.ofList xs) (Clause.ofList ys) = Clause.ofList (xs ++ ys) := by
  apply LCS.Finset.ext
  intro M
  simp [GCNF.Clause.union, Clause.ofList]

helper theorem Completeness.replay_complementaryGraph (L : Literal) (f : Clause → Clause) :
    replay (complementaryGraph L) f =
      ⟨[⟨f (Clause.single L), none⟩, ⟨f (Clause.single L.conjugate), none⟩,
        ⟨GCNF.Clause.union (GCNF.Clause.remove (f (Clause.single L)) L)
          (GCNF.Clause.remove (f (Clause.single L.conjugate)) L.conjugate),
          some ⟨L, 0, 1⟩⟩], 2⟩ := by
  have h0 : replayLabel (complementaryGraph L) f ⟨0, by change 0 < 3; decide⟩ = f (Clause.single L) := by
    rw [replayLabel]
    rfl
  have h1 : replayLabel (complementaryGraph L) f ⟨1, by change 1 < 3; decide⟩ = f (Clause.single L.conjugate) := by
    rw [replayLabel]
    rfl
  have h2 : replayLabel (complementaryGraph L) f ⟨2, by change 2 < 3; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.single L)) L)
        (GCNF.Clause.remove (f (Clause.single L.conjugate)) L.conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union
      (GCNF.Clause.remove (replayLabel (complementaryGraph L) f ⟨0, _⟩) L)
      (GCNF.Clause.remove (replayLabel (complementaryGraph L) f ⟨1, _⟩) L.conjugate) = _
    rw [h0, h1]
  simp only [replay, complementaryGraph, List.ofFn_succ, List.ofFn_zero]
  change (⟨[⟨replayLabel (complementaryGraph L) f ⟨0, _⟩, none⟩,
    ⟨replayLabel (complementaryGraph L) f ⟨1, _⟩, none⟩,
    ⟨replayLabel (complementaryGraph L) f ⟨2, _⟩, some ⟨L, 0, 1⟩⟩], 2⟩ : FiniteGraph) = _
  rw [h0, h1, h2]

end LCS.Resolution.Method.Completeness
end
end
