import LCS.Resolution.Method.ReverseGrowth

namespace LCS.Resolution.Method.ReverseGrowth

open LCS.Resolution.GCNF

open ResolutionTree

helper def ReverseGrowth.erased (n : Nat) : ResolutionTree :=
  .resolve
    (.resolve (units n) (.axiom_ (leftResidual n)) (p n))
    (.resolve (units n) (.axiom_ (rightResidual n)) (p n)) (r n)

helper def ReverseGrowth.cut (n : Nat) : ResolutionTree :=
  .resolve (.axiom_ (GCNF.Clause.single (r n)))
    (.resolve (units n) (.axiom_ (rightResidual n)) (p n)) (r n)

helper theorem ReverseGrowth.refutation_label (n : Nat) :
    (refutation n).label = GCNF.Clause.empty := by
  apply LCS.Finset.ext
  intro L
  simp [refutation, label, units_label, GCNF.Clause.empty,
    GCNF.Clause.single, GCNF.Clause.union, GCNF.Clause.remove,
    LCS.Finset.mem_erase, LCS.Finset.mem_singleton]
  exact LCS.Finset.not_mem_empty

helper theorem ReverseGrowth.units_inputs (n : Nat) (C : GCNF.Clause) :
    C ∈ (units n).inputs ↔ C = GCNF.Clause.single (p 0) ∨
      ∃ k, k < n ∧ (C = leftInput k ∨ C = rightInput k) := by
  induction n with
  | zero => simp [units, inputs, ClauseSequent.single]
  | succ n ih =>
    simp only [units, inputs, LCS.Finset.mem_union, ClauseSequent.single,
      LCS.Finset.mem_singleton, ih]
    constructor
    · rintro ((h | h) | (h | h))
      · rcases h with h | ⟨k, hk, hC⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hC⟩
      · exact Or.inr ⟨n, by omega, Or.inl h⟩
      · rcases h with h | ⟨k, hk, hC⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, by omega, hC⟩
      · exact Or.inr ⟨n, by omega, Or.inr h⟩
    · rintro (h | ⟨k, hk, hC⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · by_cases hkn : k < n
        · exact Or.inl (Or.inl (Or.inr ⟨k, hkn, hC⟩))
        · have hke : k = n := by omega
          subst k
          exact hC.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))

helper theorem ReverseGrowth.units_inputs_ordinary (n : Nat) : (units n).inputs.isOrdinary := by
  intro C hC
  rcases (units_inputs n C).mp hC with rfl | ⟨k, _, rfl | rfl⟩
  · exact GCNF.Clause.single_ordinary _
  · exact GCNF.Clause.ofList_cons_ordinary _ _
  · exact GCNF.Clause.ofList_cons_ordinary _ _

proof_of refutation_inputs_ordinary := open LCS.Resolution.Method.ReverseGrowth.Proofs.ReverseGrowth in
  ClauseSequent.ordinary_union (units_inputs_ordinary n)
      (ClauseSequent.ordinary_single (GCNF.Clause.single_ordinary _))


helper theorem ReverseGrowth.single_inj (L K : Literal) :
    GCNF.Clause.single L = GCNF.Clause.single K ↔ L = K := by
  constructor
  · intro h
    have hm : L ∈ GCNF.Clause.single K := h ▸ ((LCS.Finset.mem_singleton L L).mpr rfl)
    exact (LCS.Finset.mem_singleton L K).mp hm
  · rintro rfl; rfl

helper @[simp] theorem ReverseGrowth.single_mem_units (n : Nat) (L : Literal) :
    GCNF.Clause.single L ∈ (units n).inputs ↔ L = p 0 := by
  rw [units_inputs]
  constructor
  · rintro (h | ⟨k, _, h | h⟩)
    · exact (single_inj L _).mp h
    · exact (leftInput_not_single k L h.symm).elim
    · exact (rightInput_not_single k L h.symm).elim
  · intro h
    exact Or.inl ((single_inj L _).mpr h)

helper theorem ReverseGrowth.units_inputs_pos_bound (n : Nat) (C : GCNF.Clause)
    (hC : C ∈ (units n).inputs) (i : Nat) (hi : Literal.pos i ∈ C) : i ≤ 2 * n := by
  rcases (units_inputs n C).mp hC with rfl | ⟨k, hk, rfl | rfl⟩
  · simp [GCNF.Clause.single, p] at hi; omega
  · simp [leftInput, GCNF.Clause.ofList, p, r] at hi; omega
  · simp [rightInput, GCNF.Clause.ofList, p, Literal.conjugate] at hi; omega

helper theorem ReverseGrowth.leftResidual_not_mem_units (n : Nat) :
    leftResidual n ∉ (units n).inputs := by
  intro h
  have hb := units_inputs_pos_bound n _ h (2 * n + 1)
    (by simp [leftResidual, GCNF.Clause.ofList, r])
  omega

helper theorem ReverseGrowth.leftResidual_ne_inputs (n : Nat) :
    leftResidual n ≠ leftInput n ∧ leftResidual n ≠ rightInput n := by
  have hnot : p (n + 1) ∉ leftResidual n := by
    simp [leftResidual, GCNF.Clause.ofList, p, r]; omega
  constructor
  · intro he
    apply hnot
    rw [he]
    simp [leftInput, GCNF.Clause.ofList]
  · intro he
    apply hnot
    rw [he]
    simp [rightInput, GCNF.Clause.ofList]

helper theorem ReverseGrowth.combine_eq_add (A : ResolutionTree) (L : Literal)
    (S : ClauseSequent) (C : GCNF.Clause)
    (hUnit : GCNF.Clause.single L ∉ S)
    (hNew : C ∈ (A.eraseLiteral L).inputs) (hNot : C ∉ S)
    (first second : Nat) :
    combineConversionLeafCounts A L S first second = first + second := by
  have hne : newInputs (A.eraseLiteral L) S ≠ LCS.Finset.empty := by
    intro he
    have hC : C ∈ newInputs (A.eraseLiteral L) S :=
      LCS.Finset.mem_filter.mpr ⟨hNew, by simp [hNot]⟩
    exact LCS.Finset.not_mem_empty (he ▸ hC)
  simp [combineConversionLeafCounts, hUnit, hne]

helper theorem ReverseGrowth.leftResidual_label (n : Nat) :
    (resolve (units n) (axiom_ (leftResidual n)) (p n)).label =
      GCNF.Clause.single (r n) := by
  apply LCS.Finset.ext
  intro L
  cases L <;>
    simp [label, units_label, leftResidual, GCNF.Clause.ofList, GCNF.Clause.single,
      GCNF.Clause.union, GCNF.Clause.remove, Literal.conjugate,
      LCS.Finset.mem_erase, LCS.Finset.mem_singleton, p, r] <;> omega

helper theorem ReverseGrowth.rightResidual_label (n : Nat) :
    (resolve (units n) (axiom_ (rightResidual n)) (p n)).label =
      GCNF.Clause.single (r n).conjugate := by
  apply LCS.Finset.ext
  intro L
  cases L <;>
    simp [label, units_label, rightResidual, GCNF.Clause.ofList, GCNF.Clause.single,
      GCNF.Clause.union, GCNF.Clause.remove, Literal.conjugate,
      LCS.Finset.mem_erase, LCS.Finset.mem_singleton, p] <;> omega

helper theorem ReverseGrowth.erase_resolve_unit (U : ResolutionTree) (P L : Literal)
    (C : GCNF.Clause) (hU : U.label = GCNF.Clause.single P)
    (hPL : P ≠ L) (hCL : P.conjugate ≠ L)
    (hRoot : L ∈ (resolve U (axiom_ C) P).label)
    (hL : L ∈ C) (hP : P.conjugate ∈ C) :
    (resolve U (axiom_ C) P).eraseLiteral L =
      resolve U (axiom_ (GCNF.Clause.remove C L)) P := by
  rw [eraseLiteral.eq_def, if_pos hRoot]
  have hUnot : L ∉ U.label := by simpa [hU, GCNF.Clause.single] using Ne.symm hPL
  change replayResolve (U.eraseLiteral L) ((axiom_ C).eraseLiteral L) P = _
  rw [LCS.Resolution.Method.Erase.Proofs.eraseLiteral_eq_self U L hUnot, eraseLiteral.eq_def]
  simp only [label, if_pos hL]
  unfold replayResolve
  have hPu : P ∈ U.label := by simp [hU, GCNF.Clause.single]
  have hPc : P.conjugate ∈ GCNF.Clause.remove C L :=
    (LCS.Finset.mem_erase _ _ _).mpr ⟨hP, hCL⟩
  simp [hPu, label, hPc, hL]

helper theorem ReverseGrowth.erase_leftResidual (n : Nat) :
    (resolve (units n) (axiom_ (leftResidual n)) (p n)).eraseLiteral (r n) =
      refutation n := by
  rw [erase_resolve_unit _ _ _ _ (units_label n)]
  · have hc : GCNF.Clause.remove (leftResidual n) (r n) =
        GCNF.Clause.single (p n).conjugate := by
      apply LCS.Finset.ext
      intro L
      cases L <;> simp [leftResidual, GCNF.Clause.ofList, GCNF.Clause.remove,
        GCNF.Clause.single, Literal.conjugate, LCS.Finset.mem_erase, r] <;> omega
    rw [hc]; rfl
  · simp [p, r] <;> omega
  · simp [r, Literal.conjugate]
  · simp [leftResidual_label, GCNF.Clause.single]
  · simp [leftResidual, GCNF.Clause.ofList]
  · simp [leftResidual, GCNF.Clause.ofList, Literal.conjugate]

helper theorem ReverseGrowth.erase_rightResidual (n : Nat) :
    (resolve (units n) (axiom_ (rightResidual n)) (p n)).eraseLiteral (r n).conjugate =
      refutation n := by
  rw [erase_resolve_unit _ _ _ _ (units_label n)]
  · have hc : GCNF.Clause.remove (rightResidual n) (r n).conjugate =
        GCNF.Clause.single (p n).conjugate := by
      apply LCS.Finset.ext
      intro L
      cases L <;> simp [rightResidual, GCNF.Clause.ofList, GCNF.Clause.remove,
        GCNF.Clause.single, Literal.conjugate, LCS.Finset.mem_erase] <;> omega
    rw [hc]; rfl
  · simp [p, Literal.conjugate]
  · simp [Literal.conjugate] <;> omega
  · simp [rightResidual_label, GCNF.Clause.single]
  · simp [rightResidual, GCNF.Clause.ofList]
  · simp [rightResidual, GCNF.Clause.ofList, Literal.conjugate]

helper theorem ReverseGrowth.erase_leftInput (n : Nat) :
    (resolve (units n) (axiom_ (leftInput n)) (p n)).eraseLiteral (p (n + 1)) =
      resolve (units n) (axiom_ (leftResidual n)) (p n) := by
  rw [erase_resolve_unit _ _ _ _ (units_label n)]
  · have hc : GCNF.Clause.remove (leftInput n) (p (n + 1)) = leftResidual n := by
      apply LCS.Finset.ext
      intro L
      cases L <;> simp [leftInput, leftResidual, GCNF.Clause.ofList, GCNF.Clause.remove,
        LCS.Finset.mem_erase, p, r] <;> omega
    rw [hc]
  · simp [p] <;> omega
  · simp [p, Literal.conjugate]
  · rw [left_label n _ (units_label n)]; simp [GCNF.Clause.ofList]
  · simp [leftInput, GCNF.Clause.ofList]
  · simp [leftInput, GCNF.Clause.ofList, p, Literal.conjugate]

helper theorem ReverseGrowth.erase_rightInput (n : Nat) :
    (resolve (units n) (axiom_ (rightInput n)) (p n)).eraseLiteral (p (n + 1)) =
      resolve (units n) (axiom_ (rightResidual n)) (p n) := by
  rw [erase_resolve_unit _ _ _ _ (units_label n)]
  · have hc : GCNF.Clause.remove (rightInput n) (p (n + 1)) = rightResidual n := by
      apply LCS.Finset.ext
      intro L
      cases L <;> simp [rightInput, rightResidual, GCNF.Clause.ofList, GCNF.Clause.remove,
        Literal.conjugate, LCS.Finset.mem_erase, p] <;> omega
    rw [hc]
  · simp [p] <;> omega
  · simp [p, Literal.conjugate]
  · rw [right_label n _ (units_label n)]; simp [GCNF.Clause.ofList]
  · simp [rightInput, GCNF.Clause.ofList]
  · simp [rightInput, GCNF.Clause.ofList, p, Literal.conjugate]

helper theorem ReverseGrowth.erase_units_succ (n : Nat) :
    (units (n + 1)).eraseLiteral (p (n + 1)) = erased n := by
  rw [eraseLiteral.eq_def]
  have hm : p (n + 1) ∈ (units (n + 1)).label := by simp [units_label, GCNF.Clause.single]
  rw [if_pos hm]
  change replayResolve _ _ _ = erased n
  rw [erase_leftInput, erase_rightInput]
  unfold replayResolve
  simp [leftResidual_label, rightResidual_label, GCNF.Clause.single, erased]

helper theorem ReverseGrowth.cut_count (n : Nat) :
    conversionLeafCount (cut n) = conversionLeafCount (refutation n) + 1 := by
  rw [cut, conversionLeafCount]
  rw [combine_eq_add _ _ _ (GCNF.Clause.single (p n).conjugate)]
  · rw [erase_rightResidual]
    simp [conversionLeafCount]
  · simp [inputs, ClauseSequent.single, single_inj, p, r, Literal.conjugate]
  · rw [erase_rightResidual]
    simp [refutation, inputs, ClauseSequent.single]
  · simp [inputs, ClauseSequent.single, single_inj, p, r, Literal.conjugate]

helper theorem ReverseGrowth.erased_count (n : Nat) :
    conversionLeafCount (erased n) = 2 * conversionLeafCount (refutation n) + 1 := by
  rw [erased, conversionLeafCount]
  rw [combine_eq_add _ _ _ (GCNF.Clause.single (p n).conjugate)]
  · rw [erase_leftResidual]
    change conversionLeafCount (refutation n) + conversionLeafCount (cut n) = _
    rw [cut_count]
    omega
  · simp [inputs, ClauseSequent.single, p, r]
  · rw [erase_leftResidual]
    simp [refutation, inputs, ClauseSequent.single]
  · simp [inputs, ClauseSequent.single, p, Literal.conjugate]

helper theorem ReverseGrowth.refutation_count_succ (n : Nat) :
    conversionLeafCount (refutation (n + 1)) =
      2 * conversionLeafCount (refutation n) + 2 := by
  rw [refutation, units, conversionLeafCount]
  change combineConversionLeafCounts (units (n + 1)) (p (n + 1))
    (refutation (n + 1)).inputs
    (conversionLeafCount ((units (n + 1)).eraseLiteral (p (n + 1))))
    (conversionLeafCount (resolve (axiom_ (GCNF.Clause.single (p (n + 1))))
      (axiom_ (GCNF.Clause.single (p (n + 1)).conjugate)) (p (n + 1)))) = _
  rw [combine_eq_add _ _ _ (leftResidual n)]
  · rw [erase_units_succ, erased_count]
    simp [conversionLeafCount]
  · simp [refutation, inputs, ClauseSequent.single, single_inj, p, Literal.conjugate]
  · rw [erase_units_succ]
    simp [erased, inputs, ClauseSequent.single]
  · have hleft := leftResidual_ne_inputs n
    simp [refutation, units, inputs, ClauseSequent.single,
      leftResidual_not_mem_units, hleft.1, hleft.2, leftResidual_not_single]

helper theorem ReverseGrowth.refutation_count_closed (n : Nat) :
    conversionLeafCount (refutation n) + 2 = 3 * 2 ^ n := by
  induction n with
  | zero => simp [refutation, units, conversionLeafCount]
  | succ n ih =>
    rw [refutation_count_succ, Nat.pow_succ]
    omega

helper /-- The returned proof object has exponentially many axioms in the family
index: the count refers to the actual converter, not the input unfolding. -/
theorem ReverseGrowth.actual_output_leafCount (n : Nat) :
    (ResolutionTree.toGCNF (refutation n) (refutation_wellFormed n)
      (refutation_label n) (refutation_inputs_ordinary n)).val.leafCount + 2 = 3 * 2 ^ n := by
  rw [toGCNF_leafCount_eq_conversionLeafCount]
  exact refutation_count_closed n

end LCS.Resolution.Method.ReverseGrowth

namespace LCS.Resolution.Method.ReverseGrowthGraph

open LCS.Resolution.GCNF

open FiniteGraph

helper theorem ReverseGrowthGraph.graph_nodeCount_of_wellFormed
    (hwell : ∀ n, (graph n).WellFormed) (n : Nat) :
    (graph n).nodeCount = 5*n+1 := by
  rw [nodeCount_eq_length (hwell n)
    (fun i hi => graph_all_reachable hwell n i (by simpa using hi))]
  exact table_length n

helper theorem ReverseGrowthGraph.graph_nodeCount (n : Nat) : (graph n).nodeCount = 5*n+1 :=
  graph_nodeCount_of_wellFormed graph_wellFormed n

end LCS.Resolution.Method.ReverseGrowthGraph

namespace LCS.Resolution.Method.ReverseGrowth

open LCS.Resolution.GCNF

helper /-- The shared graph has precisely the recursive refutation as its unfolding. -/
theorem ReverseGrowth.graph_unfold (n : Nat) :
    (ReverseGrowthGraph.refutation n).unfold (ReverseGrowthGraph.refutation_wellFormed n) =
      refutation n :=
  ReverseGrowthGraph.refutation_unfold_eq units rfl (fun _ => rfl) n

proof_of graph_refutes := open LCS.Resolution.Method.ReverseGrowth.Proofs.ReverseGrowth in
  by
    refine ⟨ReverseGrowthGraph.refutation_wellFormed n, ?_, ReverseGrowthGraph.refutation_rootLabel n⟩
    apply (FiniteGraph.unfold_inputs_subset _ _ _).mp
    rw [graph_unfold]
    exact fun _ h => h


proof_of linear_graph_exponential_output := open LCS.Resolution.Method.ReverseGrowth.Proofs.ReverseGrowth in
  by
    refine ⟨ReverseGrowthGraph.refutation_nodeCount n, ?_⟩
    unfold FiniteGraph.toGCNF
    rw [weakenTo_leafCount, ResolutionTree.toGCNF_leafCount_eq_conversionLeafCount]
    rw [show (ReverseGrowthGraph.refutation n).unfold (graph_refutes n).1 = refutation n
      from graph_unfold n]
    exact refutation_count_closed n


proof_of actual_graph_output_nodeCount := open LCS.Resolution.Method.ReverseGrowth.Proofs.ReverseGrowth in
  by
    have hLeaves := (linear_graph_exponential_output n).2
    have hNodes := LCS.Resolution.GCNF.Proofs.GCNFProofTree.nodeCount_eq_two_leafCount_sub_one
      ((ReverseGrowthGraph.refutation n).toGCNF (refutation n).inputs
        (graph_refutes n) (refutation_inputs_ordinary n))
    omega


end LCS.Resolution.Method.ReverseGrowth
