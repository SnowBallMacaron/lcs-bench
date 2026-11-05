import LCS.Propositional.Systems.G.Search.Falsification
import LCS.Propositional.Systems.G.Search.Validity.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem boolval_eq_F_of_ne_T {b : BoolVal} (h : b ≠ BoolVal.T) :
    b = BoolVal.F := by cases b <;> simp_all

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper def formulaVarsN : PropFormulaNormalized → Set Nat
  | .var n => fun m => m = n
  | .neg A => formulaVarsN A
  | .conj A B => formulaVarsN A ∪ formulaVarsN B
  | .disj A B => formulaVarsN A ∪ formulaVarsN B
  | .impl A B => formulaVarsN A ∪ formulaVarsN B

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem evalExtN_depends_on_vars (A : PropFormulaNormalized) (v v' : Valuation)
    (h : ∀ n : Nat, formulaVarsN A n → v n = v' n) :
    evalExtN v A = evalExtN v' A := by
-- BEGIN PROOF
  induction A with
  | var n => simp only [evalExtN]; exact h n rfl
  | neg A ih => simp only [evalExtN]; rw [ih h]
  | conj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | disj A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | impl A B ihA ihB =>
    simp only [evalExtN]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem formulaVarIndices_complete (A : PropFormulaNormalized) (n : Nat)
    (h : formulaVarsN A n) : n ∈ formulaVarIndices A := by
-- BEGIN PROOF
  induction A with
  | var m =>
    simp only [formulaVarsN] at h; subst h; simp [formulaVarIndices]
  | neg B ih => exact ih h
  | conj B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))
  | disj B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))
  | impl B C ihB ihC =>
    rcases h with hB | hC
    · exact List.mem_append.mpr (Or.inl (ihB hB))
    · exact List.mem_append.mpr (Or.inr (ihC hC))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sequentVarIndices_complete (s : Sequent) (A : PropFormulaNormalized)
    (hA : A ∈ s.antecedent ++ s.succedent) (n : Nat) (hn : formulaVarsN A n) :
    n ∈ sequentVarIndices s :=
-- BEGIN PROOF
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨A, hA, formulaVarIndices_complete A n hn⟩)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem allValuations_covers (vars : List Nat) (v : Valuation) :
    ∃ w ∈ allValuations vars, ∀ i ∈ vars, w i = v i := by
-- BEGIN PROOF
  induction vars with
  | nil => exact ⟨fun _ => BoolVal.F, List.Mem.head _, fun _ h => (List.not_mem_nil h).elim⟩
  | cons n ns ih =>
    obtain ⟨w0, hw0mem, hw0eq⟩ := ih
    -- Construct the covering valuation
    rcases boolval_T_or_F (v n) with hvn | hvn
    · -- v n = T: use the T-branch
      refine ⟨fun m => if m == n then BoolVal.T else w0 m, ?_, ?_⟩
      · simp only [allValuations]
        exact List.mem_flatMap.mpr ⟨w0, hw0mem, List.Mem.head _⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hns
        · simp [hvn]
        · -- i ∈ ns; need: (if i == n then T else w0 i) = v i
          by_cases hin : i = n
          · subst hin; simp [hvn]
          · simp [beq_eq_false_iff_ne.mpr hin]; exact hw0eq i hns
    · -- v n = F: use the F-branch
      refine ⟨fun m => if m == n then BoolVal.F else w0 m, ?_, ?_⟩
      · simp only [allValuations]
        exact List.mem_flatMap.mpr ⟨w0, hw0mem, List.Mem.tail _ (List.Mem.head _)⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hns
        · simp [hvn]
        · by_cases hin : i = n
          · subst hin; simp [hvn]
          · simp [beq_eq_false_iff_ne.mpr hin]; exact hw0eq i hns

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem checkSequentValidFor_iff (s : Sequent) (v : Valuation) :
    checkSequentValidFor s v = true ↔
    ((∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) →
     (∃ B ∈ s.succedent, evalExtN v B = BoolVal.T)) := by
-- BEGIN PROOF
  constructor
  · -- Forward: checkSequentValidFor true → implication holds
    intro hcheck hAllT
    simp only [checkSequentValidFor] at hcheck
    have hallb : (s.antecedent.all (fun A => evalExtN v A == BoolVal.T)) = true := by
      rw [List.all_eq_true]
      intro A hA; exact beq_iff_eq.mpr (hAllT A hA)
    simp [hallb] at hcheck
    exact hcheck
  · -- Backward: implication holds → checkSequentValidFor true
    intro hf
    simp only [checkSequentValidFor]
    by_cases hallb : (s.antecedent.all (fun A => evalExtN v A == BoolVal.T)) = true
    · simp [hallb]
      rw [List.all_eq_true] at hallb
      have hAllT : ∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T :=
        fun A hA => beq_iff_eq.mp (hallb A hA)
      exact hf hAllT
    · simp [Bool.eq_false_iff.mpr hallb]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of checkSequentValid_correct := by
  -- BEGIN PROOF
    simp [checkSequentValid, List.all_eq_true]
    constructor
    · -- Forward: checkSequentValid s = true → sequentValid s
      intro hall v hAntT
      -- Find a valuation w in allValuations that agrees with v on sequent vars
      obtain ⟨w, hwmem, hwagree⟩ := allValuations_covers (sequentVarIndices s) v
      -- w satisfies checkSequentValidFor
      have hwcheck := (checkSequentValidFor_iff s w).mp (hall w hwmem)
      -- Show w makes all antecedents T (since it agrees with v on relevant vars)
      have hAntW : ∀ A ∈ s.antecedent, evalExtN w A = BoolVal.T := by
        intro A hA
        have heq : evalExtN w A = evalExtN v A :=
          evalExtN_depends_on_vars A w v (fun n hn =>
            (hwagree n (sequentVarIndices_complete s A
              (List.mem_append.mpr (Or.inl hA)) n hn)))
        rw [heq]; exact hAntT A hA
      -- Get a succedent formula B true under w
      obtain ⟨B, hBmem, hBw⟩ := hwcheck hAntW
      -- Transfer back to v
      have heqB : evalExtN v B = evalExtN w B :=
        evalExtN_depends_on_vars B v w (fun n hn =>
          (hwagree n (sequentVarIndices_complete s B
            (List.mem_append.mpr (Or.inr hBmem)) n hn)).symm)
      exact ⟨B, hBmem, heqB.trans hBw⟩
    · -- Backward: sequentValid s → checkSequentValid s = true
      intro hvalid w hwmem
      exact (checkSequentValidFor_iff s w).mpr (fun hAntW => hvalid w hAntW)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem falsifiedBy_of_checkFalse (s : Sequent) (v : Valuation)
    (h : checkSequentValidFor s v = false) :
    sequentFalsifiedBy s v := by
-- BEGIN PROOF
  simp only [checkSequentValidFor] at h
  -- h : (if cond = true then ... else true) = false
  -- Case split on the condition (Bool-valued, so decidable)
  cases hcond : s.antecedent.all (fun A => evalExtN v A == BoolVal.T) with
  | false =>
    -- If condition is false, the if-then-else gives `true`, contradicting h
    simp [hcond] at h
  | true =>
    -- Condition is true: all antecedent formulas evaluate to T
    simp [hcond] at h
    -- h : s.succedent.any (fun B => evalExtN v B == BoolVal.T) = false
    constructor
    · -- All antecedent formulas evaluate to T
      intro A hA
      exact beq_iff_eq.mp ((List.all_eq_true.mp hcond) A hA)
    · -- All succedent formulas evaluate to F (simp already converted h)
      intro B hB
      exact boolval_eq_F_of_ne_T (h B hB)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of search_falsifying_extraction := by
  -- BEGIN PROOF
    -- Step 1: From ¬sequentValid s, derive checkSequentValid s = false
    --         using Bool case analysis (no Classical axioms needed).
    have hcheck : checkSequentValid s = false := by
      cases hb : checkSequentValid s with
      | false => rfl
      | true => exact absurd (checkSequentValid_correct s |>.mp hb) hf
    -- Step 2: Extract a valuation from allValuations that fails the check.
    rw [checkSequentValid] at hcheck
    obtain ⟨v, hv_mem, hv_fail⟩ := List.all_eq_false.mp hcheck
    -- Step 3: Convert checkSequentValidFor failure to falsification evidence.
    have hv_false : checkSequentValidFor s v = false :=
      Bool.eq_false_iff.mpr hv_fail
    have hfals := falsifiedBy_of_checkFalse s v hv_false
    -- Step 4: Wrap into sequentFalsifiable.
    exact ⟨v, hfals.1, hfals.2⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of search_termination_and_completeness := ⟨completeness_G s, search_falsifying_extraction s⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of rule_falsification_step1_iff := by
  -- BEGIN PROOF
    exact ⟨step1_falsification_forward rule v, step1_falsification_backward rule v⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of rule_falsification_step2_iff := by
  -- BEGIN PROOF
    exact ⟨step2_falsification_forward rule v, step2_falsification_backward rule v⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTraceRound1_leaf_count := by decide

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTraceRound1_leaves := by decide

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTraceRound2_leaves := by decide

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of exSearchTrace_descendant_demo := by
  -- BEGIN PROOF
    have h : (nonAxiomLeaves exSearchTraceRound1).all (fun leaf =>
        (leaf.antecedent.any (· == .var 0))) = true := by decide
    simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
    intro leaf hleaf
    obtain ⟨a, ha, rfl⟩ := h leaf hleaf
    exact ha

end LCS.Propositional.Systems.G.Search
end
