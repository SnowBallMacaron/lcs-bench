import LCS.FirstOrder.Equality.MetaTheorems

namespace LCS.FirstOrder.Equality.MetaTheorems

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax (peanoLanguage ArithFunc ArithConst)

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SyntaxN.Variables (formulaFVN)

open LCS.FirstOrder.Semantics (zeroTerm mkSucc mkPlus mkTimes peanoNatStructure)

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Equality.Completeness

open LCS.FirstOrder.Completeness.MetaTheorems

open Classical

proof_of satisfiable_implies_consistent_eq := by
  -- BEGIN PROOF
    obtain ⟨M, s, hsat⟩ := hSat
    let B : FormulaN L := .neg (.eq_ hL (.var 0) (.var 0))
    refine ⟨B, fun cs hcs hprov => ?_⟩
    have hvalid := soundnessGEq hL (Sequent.mk cs [B]) hprov
    obtain ⟨A, hA, hEval⟩ := hvalid M s (fun C hC => hsat C (hcs C hC))
    have hAB : A = B := by simpa using hA
    subst A
    exact hEval rfl


proof_of consistent_implies_satisfiable_eq := consistentEq_implies_satisfiable hL Gamma hCon
  -- BEGIN PROOF


proof_of lowenheim_skolem_eq := by
  -- BEGIN PROOF
    -- Step 1: From satisfiability, derive G=-consistency.
    have hCon := satisfiable_implies_consistent_eq hL Gamma hSat
    -- Step 2: From G=-consistency, produce a countable model.
    obtain ⟨M, s, hsat, hcount⟩ :=
      consistentEq_implies_satisfiable_countable hL Gamma hCon
    exact ⟨M, ⟨s, hsat⟩, hcount⟩

proof_of compactness_eq := by
  -- BEGIN PROOF
    have hCon : isConsistentSetEq hL Gamma := by
      let B : FormulaN L := .neg (.eq_ hL (.var 0) (.var 0))
      refine ⟨B, fun cs hcs hprov => ?_⟩
      have hvalid := soundnessGEq hL (Sequent.mk cs [B]) hprov
      have hSat : ∃ (M : Structure L) (s : Assignment M),
          ∀ A ∈ cs, formulaEvalN M A s := by
        by_cases hne : cs = []
        · subst cs
          let M : Structure L := {
            carrier := Unit
            carrierNonempty := ⟨()⟩
            interpFunc := fun _ _ => ()
            interpConst := fun _ => ()
            interpPred := fun _ _ => True }
          exact ⟨M, fun _ => (), fun _ h => by simp at h⟩
        · exact hFSS cs hne hcs
      obtain ⟨M, s, hMs⟩ := hSat
      obtain ⟨A, hA, hEval⟩ := hvalid M s hMs
      have hAB : A = B := by simpa using hA
      subst A
      exact hEval rfl
    -- Step 2: From consistency, derive satisfiability via model existence.
    exact consistent_implies_satisfiable_eq hL Gamma hCon


proof_of maximal_consistent_extension_eq := lindenbaum_eq hL Gamma hCon
  -- BEGIN PROOF

helper /-- Example 5.6.3: Compactness gives satisfiability of Γ = A_P ∪ I. -/
theorem gammaNonstandard_satisfiable : satisfiableSetN gammaNonstandard := by
  letI := Classical.choice expandedArithFormula_countable
  apply compactness_eq rfl gammaNonstandard
  intro cs _ hcs
  obtain ⟨k, hk⟩ := gammaNonstandard_finite_nat_model cs hcs
  exact ⟨expandedPeanoNatStructure k, fun _ => (0 : Nat),
    fun A hA => hk A hA (fun _ => (0 : Nat))⟩

proof_of gammaNonstandard_countable_model := by
  letI := Classical.choice expandedArithFormula_countable
  obtain ⟨M, ⟨s, hsat⟩, hcount⟩ :=
    lowenheim_skolem_eq rfl gammaNonstandard gammaNonstandard_satisfiable
  refine ⟨M, hcount, ?_⟩
  intro A hA t
  have hClosed : formulaFVN A = Set.empty := by
    -- REPAIR(T129): proof pending
    sorry
  apply (coincidenceLemmaN M A s t ?_).mp (hsat A hA)
  intro x hx
  rw [hClosed] at hx
  exact False.elim hx


helper /-- Example 5.6.3: M₀ is countable and models every member of Γ. -/
theorem nonstandardModel0_spec :
    isAtMostCountable nonstandardModel0 ∧
      ∀ A ∈ gammaNonstandard, validInN nonstandardModel0 A :=
  Classical.choose_spec gammaNonstandard_countable_model

helper /-- Lifting an arithmetic term preserves its value in M and M₀. -/
theorem termEval_liftArithTerm (s : Assignment nonstandardModel)
    (t : Term peanoLanguage) :
    termEval nonstandardModel0 s (liftArithTerm t) = termEval nonstandardModel s t := by
  induction t with
  | var x => rfl
  | const c => rfl
  | func f ts ih =>
    simp only [liftArithTerm, termEval]
    congr 1
    funext i
    exact ih i

helper /-- Lifting a numeral gives the corresponding numeral of the expanded language. -/
theorem liftArithTerm_numeral (n : Nat) :
    liftArithTerm (numeral n) = numeralExpanded n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [numeral, numeralExpanded, mkSucc, liftArithTerm]
    congr 1
    funext i
    have hi : i = ⟨0, by decide⟩ := by
      apply Fin.ext
      have h : i.val < 1 := i.isLt
      change i.val = 0
      omega
    subst i
    exact ih

helper /-- Example 5.6.3: The element a is not the value of any numeral in M. -/
theorem nonstandardElement_not_numeral (n : Nat) (s : Assignment nonstandardModel) :
    nonstandardElement ≠ termEval nonstandardModel s (numeral n) := by
  have h := nonstandardModel0_spec.2
    (FormulaN.neg (FormulaN.eq_ rfl (numeralExpanded n) newConstantC))
    (Or.inr ⟨n, rfl⟩) s
  change termEval nonstandardModel0 s (numeralExpanded n) ≠ nonstandardElement at h
  rw [← liftArithTerm_numeral, termEval_liftArithTerm] at h
  exact Ne.symm h

helper /-- Evaluating S(t) applies the structure's successor to the value of t. -/
theorem termEval_mkSucc (M : Structure peanoLanguage) (s : Assignment M)
    (t : Term peanoLanguage) :
    termEval M s (mkSucc t) = M.interpFunc ArithFunc.succ (vec1 (termEval M s t)) := by
  simp only [mkSucc, termEval]
  congr 1
  funext i
  have hi : i = ⟨0, by decide⟩ := by
    apply Fin.ext
    have h : i.val < 1 := i.isLt
    change i.val = 0
    omega
  subst i
  rfl

helper /-- Example 5.6.3: Under a hypothetical isomorphism f from M to 𝒩,
every natural number differs from k = f(a). Numeral preservation and
injectivity transfer a ≠ n_M to n ≠ k for each n. -/
theorem nonstandard_isomorphism_forall_ne
    (f : StructureIsomorphism nonstandardModel peanoNatStructure) :
    let k := f.toFun nonstandardElement
    ∀ n : Nat, n ≠ k := by
  change ∀ n : Nat, n ≠ f.toFun nonstandardElement
  let s : Assignment nonstandardModel := fun _ => nonstandardElement
  have hn : ∀ n : Nat, f.toFun (termEval nonstandardModel s (numeral n)) = n := by
    intro n
    induction n with
    | zero => exact f.preservesConst ArithConst.zero
    | succ n ih =>
      rw [numeral, termEval_mkSucc]
      exact (f.preservesFunc ArithFunc.succ
        (vec1 (termEval nonstandardModel s (numeral n)))).trans (by
          change Nat.succ (f.toFun (termEval nonstandardModel s (numeral n))) = n + 1
          rw [ih])
  intro n hnk
  exact nonstandardElement_not_numeral n s
    (f.injective ((hn n).trans hnk).symm)

proof_of nonstandardModel_not_isomorphic := by
  intro ⟨f⟩
  exact nonstandard_isomorphism_forall_ne f (f.toFun nonstandardElement) rfl


end LCS.FirstOrder.Equality.MetaTheorems
