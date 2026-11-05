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

helper /-- G_= extends G: every G proof tree embeds into G_= via the .base
    constructor. Therefore `sequentProvableExt s` (G-provability under
    the §5.4.8 standing assumption) implies `sequentProvableEq s`. By
    contrapositive, isConsistentSetEq (not G_=-provable) implies
    isConsistentSet (not G-provable). Both sides now use Set (FormulaN L). -/
theorem consistentEq_implies_consistent {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L)) (hCon : isConsistentSetEq hL Gamma) :
    LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSet Gamma := by
-- BEGIN PROOF
  obtain ⟨B, hB⟩ := hCon
  refine ⟨B, ?_⟩
  intro cs hcs hprov
  apply hB cs hcs
  obtain ⟨t⟩ := hprov
  exact ⟨GEqProofTree.base t⟩

helper /-- Model existence for G_= specializes to consistent sets of equality-free
formulae satisfying the global rectification condition. -/
theorem consistentEq_implies_satisfiable_noEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSetEq hL Gamma)
    (hNoEq : ∀ A ∈ Gamma,
      formulaNoEq A)
    (hGRN : LCS.FirstOrder.Completeness.MetaTheorems.globallyRectifiedN Gamma) :
    satisfiableSetN Gamma := by
-- BEGIN PROOF
  exact consistentEq_implies_satisfiable hL Gamma hCon

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


proof_of ls_model_may_be_finite := by
  let A : FormulaN L := .all 0 (.all 1 (.eq_ hL (.var 0) (.var 1)))
  refine ⟨Set.singleton A, ?_, ?_⟩
  · let M : Structure L := {
      carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => True }
    refine ⟨M, fun _ => (), ?_⟩
    intro B hB
    have hBA : B = A := hB
    subst B
    change ∀ a b : Unit, a = b
    intro a b
    cases a
    cases b
    rfl
  · intro M ⟨s, hs⟩
    have hall : ∀ a b : M.carrier, a = b := hs A rfl
    obtain ⟨a⟩ := M.carrierNonempty
    exact ⟨1, fun _ => a, fun b => ⟨⟨0, by decide⟩, hall a b⟩⟩


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


helper /-- Example 5.6.3: Every expansion of 𝒩 interpreting c above the indices
of all inequations in a finite subset of Γ validates that entire subset,
including its lifted Peano axioms. For the empty list every k satisfies the
bound and the conclusion. -/
theorem finiteInequations_valid_above
    (cs : List (FormulaN expandedArithLanguage))
    (hcs : ∀ A ∈ cs, A ∈ gammaNonstandard)
    (k : Nat)
    (hk : ∀ n : Nat,
      FormulaN.neg (FormulaN.eq_ rfl (numeralExpanded n) newConstantC) ∈ cs → n < k) :
    ∀ A ∈ cs, validInN (expandedPeanoNatStructure k) A := by
  have hTerm (s : Assignment peanoNatStructure) (t : Term peanoLanguage) :
      termEval (expandedPeanoNatStructure k) s (liftArithTerm t) =
        termEval peanoNatStructure s t := by
    induction t with
    | var x => rfl
    | const c => rfl
    | func f ts ih =>
      simp only [liftArithTerm, termEval]
      congr 1
      funext i
      exact ih i
  have hFormula (s : Assignment peanoNatStructure) (A : FormulaN peanoLanguage) :
      formulaEvalN (expandedPeanoNatStructure k) (liftArithFormula A) s ↔
        formulaEvalN peanoNatStructure A s := by
    induction A generalizing s with
    | predN P ts => exact Empty.elim P
    | eq_ h t u =>
      simp only [liftArithFormula, formulaEvalN, hTerm]
      rfl
    | neg A ih => exact not_congr (ih s)
    | conj A B ihA ihB => exact and_congr (ihA s) (ihB s)
    | disj A B ihA ihB => exact or_congr (ihA s) (ihB s)
    | impl A B ihA ihB => exact imp_congr (ihA s) (ihB s)
    | all x A ih => exact forall_congr' (fun a => ih (assignUpdate s x a))
    | ex x A ih => exact exists_congr (fun a => ih (assignUpdate s x a))
  have hNumeral (s : Assignment (expandedPeanoNatStructure k)) (n : Nat) :
      termEval (expandedPeanoNatStructure k) s (numeralExpanded n) = n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.succ (termEval (expandedPeanoNatStructure k) s (numeralExpanded n)) = n + 1
      rw [ih]
  intro A hA s
  rcases hcs A hA with ⟨B, hB, rfl⟩ | ⟨n, rfl⟩
  · exact (hFormula s B).mpr (peanoNatStructure_models_peanoArithAxioms B hB s)
  · change termEval (expandedPeanoNatStructure k) s (numeralExpanded n) ≠ k
    rw [hNumeral]
    exact Nat.ne_of_lt (hk n hA)

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

helper /-- Lifting an arithmetic formula preserves its truth in M and M₀. -/
theorem formulaEvalN_liftArithFormula (s : Assignment nonstandardModel)
    (A : FormulaN peanoLanguage) :
    formulaEvalN nonstandardModel0 (liftArithFormula A) s ↔
      formulaEvalN nonstandardModel A s := by
  induction A generalizing s with
  | predN P ts => exact Empty.elim P
  | eq_ h t u =>
    simp only [liftArithFormula, formulaEvalN, termEval_liftArithTerm]
    rfl
  | neg A ih => exact not_congr (ih s)
  | conj A B ihA ihB => exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB => exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB => exact imp_congr (ihA s) (ihB s)
  | all x A ih => exact forall_congr' (fun a => ih (assignUpdate s x a))
  | ex x A ih => exact exists_congr (fun a => ih (assignUpdate s x a))

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

helper /-- Example 5.6.3: The reduct M models the Peano arithmetic axioms. -/
theorem nonstandardModel_models_peanoArithAxioms :
    ∀ A ∈ peanoArithAxioms, validInN nonstandardModel A := by
  intro A hA s
  exact (formulaEvalN_liftArithFormula s A).mp
    (nonstandardModel0_spec.2 (liftArithFormula A) (Or.inl ⟨A, hA, rfl⟩) s)

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

helper /-- Example 5.6.3: Distinct natural numbers have distinct numeral values in M. -/
theorem nonstandardModel_numerals_distinct (m n : Nat) (hmn : m ≠ n)
    (s : Assignment nonstandardModel) :
    termEval nonstandardModel s (numeral m) ≠
      termEval nonstandardModel s (numeral n) := by
  have hZero : ∀ a : nonstandardModel.carrier,
      nonstandardModel.interpFunc ArithFunc.succ (vec1 a) ≠
        nonstandardModel.interpConst ArithConst.zero := by
    intro a
    have h := nonstandardModel_models_peanoArithAxioms paSuccZeroAxiom
      (Or.inl rfl) s a
    change termEval nonstandardModel (assignUpdate s 0 a) (mkSucc (.var 0)) ≠
      nonstandardModel.interpConst ArithConst.zero at h
    rw [termEval_mkSucc] at h
    simpa [termEval, assignUpdate] using h
  have hInj : ∀ a b : nonstandardModel.carrier,
      nonstandardModel.interpFunc ArithFunc.succ (vec1 a) =
        nonstandardModel.interpFunc ArithFunc.succ (vec1 b) → a = b := by
    intro a b
    have h := nonstandardModel_models_peanoArithAxioms paSuccInjectiveAxiom
      (Or.inr (Or.inl rfl)) s a b
    change termEval nonstandardModel (assignUpdate (assignUpdate s 0 a) 1 b)
        (mkSucc (.var 0)) =
      termEval nonstandardModel (assignUpdate (assignUpdate s 0 a) 1 b)
        (mkSucc (.var 1)) → _ at h
    simp only [formulaEvalN, termEval_mkSucc, termEval, assignUpdate] at h
    simpa using h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact False.elim (hmn rfl)
    | succ n =>
      rw [numeral, numeral, termEval_mkSucc]
      exact Ne.symm (hZero (termEval nonstandardModel s (numeral n)))
  | succ m ih =>
    cases n with
    | zero =>
      rw [numeral, numeral, termEval_mkSucc]
      exact hZero (termEval nonstandardModel s (numeral m))
    | succ n =>
      rw [numeral, numeral, termEval_mkSucc, termEval_mkSucc]
      intro h
      exact ih n (fun e => hmn (congrArg Nat.succ e))
        (hInj _ _ h)

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
