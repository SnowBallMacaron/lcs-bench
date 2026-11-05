import LCS.Herbrand.SharpenedHauptsatz

namespace LCS.Herbrand.SharpenedHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Equality

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

helper /-- Example 7.1.1 (companion theorem): Exactly the nonidentity left leaf
remains open; the right leaf is the certified identity axiom. -/
theorem openDeductionExample_boundaries_7_1_1 :
    openDeductionExample_7_1_1.openLeaves = [openBoundary_7_1_1] ∧
    openDeductionExample_7_1_1.axiomLeaves = [openRightBoundary_7_1_1] := by
-- BEGIN PROOF
  exact ⟨rfl, rfl⟩

helper /-- Example 7.1.1 (companion): The legal first rule of the attempted exchange,
with the original two premises retained. -/
def openSwapFirstRule_7_1_1 :
    FOLKStep2 openBoundary_7_1_1 openRightBoundary_7_1_1 openSwapBoundary_7_1_1 :=
  .orLeft openExamplePa_7_1_1 openExampleQfga_7_1_1 [] [openExampleQfga_7_1_1]

proof_of failedLocalExchange_7_1_1 := by
  -- BEGIN PROOF
    rintro ⟨t, x, A, Γ, Δ, hfree, hprem, hconc⟩
    have h := congrArg Sequent.antecedent hconc
    simp only [openConclusion_7_1_1] at h
    cases h


proof_of openExample_properSubformula_7_1_1 := by
  -- BEGIN PROOF
    refine ⟨.disjRight (.refl _), ?_⟩
    intro h
    cases h


helper /-- Example 7.3.1 (companion def): A language with three unary predicates P, Q, R, no function symbols or constants. Used to construct the eigenvariable condition violation example. Note: the textbook version has Q as zero-arity (propositional), but since FormulaN has no pred0 constructor we make Q unary with a dummy argument. -/
def exViolationLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExViolationPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 1

helper /-- Example 7.3.1 (companion def): The conclusion sequent Gamma -> forall x P(x), Q(z0) /\ R(y) that exhibits the eigenvariable condition violation when one attempts to permute and-right above forall-right. Variables: y = 1, x = 0, z0 = 3. -/
def eigenvariableViolationConclusionSeq : Sequent exViolationLang :=
  let px := FormulaN.predN ExViolationPred.P (fun _ => Term.var 0)
  let forallXPx := FormulaN.all 0 px
  let q := FormulaN.predN ExViolationPred.Q (fun _ => Term.var 3)
  let ry := FormulaN.predN ExViolationPred.R (fun _ => Term.var 1)
  let qAndRy := FormulaN.conj q ry
  { antecedent := []
    succedent := [forallXPx, qAndRy] }

proof_of eigenvariableSwapFreshnessFails := by
  -- BEGIN PROOF
    intro hfresh
    exact hfresh (.conj Q R) (by simp) (Or.inr hyR)


helper /-- Example 7.3.1 (companion theorem): The original fragment has exactly the
two printed open premises and no identity-axiom substitutes. -/
theorem eigenvariableOriginalBoundaries {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) (hfree : isFreeForN (.var y) x P)
    (hfresh : ∀ F ∈ Γ ++ [Q, .all x P], y ∉ formulaFVN F) :
    (eigenvariableViolationTree Γ P Q R x y hfree hfresh).openLeaves =
      eigenvariableExamplePremises Γ P Q R x y ∧
    (eigenvariableViolationTree Γ P Q R x y hfree hfresh).axiomLeaves = [] := by
-- BEGIN PROOF
  exact ⟨rfl, rfl⟩

helper /-- Example 7.3.1 (companion theorem): The attempted upper part retains the
same ordered open premises. Its tail has only the candidate all-right conclusion
as its open boundary; the final sequent is the common indexed conclusion. -/
theorem eigenvariableAttemptBoundaries {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) (hfree : isFreeForN (.var y) x P)
    (hyR : y ∈ formulaFVN R) :
    (eigenvariableIllegalSwap Γ P Q R x y hfree hyR).beforeQuantifier.openLeaves =
      eigenvariableExamplePremises Γ P Q R x y ∧
    (eigenvariableIllegalSwap Γ P Q R x y hfree hyR).afterQuantifier.openLeaves =
      [eigenvariableSwapAfterForall Γ P Q R x] := by
-- BEGIN PROOF
  exact ⟨rfl, rfl⟩

helper /-- Example 7.3.2 (companion theorem): The two concrete fragments have the
same ordered open premises, no axiom substitutes, and the printed rule orders.
In preorder the original and-right precedes all-right; in the permuted tree
all-right precedes and-right, so it is below it in the printed deduction. -/
theorem renamedAndPermutedSkeletons {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x z : Nat) (hfree : isFreeForN (.var z) x P)
    (hbefore : ∀ F ∈ Γ ++ [Q, .all x P], z ∉ formulaFVN F)
    (hafter : ∀ F ∈ Γ ++ ([.all x P, .conj Q R] ++ [.all x P]),
      z ∉ formulaFVN F) :
    let before := pureVariableRenamedTree Γ P Q R x z hfree hbefore
    let after := permutedLegalTree Γ P Q R x z hfree hafter
    before.openLeaves = eigenvariableExamplePremises Γ P Q R x z ∧
    after.openLeaves = before.openLeaves ∧
    before.axiomLeaves = [] ∧ after.axiomLeaves = [] ∧
    before.ruleTrace = [7,4,2,4,0,0] ∧
    after.ruleTrace = [4,5,4,4,4,2,4,4,7,4,3,0,4,4,3,0] := by
-- BEGIN PROOF
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

proof_of renamedAndPermutedPure := by
  -- BEGIN PROOF
    -- REPAIR(T7-120): proof pending
    sorry


helper /-- Example 7.3.2 (companion theorem): In the source's unary P instance,
replacing y by fresh z in the selected P(y) formula yields P(z). The second
boundary sequent (and hence R(y)) is identical before and after that local change. -/
theorem renamedLocalBoundary (Γ : List (FormulaN exViolationLang))
    (Q R : FormulaN exViolationLang) :
    let P := FormulaN.predN ExViolationPred.P (fun _ => Term.var 0)
    formulaSubstN (formulaSubstN P (.var 1) 0) (.var 2) 1 =
      formulaSubstN P (.var 2) 0 ∧
    (eigenvariableExamplePremises Γ P Q R 0 1)[1]? =
      (eigenvariableExamplePremises Γ P Q R 0 2)[1]? := by
-- BEGIN PROOF
  exact ⟨rfl, rfl⟩

helper /-- Definition 7.3.1 (companion def): The set of all variables (free
    or bound) occurring in any formula of the LK proof tree. -/
def proofTreeVariables {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Set Nat
  | s, .axiom_ _ _ =>
    Set.iUnion (fun (f : Fin s.antecedent.length) =>
      formulaAllVariables (s.antecedent.get f)) ∪
    Set.iUnion (fun (f : Fin s.succedent.length) =>
      formulaAllVariables (s.succedent.get f))
  | _, .onePremise _ t => proofTreeVariables t
  | _, .twoPremise _ t1 t2 =>
    proofTreeVariables t1 ∪ proofTreeVariables t2

proof_of pureVariableConversion_LK := by
  -- REPAIR(T7-36): proof pending
  sorry


proof_of pureVariableConversion_G := by
  -- REPAIR(T7-36): proof pending
  sorry


proof_of pureVariableConversion_LKe := by
  exact pureVariableConversion_LKe_helper T


proof_of pureVariableConversion_GEq := by
  exact pureVariableConversion_GEq_helper T


proof_of atomicAxiomReduction_LK := by
  -- BEGIN PROOF
  obtain ⟨T⟩ := hprov
  exact atomicAxiomReduction_LK_helper T

proof_of atomicAxiomReduction_LKe_helper := by
  -- BEGIN PROOF
  intro s T
  induction T with
  | axiom_ s hax =>
    obtain ⟨A, hAnt, hSucc⟩ := hax
    obtain ⟨tA, hA⟩ := atomicIdentity_LK A
    cases s with
    | mk Γ Δ =>
      simp only at hAnt hSucc
      subst Γ
      subst Δ
      exact ⟨LKeProofTree.lk tA, hasOnlyAtomicAxioms_lk tA hA⟩
  | eqAxiom hL ax =>
    exact ⟨.eqAxiom hL ax, trivial⟩
  | onePremise rule T ih =>
    obtain ⟨T', hT'⟩ := ih
    exact ⟨.onePremise rule T', hT'⟩
  | twoPremise rule T₁ T₂ ih₁ ih₂ =>
    obtain ⟨T₁', hT₁'⟩ := ih₁
    obtain ⟨T₂', hT₂'⟩ := ih₂
    exact ⟨.twoPremise rule T₁' T₂', ⟨hT₁', hT₂'⟩⟩

helper theorem atomicAxiomReduction_LKe {L : Language}
    (seq : Sequent L)
    (hprov : lkeProvable seq) :
    ∃ t : LKeProofTree seq, hasOnlyAtomicOrEqAxioms t := by
-- BEGIN PROOF
  obtain ⟨T⟩ := hprov
  obtain ⟨T', hatomic⟩ := atomicAxiomReduction_LKe_helper T
  exact ⟨T', hatomic⟩


end LCS.Herbrand.SharpenedHauptsatz
