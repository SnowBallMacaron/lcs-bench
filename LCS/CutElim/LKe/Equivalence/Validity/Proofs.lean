import LCS.CutElim.LKe.Equivalence.Validity

section

namespace LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Equality.Completeness

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.CompletenessBridge

open LCS.FirstOrder.Equality







































helper def validBridgeLiftFOLKProof {L : Language} (F : FormulaN L) :
    {s : Sequent (ValidBridgeSupportLanguage F)} →
      FOLKProofTree s →
      FOLKProofTree (validBridgeLiftSequent F s)
  | _, .axiom_ s h =>
      .axiom_ (validBridgeLiftSequent F s)
        (validBridgeLift_isFOLKAxiom F h)
  | _, .onePremise rule t =>
      .onePremise (validBridgeLiftFOLKStep1 F rule)
        (validBridgeLiftFOLKProof F t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise (validBridgeLiftFOLKStep2 F rule)
        (validBridgeLiftFOLKProof F t₁)
        (validBridgeLiftFOLKProof F t₂)







helper /-- Compatibility of finite-support proof lifting with the recursive
`LKeProofTree.lk` smart embedding. -/
@[simp]
theorem validBridgeLiftLKeProof_lk {L : Language}
    (F : FormulaN L)
    {s : Sequent (ValidBridgeSupportLanguage F)}
    (t : FOLKProofTree s) :
    validBridgeLiftLKeProof F (LKeProofTree.lk t) =
      LKeProofTree.lk (validBridgeLiftFOLKProof F t) := by
  induction t with
  | axiom_ _ _ => rfl
  | onePremise rule _ ih =>
      simpa [LKeProofTree.lk, validBridgeLiftLKeProof,
        validBridgeLiftFOLKProof] using congrArg
          (fun u => LKeProofTree.onePremise
            (validBridgeLiftFOLKStep1 F rule) u) ih
  | twoPremise _ _ _ ih1 ih2 =>
      simp [LKeProofTree.lk, validBridgeLiftLKeProof,
        validBridgeLiftFOLKProof, ih1, ih2]















































helper /-- Iteratively removes a list of isEqAxiomInstance formulas from the
antecedent prefix of an lkeProvableWithoutEssentialCuts proof. -/
theorem lkeNoEssentialCuts_remove_axiom_prefix {L : Language}
    (hL : L.hasEquality = true)
    (axioms : List (FormulaN L)) (rest Λ : List (FormulaN L))
    (haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A)
    (ih : lkeProvableWithoutEssentialCuts (Sequent.mk (axioms ++ rest) Λ)) :
    lkeProvableWithoutEssentialCuts (Sequent.mk rest Λ) := by
-- BEGIN PROOF
  induction axioms with
  | nil => exact ih
  | cons a as ihas =>
    have ha : isEqAxiomInstance hL a := haxioms a (List.Mem.head _)
    have has' : ∀ A ∈ as, isEqAxiomInstance hL A :=
      fun A hA => haxioms A (List.mem_cons_of_mem _ hA)
    have ih' : lkeProvableWithoutEssentialCuts
        (Sequent.mk ([] ++ [a] ++ (as ++ rest)) Λ) := by
      simp at ih ⊢; exact ih
    have := lkeNoEssentialCuts_remove_eqAxiomInstance hL a ha [] (as ++ rest) Λ ih'
    simp at this
    exact ihas has' this

helper /-- Theorem 6.3.1: Provability implications from LKe to G= and from G= to
LKe without essential cuts over a language with equality. The §6.1
sequent-level free/bound convention on the end sequent supplies the
LKe-to-G= direction under E-CUTFB; the reverse direction holds independently
of that convention. -/
theorem geq_lke_equivalence {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L) (hCross : crossNoFreeBound seq) :
    (lkeProvable seq → sequentProvableEq hL seq) ∧
    (sequentProvableEq hL seq → lkeProvableWithoutEssentialCuts seq) := by
-- BEGIN PROOF
  constructor
  · intro h
    have hvalid := lkeProvable_valid seq h
    exact completenessGEq_cross hL seq hCross hvalid
  · intro h
    exact sequentProvableEq_lkeNoEssentialCuts hL seq h

proof_of gentzenHaupsatzLKe := by
  -- BEGIN PROOF
    constructor
    · intro h
      exact (geq_lke_equivalence hL seq hCross).2
        ((geq_lke_equivalence hL seq hCross).1 h)
    · intro ⟨T, _⟩
      exact ⟨T⟩


proof_of lke_inessential_cut_elimination := by
  -- REPAIR(T6-36): proof pending
  sorry


end LCS.CutElim.LKe.Equivalence

end
