import LCS.Herbrand.SHGTheorem.Main.SHG

section

namespace LCS.Herbrand.SHGTheorem.Main

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.SHGTheorem

open LCS.Herbrand.SHGTheorem.Herbrand

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.CutElim.Hauptsatz

open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Helper: if `init` and every element of `fs` evaluates to true at
`s`, then the left-associated foldl conjunction
`fs.foldl (fun acc f => .conj acc f) init` evaluates to true at `s`.
Used by the later conjunction semantics helpers. -/
theorem formulaEvalN_foldl_conj {L : Language} (M : Structure L)
    (s : Assignment M) (init : FormulaN L) (fs : List (FormulaN L))
    (hInit : formulaEvalN M init s)
    (hFs : ∀ f ∈ fs, formulaEvalN M f s) :
    formulaEvalN M
      (fs.foldl (fun acc f => FormulaN.conj acc f) init) s := by
-- BEGIN PROOF
  induction fs generalizing init with
  | nil => exact hInit
  | cons f rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · -- Show: formulaEvalN M (conj init f) s
      refine ⟨hInit, ?_⟩
      exact hFs f (by simp)
    · intro g hg
      exact hFs g (by simp; right; exact hg)





helper /-- Theorem 7.6.1(b), result specification: from provability of the
original A ->, there exists a quantifier-free c-instance C of the fixed
Skolem form such that not C is provable, represented in NNF by C ->.
Input and output use G1nnf without equality and G1nnf= with equality; C
lives in spec.language. The conclusion is a provability proposition.
Effective production of C from an input proof remains deferred under OD-A17;
this Prop-valued specification does not implement that algorithm. -/
theorem shgTheorem_effective {L : Language}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols) :
    (∀ hL : L.withoutEquality,
      LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hL
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        G1nnfProvableSet (L := spec.language)
          (show spec.language.withoutEquality from hL)
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) ∧
    (∀ (hL : L.hasEquality = true),
      LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set hL
          (({A} : LCS.Finset (FormulaN L)),
           (∅ : LCS.Finset (FormulaN L))) →
      ∃ (C : FormulaN spec.language),
        isCInstanceOf C (SK spec) ∧
        FirstOrder.SemanticsN.isQuantifierFree C ∧
        LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set
          (L := spec.language) hL
          (({C} : LCS.Finset (FormulaN spec.language)),
           (∅ : LCS.Finset (FormulaN spec.language)))) := by
-- BEGIN PROOF
  exact herbrand_half_lemma spec A hSource hConst

proof_of shgTheorem := ⟨shgTheorem_unsat spec A hSource hConst,
  -- BEGIN PROOF
     (shgTheorem_effective spec A hSource hConst).1,
     (shgTheorem_effective spec A hSource hConst).2⟩


helper /-- Negating each compound-instance witness transfers the Skolem condition
from unsatisfiability to validity. The chosen Skolem form, language and
compound instance are identical on both sides; only the semantic condition
on that instance changes. -/
theorem shgCompoundInstance_negation_duality {L : Language}
    (spec : SkolemSpec L) :
    (∃ C : FormulaN spec.language,
      isCInstanceOf C (SK spec) ∧ ¬ satisfiableN C) ↔
    (∃ C : FormulaN spec.language,
      isCInstanceOf C (SK spec) ∧ universallyValidN (.neg C)) := by
  have dual (C : FormulaN spec.language) :
      ¬ satisfiableN C ↔ universallyValidN (.neg C) := by
    classical
    simp [universallyValidN, validInN, satisfiableN, satisfiableInN,
      formulaEvalN, negM]
  constructor
  · rintro ⟨C, hC, hUnsat⟩
    exact ⟨C, hC, (dual C).mp hUnsat⟩
  · rintro ⟨C, hC, hValid⟩
    exact ⟨C, hC, (dual C).mpr hValid⟩

proof_of shgUnsatisfiability_to_validity := by
  exact (LCS.Herbrand.HerbrandTheorem.skolem_validity_duality
    A (.neg A) rfl).1.trans
      (hUnsatVersion.trans (shgCompoundInstance_negation_duality spec))


proof_of shgValidity_to_unsatisfiability := by
  have dual : ¬ satisfiableN A ↔ universallyValidN (.neg A) := by
    classical
    simp [universallyValidN, validInN, satisfiableN, satisfiableInN,
      formulaEvalN, negM]
  exact dual.trans
    (hValidVersion.trans (shgCompoundInstance_negation_duality spec).symm)


helper /-- The validity formulation obtained from the actual SHG theorem for a
fixed rectified NNF source: not spec.source is valid exactly when the
negation of a compound instance of SK spec is valid. The explicit instance
relation retains the Skolem extension and all well-formedness conditions. -/
theorem shgTheorem_validity {L : Language}
    (spec : SkolemSpec L) (hConst : Nonempty L.constSymbols) :
    universallyValidN (.neg spec.source) ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ universallyValidN (.neg C) := by
  have hUnsat : ¬ satisfiableN spec.source ↔
      ∃ C : FormulaN spec.language,
        isCInstanceOf C (SK spec) ∧ ¬ satisfiableN C := by
    constructor
    · intro h
      obtain ⟨C, ci, hSource, hFormula, hWF, hUnsat⟩ :=
        (shgTheorem_unsat spec spec.source rfl hConst).mp h
      exact ⟨C, ⟨ci, hSource, hFormula, hWF⟩, hUnsat⟩
    · rintro ⟨C, ⟨ci, hSource, hFormula, hWF⟩, hUnsat⟩
      exact (shgTheorem_unsat spec spec.source rfl hConst).mpr
        ⟨C, ci, hSource, hFormula, hWF, hUnsat⟩
  have hDouble : ¬ satisfiableN (.neg (.neg spec.source)) ↔
      ¬ satisfiableN spec.source := by
    classical
    simp [satisfiableN, satisfiableInN, formulaEvalN, negM]
  exact shgUnsatisfiability_to_validity (.neg spec.source) spec
    (hDouble.trans hUnsat)

helper /-- Sequential ground substitution is the same root-to-node replay used
by the occurrence-sensitive Herbrand extraction API. -/
theorem applyGroundSubstitution_eq_replayQuantifierSubstitutionsFormula
    {L : Language} (M : FormulaN L)
    (substitutions : List (Nat × Term L)) :
    applyGroundSubstitution M substitutions =
      Herbrand.replayQuantifierSubstitutionsFormula substitutions M := by
  induction substitutions generalizing M with
  | nil => rfl
  | cons p rest ih =>
    change
      applyGroundSubstitution
          (formulaSubstN M p.2 p.1) rest =
        Herbrand.replayQuantifierSubstitutionsFormula rest
          (formulaSubstN M p.2 p.1)
    exact ih _

helper /-- Sequential substitution preserves quantifier-freeness. -/
theorem applyGroundSubstitution_isQuantifierFree
    {L : Language} (M : FormulaN L)
    (substitutions : List (Nat × Term L))
    (hQF : FirstOrder.SemanticsN.isQuantifierFree M) :
    FirstOrder.SemanticsN.isQuantifierFree
      (applyGroundSubstitution M substitutions) := by
  induction substitutions generalizing M with
  | nil => exact hQF
  | cons p rest ih =>
    change
      FirstOrder.SemanticsN.isQuantifierFree
        (applyGroundSubstitution
          (formulaSubstN M p.2 p.1) rest)
    exact ih _ (qf_formulaSubstN M p.2 p.1 hQF)





end LCS.Herbrand.SHGTheorem.Main

end

section

namespace LCS.Herbrand.SHGTheorem.Main

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.SHGTheorem

open LCS.Herbrand.SHGTheorem.Herbrand

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.CutElim.Hauptsatz

open LCS.FirstOrder.SemanticsN.Substitution

namespace GroundMatrixInstance

helper /-- Every proof-coupled ground matrix instance has a closed leaf. -/
theorem GroundMatrixInstance.toFormula_isClosed {L : Language} {B : FormulaN L}
    (g : GroundMatrixInstance B) :
    FormulaN.isClosed g.toFormula :=
  g.leafClosed

end GroundMatrixInstance

end LCS.Herbrand.SHGTheorem.Main

end

section

namespace LCS.Herbrand.SHGTheorem.Main

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.SHGTheorem

open LCS.Herbrand.SHGTheorem.Herbrand

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.CutElim.Hauptsatz

open LCS.FirstOrder.SemanticsN.Substitution

namespace ConjunctionFlattening

helper /-- If every listed leaf is closed, the represented conjunction is closed. -/
theorem ConjunctionFlattening.isClosed_of_all_leaves_closed {L : Language}
    {F : FormulaN L} {leaves : List (FormulaN L)}
    (flattening : ConjunctionFlattening F leaves)
    (leavesClosed : ∀ A ∈ leaves, FormulaN.isClosed A) :
    FormulaN.isClosed F := by
  induction flattening with
  | leaf A =>
    exact leavesClosed A List.mem_cons_self
  | @conj A B as bs flatteningA flatteningB closedA closedB =>
    have hA : FormulaN.isClosed A :=
      closedA (fun C hC =>
        leavesClosed C (List.mem_append.mpr (Or.inl hC)))
    have hB : FormulaN.isClosed B :=
      closedB (fun C hC =>
        leavesClosed C (List.mem_append.mpr (Or.inr hC)))
    unfold FormulaN.isClosed at hA hB ⊢
    simp [formulaFVN, hA, hB]

helper /-- Two conjunction trees with the same ordered leaf list are logically
equivalent, regardless of their binary bracketing. -/
theorem ConjunctionFlattening.foLogEquivN_of_same_leaves {L : Language}
    {F G : FormulaN L} {leaves : List (FormulaN L)}
    (flatteningF : ConjunctionFlattening F leaves)
    (flatteningG : ConjunctionFlattening G leaves) :
    LCS.FirstOrder.Semantics.Equivalence.foLogEquivN F G := by
  intro M s
  simp only [formulaEvalN]
  have evalF := flatteningF.formulaEvalN_iff_all_leaves M s
  have evalG := flatteningG.formulaEvalN_iff_all_leaves M s
  exact
    ⟨fun hF => evalG.mpr (evalF.mp hF),
     fun hG => evalF.mpr (evalG.mp hG)⟩

helper /-- Rebracketing a fixed ordered leaf list preserves satisfiability. -/
theorem ConjunctionFlattening.satisfiableN_iff_of_same_leaves {L : Language}
    {F G : FormulaN L} {leaves : List (FormulaN L)}
    (flatteningF : ConjunctionFlattening F leaves)
    (flatteningG : ConjunctionFlattening G leaves) :
    satisfiableN F ↔ satisfiableN G := by
  constructor
  · rintro ⟨M, s, hF⟩
    exact
      ⟨M, s, (flatteningG.formulaEvalN_iff_all_leaves M s).mpr
        ((flatteningF.formulaEvalN_iff_all_leaves M s).mp hF)⟩
  · rintro ⟨M, s, hG⟩
    exact
      ⟨M, s, (flatteningF.formulaEvalN_iff_all_leaves M s).mpr
        ((flatteningG.formulaEvalN_iff_all_leaves M s).mp hG)⟩

helper /-- Rebracketing a fixed ordered leaf list also preserves
unsatisfiability. -/
theorem ConjunctionFlattening.unsatisfiableN_iff_of_same_leaves {L : Language}
    {F G : FormulaN L} {leaves : List (FormulaN L)}
    (flatteningF : ConjunctionFlattening F leaves)
    (flatteningG : ConjunctionFlattening G leaves) :
    ¬ satisfiableN F ↔ ¬ satisfiableN G := by
  have hSat :=
    satisfiableN_iff_of_same_leaves flatteningF flatteningG
  exact
    ⟨fun hF hG => hF (hSat.mpr hG),
     fun hG hF => hG (hSat.mp hF)⟩

end ConjunctionFlattening

end LCS.Herbrand.SHGTheorem.Main

end
