import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.Axioms

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

/-- The nonlogical head symbol of an equality axiom is supported by
the root sequent. Reflexivity and built-in equality congruence have no
function- or named-predicate head to check. -/
def equalityAxiomSupportedBy {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) : LKeEqualityAxiom L → Prop
  | .refl _ => True
  | .funcCong f _ _ => f ∈ sequentFunSymbolsList S
  | .predCong P _ _ => P ∈ sequentPredSymbolsList S
  | .eqCong _ _ _ _ => True

/-- Every equality-axiom leaf in an LKe proof uses a function or
named predicate occurring in the designated root sequent. -/
def lkeEqualityLeavesSupportedBy {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) :
    {q : Sequent L} → LKeProofTree q → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ ax => equalityAxiomSupportedBy S ax
  | _, .onePremise _ t => lkeEqualityLeavesSupportedBy S t
  | _, .twoPremise _ t₁ t₂ =>
      lkeEqualityLeavesSupportedBy S t₁ ∧
        lkeEqualityLeavesSupportedBy S t₂

private theorem validBridgeTermFunSymbols_mem_occurs {L : Language}
    {f : L.funSymbols} {t : Term L}
    (h : f ∈ validBridgeTermFunSymbols t) :
    validBridgeTermFunOccurs f t := by
  induction t with
  | var _ =>
      simp [validBridgeTermFunSymbols] at h
  | const _ =>
      simp [validBridgeTermFunSymbols] at h
  | func g ts ih =>
      simp only [validBridgeTermFunSymbols, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · rw [List.mem_flatten] at h
        obtain ⟨xs, hxs, hf⟩ := h
        rw [List.mem_ofFn] at hxs
        obtain ⟨i, rfl⟩ := hxs
        exact Or.inr ⟨i, ih i hf⟩

private theorem validBridgeFormulaFunSymbols_mem_occurs {L : Language}
    {f : L.funSymbols} {A : FormulaN L}
    (h : f ∈ validBridgeFormulaFunSymbols A) :
    validBridgeFormulaFunOccurs f A := by
  induction A with
  | predN P ts =>
      rw [validBridgeFormulaFunSymbols, List.mem_flatten] at h
      obtain ⟨xs, hxs, hf⟩ := h
      rw [List.mem_ofFn] at hxs
      obtain ⟨i, rfl⟩ := hxs
      exact ⟨i, validBridgeTermFunSymbols_mem_occurs hf⟩
  | eq_ hL t₁ t₂ =>
      simp only [validBridgeFormulaFunSymbols, List.mem_append] at h
      exact h.imp validBridgeTermFunSymbols_mem_occurs
        validBridgeTermFunSymbols_mem_occurs
  | neg A ih =>
      exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [validBridgeFormulaFunSymbols, List.mem_append] at h
      exact h.imp ihA ihB
  | all x A ih | ex x A ih =>
      exact ih h

private theorem validBridgeFormulaPredSymbols_mem_occurs {L : Language}
    {P : L.predSymbols} {A : FormulaN L}
    (h : P ∈ validBridgeFormulaPredSymbols A) :
    validBridgeFormulaPredOccurs P A := by
  induction A with
  | predN Q ts =>
      simpa [validBridgeFormulaPredSymbols,
        validBridgeFormulaPredOccurs] using h
  | eq_ hL t₁ t₂ =>
      simp [validBridgeFormulaPredSymbols] at h
  | neg A ih =>
      exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [validBridgeFormulaPredSymbols, List.mem_append] at h
      exact h.imp ihA ihB
  | all x A ih | ex x A ih =>
      exact ih h

private theorem validBridgeTermFunOccurs_mem_sequentTermFunSymbols
    {L : Language} {f : L.funSymbols} {t : Term L}
    (h : validBridgeTermFunOccurs f t) :
    f ∈ sequentFunSymbolsList.termFunSymbols t := by
  induction t with
  | var _ =>
      exact h.elim
  | const _ =>
      exact h.elim
  | func g ts ih =>
      simp only [validBridgeTermFunOccurs] at h
      unfold sequentFunSymbolsList.termFunSymbols
      rcases h with rfl | ⟨i, hi⟩
      · exact List.mem_append_left _ (List.Mem.head _)
      · exact List.mem_append_right _
          (List.mem_flatMap.mpr
            ⟨i, List.mem_finRange i, ih i hi⟩)

private theorem validBridgeFormulaFunOccurs_mem_sequentFormulaFunSymbols
    {L : Language} {f : L.funSymbols} {A : FormulaN L}
    (h : validBridgeFormulaFunOccurs f A) :
    f ∈ sequentFunSymbolsList.formulaFunSyms A := by
  induction A with
  | predN P ts =>
      obtain ⟨i, hi⟩ := h
      unfold sequentFunSymbolsList.formulaFunSyms
      exact List.mem_flatMap.mpr
        ⟨i, List.mem_finRange i,
          validBridgeTermFunOccurs_mem_sequentTermFunSymbols hi⟩
  | eq_ hL t₁ t₂ =>
      unfold sequentFunSymbolsList.formulaFunSyms
      rcases h with h | h
      · exact List.mem_append_left _
          (validBridgeTermFunOccurs_mem_sequentTermFunSymbols h)
      · exact List.mem_append_right _
          (validBridgeTermFunOccurs_mem_sequentTermFunSymbols h)
  | neg A ih =>
      exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      unfold sequentFunSymbolsList.formulaFunSyms
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih =>
      exact ih h

private theorem validBridgeFormulaPredOccurs_mem_sequentFormulaPredSymbols
    {L : Language} {P : L.predSymbols} {A : FormulaN L}
    (h : validBridgeFormulaPredOccurs P A) :
    P ∈ sequentPredSymbolsList.formulaPredSyms A := by
  induction A with
  | predN Q ts =>
      simpa [validBridgeFormulaPredOccurs,
        sequentPredSymbolsList.formulaPredSyms] using h
  | eq_ hL t₁ t₂ =>
      exact h.elim
  | neg A ih =>
      exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      unfold sequentPredSymbolsList.formulaPredSyms
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih =>
      exact ih h

private theorem validBridgeSuccedentFormula_funOccurs
    {L : Language} (P : FormulaN L) (f : L.funSymbols) :
    ∀ Δ : List (FormulaN L),
      validBridgeFormulaFunOccurs f
          (validBridgeSuccedentFormula P Δ) →
        validBridgeFormulaFunOccurs f P ∨
          ∃ A ∈ Δ, validBridgeFormulaFunOccurs f A := by
  intro Δ
  induction Δ with
  | nil =>
      intro h
      simp only [validBridgeSuccedentFormula, validBridgeBottom,
        validBridgeFormulaFunOccurs] at h
      exact Or.inl (h.elim (fun hP => hP) (fun hP => hP))
  | cons A Δ ih =>
      intro h
      simp only [validBridgeSuccedentFormula,
        validBridgeFormulaFunOccurs] at h
      rcases h with hA | h
      · exact Or.inr ⟨A, List.Mem.head _, hA⟩
      · rcases ih h with hP | ⟨B, hB, hOcc⟩
        · exact Or.inl hP
        · exact Or.inr
            ⟨B, List.mem_cons_of_mem _ hB, hOcc⟩

private theorem validBridgeSuccedentFormula_predOccurs
    {L : Language} (P : FormulaN L) (Q : L.predSymbols) :
    ∀ Δ : List (FormulaN L),
      validBridgeFormulaPredOccurs Q
          (validBridgeSuccedentFormula P Δ) →
        validBridgeFormulaPredOccurs Q P ∨
          ∃ A ∈ Δ, validBridgeFormulaPredOccurs Q A := by
  intro Δ
  induction Δ with
  | nil =>
      intro h
      simp only [validBridgeSuccedentFormula, validBridgeBottom,
        validBridgeFormulaPredOccurs] at h
      exact Or.inl (h.elim (fun hP => hP) (fun hP => hP))
  | cons A Δ ih =>
      intro h
      simp only [validBridgeSuccedentFormula,
        validBridgeFormulaPredOccurs] at h
      rcases h with hA | h
      · exact Or.inr ⟨A, List.Mem.head _, hA⟩
      · rcases ih h with hP | ⟨B, hB, hOcc⟩
        · exact Or.inl hP
        · exact Or.inr
            ⟨B, List.mem_cons_of_mem _ hB, hOcc⟩

private theorem validBridgeSequentFormula_funOccurs
    {L : Language} (P : FormulaN L) (f : L.funSymbols)
    (Δ : List (FormulaN L)) :
    ∀ Γ : List (FormulaN L),
      validBridgeFormulaFunOccurs f
          (validBridgeSequentFormula P Δ Γ) →
        validBridgeFormulaFunOccurs f P ∨
          ∃ A ∈ Γ ++ Δ, validBridgeFormulaFunOccurs f A := by
  intro Γ
  induction Γ with
  | nil =>
      simpa [validBridgeSequentFormula] using
        validBridgeSuccedentFormula_funOccurs P f Δ
  | cons A Γ ih =>
      intro h
      simp only [validBridgeSequentFormula,
        validBridgeFormulaFunOccurs] at h
      rcases h with hA | h
      · exact Or.inr
          ⟨A, List.mem_append_left _ (List.Mem.head _), hA⟩
      · rcases ih h with hP | ⟨B, hB, hOcc⟩
        · exact Or.inl hP
        · exact Or.inr
            ⟨B, by
              rw [List.cons_append]
              exact List.mem_cons_of_mem _ hB,
              hOcc⟩

private theorem validBridgeSequentFormula_predOccurs
    {L : Language} (P : FormulaN L) (Q : L.predSymbols)
    (Δ : List (FormulaN L)) :
    ∀ Γ : List (FormulaN L),
      validBridgeFormulaPredOccurs Q
          (validBridgeSequentFormula P Δ Γ) →
        validBridgeFormulaPredOccurs Q P ∨
          ∃ A ∈ Γ ++ Δ, validBridgeFormulaPredOccurs Q A := by
  intro Γ
  induction Γ with
  | nil =>
      simpa [validBridgeSequentFormula] using
        validBridgeSuccedentFormula_predOccurs P Q Δ
  | cons A Γ ih =>
      intro h
      simp only [validBridgeSequentFormula,
        validBridgeFormulaPredOccurs] at h
      rcases h with hA | h
      · exact Or.inr
          ⟨A, List.mem_append_left _ (List.Mem.head _), hA⟩
      · rcases ih h with hP | ⟨B, hB, hOcc⟩
        · exact Or.inl hP
        · exact Or.inr
            ⟨B, by
              rw [List.cons_append]
              exact List.mem_cons_of_mem _ hB,
              hOcc⟩

private theorem validBridgeSequentFormula_fun_mem_root
    {L : Language} [DecidableEq L.funSymbols]
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hP : P ∈ Γ ++ Δ) (f : L.funSymbols)
    (hf : f ∈ validBridgeFormulaFunSymbols
      (validBridgeSequentFormula P Δ Γ)) :
    f ∈ sequentFunSymbolsList (Sequent.mk Γ Δ) := by
  have hOcc :=
    validBridgeFormulaFunSymbols_mem_occurs hf
  rcases validBridgeSequentFormula_funOccurs P f Δ Γ hOcc with
    hInP | ⟨A, hA, hInA⟩
  · unfold sequentFunSymbolsList
    rw [List.mem_eraseDups, List.mem_flatMap]
    exact
      ⟨P, hP,
        validBridgeFormulaFunOccurs_mem_sequentFormulaFunSymbols hInP⟩
  · unfold sequentFunSymbolsList
    rw [List.mem_eraseDups, List.mem_flatMap]
    exact
      ⟨A, hA,
        validBridgeFormulaFunOccurs_mem_sequentFormulaFunSymbols hInA⟩

private theorem validBridgeSequentFormula_pred_mem_root
    {L : Language} [DecidableEq L.predSymbols]
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hP : P ∈ Γ ++ Δ) (Q : L.predSymbols)
    (hQ : Q ∈ validBridgeFormulaPredSymbols
      (validBridgeSequentFormula P Δ Γ)) :
    Q ∈ sequentPredSymbolsList (Sequent.mk Γ Δ) := by
  have hOcc :=
    validBridgeFormulaPredSymbols_mem_occurs hQ
  rcases validBridgeSequentFormula_predOccurs P Q Δ Γ hOcc with
    hInP | ⟨A, hA, hInA⟩
  · unfold sequentPredSymbolsList
    rw [List.mem_eraseDups, List.mem_flatMap]
    exact
      ⟨P, hP,
        validBridgeFormulaPredOccurs_mem_sequentFormulaPredSymbols hInP⟩
  · unfold sequentPredSymbolsList
    rw [List.mem_eraseDups, List.mem_flatMap]
    exact
      ⟨A, hA,
        validBridgeFormulaPredOccurs_mem_sequentFormulaPredSymbols hInA⟩

/-- An indexed LKe proof whose equality leaves are certified against
a designated root support. The rule indices are the ordinary LKe
indices; only the equality-leaf constructor carries an extra local
support certificate. -/
inductive RootSupportedLKeProof {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) : Sequent L → Type where
  | axiom_ (q : Sequent L) (h : isFOLKAxiom q) :
      RootSupportedLKeProof S q
  | eqAxiom (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L)
      (hax : equalityAxiomSupportedBy S ax) :
      RootSupportedLKeProof S (ax.toSequent hL)
  | onePremise {prem conc : Sequent L}
      (rule : FOLKStep1 prem conc)
      (t : RootSupportedLKeProof S prem) :
      RootSupportedLKeProof S conc
  | twoPremise {prem₁ prem₂ conc : Sequent L}
      (rule : FOLKStep2 prem₁ prem₂ conc)
      (t₁ : RootSupportedLKeProof S prem₁)
      (t₂ : RootSupportedLKeProof S prem₂) :
      RootSupportedLKeProof S conc

end LCS.CutElim.Interpolation.Equality
end

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka
namespace RootSupportedLKeProof

/-- Erase support certificates, retaining the exact indexed LKe
derivation. -/
def toLKeProof {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S q : Sequent L} :
    RootSupportedLKeProof S q → LKeProofTree q
  | .axiom_ q h => .axiom_ q h
  | .eqAxiom hL ax _ => .eqAxiom hL ax
  | .onePremise rule t => .onePremise rule t.toLKeProof
  | .twoPremise rule t₁ t₂ =>
      .twoPremise rule t₁.toLKeProof t₂.toLKeProof

/-- Embed an ordinary LK proof; it introduces no equality leaves and
therefore satisfies every root-support certificate. -/
def lk {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) :
    {q : Sequent L} → FOLKProofTree q → RootSupportedLKeProof S q
  | _, .axiom_ q h => .axiom_ q h
  | _, .onePremise rule t => .onePremise rule (lk S t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise rule (lk S t₁) (lk S t₂)

theorem toLKeProof_supported {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S q : Sequent L} (t : RootSupportedLKeProof S q) :
    lkeEqualityLeavesSupportedBy S t.toLKeProof := by
  induction t with
  | axiom_ q h =>
      trivial
  | eqAxiom hL ax hax =>
      exact hax
  | onePremise rule t ih =>
      exact ih
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
      exact ⟨ih₁, ih₂⟩

end RootSupportedLKeProof
end LCS.CutElim.Interpolation.Equality
end

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

private def validBridgeLiftRootSupportedLKeProof
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hP : P ∈ Γ ++ Δ) :
    {q : Sequent
      (ValidBridgeSupportLanguage
        (validBridgeSequentFormula P Δ Γ))} →
      LKeProofTree q →
      RootSupportedLKeProof (Sequent.mk Γ Δ)
        (validBridgeLiftSequent
          (validBridgeSequentFormula P Δ Γ) q)
  | _, .axiom_ q h =>
      .axiom_ _ (validBridgeLift_isFOLKAxiom _ h)
  | _, .eqAxiom hL ax => by
      rw [validBridgeLiftEqualityAxiom_toSequent
        (validBridgeSequentFormula P Δ Γ) hL ax]
      refine RootSupportedLKeProof.eqAxiom
        (L := L) (S := Sequent.mk Γ Δ) hL
        (validBridgeLiftEqualityAxiom (L := L)
          (validBridgeSequentFormula P Δ Γ) ax) ?_
      cases ax with
      | refl u =>
          trivial
      | funcCong f ss ts =>
          exact validBridgeSequentFormula_fun_mem_root
            P Γ Δ hP f.1 f.2
      | predCong Q ss ts =>
          exact validBridgeSequentFormula_pred_mem_root
            P Γ Δ hP Q.1 Q.2
      | eqCong s₁ s₂ t₁ t₂ =>
          trivial
  | _, .onePremise rule t =>
      .onePremise (validBridgeLiftFOLKStep1
        (validBridgeSequentFormula P Δ Γ) rule)
        (validBridgeLiftRootSupportedLKeProof P Γ Δ hP t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise (validBridgeLiftFOLKStep2
        (validBridgeSequentFormula P Δ Γ) rule)
        (validBridgeLiftRootSupportedLKeProof P Γ Δ hP t₁)
        (validBridgeLiftRootSupportedLKeProof P Γ Δ hP t₂)

/-- A proof of a nonempty valid sequent can be replaced by a certified
proof whose equality leaves use only function and predicate heads from
the exact root sequent. The construction restricts the semantic bridge
to the finite language support of a one-formula encoding of the root,
lifts that proof back, and then decodes the formula by ordinary LK
rules. -/
theorem exists_rootSupportedLKeProof
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hP : P ∈ Γ ++ Δ)
    (t : LKeProofTree (Sequent.mk Γ Δ)) :
    Nonempty
      (RootSupportedLKeProof
        (Sequent.mk Γ Δ) (Sequent.mk Γ Δ)) := by
  let F := validBridgeSequentFormula P Δ Γ
  let K := ValidBridgeSupportLanguage F
  let R : FormulaN K := validBridgeRestrictSelf F
  let q : Sequent K := Sequent.mk [] [R]
  have hFvalid :
      ∀ (M : Structure L) (s : Assignment M),
        formulaEvalN M F s := by
    exact validBridgeSequentFormula_valid P Γ Δ
      (lkeProofTree_valid t)
  have hRvalid :
      ∀ (M : Structure K) (s : Assignment M),
        formulaEvalN M R s := by
    intro M s
    apply (validBridgeRestrictSelf_eval F M s).mpr
    exact hFvalid (validBridgeExtendStructure F M) s
  have hqvalid : sequentValid q := by
    intro M s _
    exact ⟨R, by simp [q], hRvalid M s⟩
  let tq : LKeProofTree q :=
    Classical.choice (lkeProvable_of_valid q hqvalid)
  let tqLifted :
      RootSupportedLKeProof (Sequent.mk Γ Δ)
        (validBridgeLiftSequent F q) :=
    validBridgeLiftRootSupportedLKeProof P Γ Δ hP tq
  have hLiftR : validBridgeLiftFormula F R = F := by
    exact validBridgeLift_restrictSelf F
  have hqLift :
      validBridgeLiftSequent F q = Sequent.mk [] [F] := by
    simp [q, validBridgeLiftSequent, hLiftR]
  let tFormula :
      RootSupportedLKeProof
        (Sequent.mk Γ Δ) (Sequent.mk [] [F]) :=
    hqLift ▸ tqLifted
  obtain ⟨tDecode, _⟩ :=
    validBridgeSequentFormula_left P Δ Γ
  let tResult :=
    RootSupportedLKeProof.twoPremise
      (FOLKStep2.cut F [] [] Γ Δ)
      tFormula
      (RootSupportedLKeProof.lk
        (Sequent.mk Γ Δ) tDecode)
  exact ⟨by simpa using tResult⟩

/-- Certified noncomputable root-support normalization with an
explicit root formula as the one-formula encoding pivot. -/
noncomputable def normalizeLKeProofSupportCertifiedWithPivot
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hP : P ∈ Γ ++ Δ)
    (t : LKeProofTree (Sequent.mk Γ Δ)) :
    RootSupportedLKeProof
      (Sequent.mk Γ Δ) (Sequent.mk Γ Δ) :=
  Classical.choice
    (exists_rootSupportedLKeProof P Γ Δ hP t)

/-- Every LKe proof has a formula in its root sequent. Otherwise its
soundness would validate the empty sequent in the one-point
structure, which is impossible. -/
theorem lkeProofTree_root_has_formula
    {L : Language} {S : Sequent L}
    (t : LKeProofTree S) :
    ∃ P, P ∈ S.antecedent ++ S.succedent := by
  rcases S with ⟨Γ, Δ⟩
  cases Γ with
  | cons A Γ =>
      exact ⟨A, by simp⟩
  | nil =>
      cases Δ with
      | cons B Δ =>
          exact ⟨B, by simp⟩
      | nil =>
          have hvalid := lkeProofTree_valid t
          let M : Structure L :=
            { carrier := Unit
              carrierNonempty := ⟨()⟩
              interpFunc := fun _ _ => ()
              interpConst := fun _ => ()
              interpPred := fun _ _ => False }
          let v : Assignment M := fun _ => ()
          obtain ⟨B, hB, _⟩ := hvalid M v (by
            intro A hA
            simp at hA)
          simp at hB

theorem exists_rootSupportedLKeProof_of_lkeProof
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S : Sequent L} (t : LKeProofTree S) :
    Nonempty (RootSupportedLKeProof S S) := by
  rcases S with ⟨Γ, Δ⟩
  obtain ⟨P, hP⟩ := lkeProofTree_root_has_formula t
  exact exists_rootSupportedLKeProof P Γ Δ hP t

/-- Canonical certified root-support normalization. The pivot is
chosen internally from the exact root sequent. -/
noncomputable def normalizeLKeProofSupportCertified
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S : Sequent L} (t : LKeProofTree S) :
    RootSupportedLKeProof S S :=
  Classical.choice
    (exists_rootSupportedLKeProof_of_lkeProof t)

/-- Erasure of certified normalization back to the canonical LKe
carrier. Its result is indexed by the exact input root sequent. -/
noncomputable def normalizeLKeProofSupport
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S : Sequent L} (t : LKeProofTree S) :
    LKeProofTree S :=
  (normalizeLKeProofSupportCertified t).toLKeProof

theorem normalizeLKeProofSupport_supported
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    {S : Sequent L} (t : LKeProofTree S) :
    lkeEqualityLeavesSupportedBy S
      (normalizeLKeProofSupport t) :=
  RootSupportedLKeProof.toLKeProof_supported
    (normalizeLKeProofSupportCertified t)

-- ===================================================================
-- Helper: foldr all is valid if inner is valid under all assignments
-- ===================================================================

theorem foldr_all_valid {L : Language} (M : Structure L) (s : Assignment M)
    (start count : Nat) (inner : FormulaN L)
    (h : ∀ (s' : Assignment M), formulaEvalN M inner s') :
    formulaEvalN M ((List.range count).foldr (fun i acc => FormulaN.all (start + i) acc) inner) s := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => simp [List.range]; exact h s
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    apply ih; intro s'; simp [formulaEvalN]; intro a
    exact h (assignUpdate s' (start + n) a)

-- ===================================================================
-- Helper: right-nested conjunction member evaluates to true
-- ===================================================================

theorem conjoin_cons_cons {L : Language} (A B : FormulaN L)
    (rest : List (FormulaN L)) :
    conjoinFormulae A (A :: B :: rest) = A.conj (conjoinFormulae B (B :: rest)) := by
  have defaults : ∀ (tl : List (FormulaN L)) (hd d e : FormulaN L),
      conjoinFormulae d (hd :: tl) = conjoinFormulae e (hd :: tl) := by
    intro tl
    induction tl with
    | nil => intros; rfl
    | cons x xs ih =>
      intro hd d e
      simp only [conjoinFormulae]
      rw [ih x d e]
  change A.conj (conjoinFormulae A (B :: rest)) = _
  rw [defaults rest B A B]

theorem conjoin_mem_eval {L : Language} (M : Structure L) (s : Assignment M)
    (hd : FormulaN L) (tl : List (FormulaN L))
    (h : formulaEvalN M (conjoinFormulae hd (hd :: tl)) s) :
    ∀ A ∈ hd :: tl, formulaEvalN M A s := by
  exact conjoinFormulaeEval h

-- ===================================================================
-- Helper: map_finRange_nil
-- ===================================================================

theorem map_finRange_nil {n : Nat} {α : Type} (f : Fin n → α)
    (h : (List.finRange n).map f = []) : n = 0 := by
-- BEGIN PROOF
  cases n with
  | zero => rfl
  | succ k => simp [List.finRange] at h

-- ===================================================================
-- Helper: closedFunCongAxiom is universally valid
-- ===================================================================

set_option maxHeartbeats 1600000 in
theorem closedFunCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedFunCongAxiom hL f) s := by
-- BEGIN PROOF
  unfold closedFunCongAxiom; simp only []
  apply foldr_all_valid; intro s1; apply foldr_all_valid; intro s2
  generalize hep : (List.finRange (L.funArity f)).map
    (fun (i : Fin (L.funArity f)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
      (Term.var (L.funArity f + (i : Nat)))) = eqPairs
  cases eqPairs with
  | nil =>
    simp [formulaEvalN, termEval]
    congr 1; funext i; exact absurd i.isLt (by
      have := map_finRange_nil _ hep; omega)
  | cons hd tl =>
    simp only [formulaEvalN, termEval]
    intro hAnte
    congr 1; funext i
    have hMem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (L.funArity f + (i : Nat))) ∈ hd :: tl := by
      rw [← hep]; exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hEq := conjoin_mem_eval M s2 hd tl hAnte _ hMem
    simp [formulaEvalN, termEval] at hEq
    exact hEq

-- ===================================================================
-- Helper: closedPredCongAxiom is universally valid
-- ===================================================================

set_option maxHeartbeats 1600000 in
theorem closedPredCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedPredCongAxiom hL P) s := by
-- BEGIN PROOF
  unfold closedPredCongAxiom; simp only []
  apply foldr_all_valid; intro s1; apply foldr_all_valid; intro s2
  generalize hprem : (List.finRange (L.predArity P)).map
    (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
      (Term.var (L.predArity P + (i : Nat)))) ++
    [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] = premises
  cases premises with
  | nil =>
    exfalso
    have hmem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈
        (List.finRange (L.predArity P)).map
          (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
            (Term.var (L.predArity P + (i : Nat)))) ++
        [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
      List.mem_append_right _ (List.Mem.head ..)
    rw [hprem] at hmem; simp at hmem
  | cons hd tl =>
    simp only [formulaEvalN, termEval]
    intro hAnte
    have hAllMem := conjoin_mem_eval M s2 hd tl hAnte
    have hPredMem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈ hd :: tl := by
      have hmem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈
          (List.finRange (L.predArity P)).map
            (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
              (Term.var (L.predArity P + (i : Nat)))) ++
          [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
        List.mem_append_right _ (List.Mem.head ..)
      rw [hprem] at hmem; exact hmem
    have hPred := hAllMem _ hPredMem
    simp only [formulaEvalN, termEval] at hPred
    have hEqs : ∀ (i : Fin (L.predArity P)), s2 i.val = s2 (L.predArity P + i.val) := by
      intro i
      have hEqMem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
          (Term.var (L.predArity P + (i : Nat))) ∈ hd :: tl := by
        have hmem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
            (Term.var (L.predArity P + (i : Nat))) ∈
            (List.finRange (L.predArity P)).map
              (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
                (Term.var (L.predArity P + (i : Nat)))) ++
            [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
          List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
        rw [hprem] at hmem; exact hmem
      have := hAllMem _ hEqMem
      simp only [formulaEvalN, termEval] at this; exact this
    have : (fun i : Fin (L.predArity P) => s2 (L.predArity P + i.val)) =
        (fun i : Fin (L.predArity P) => s2 i.val) :=
      funext (fun i => (hEqs i).symm)
    rw [this]; exact hPred

-- ===================================================================
-- Helper: closedEqCongAxiom is universally valid
-- ===================================================================

theorem closedEqCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedEqCongAxiom hL) s := by
-- BEGIN PROOF
  simp only [closedEqCongAxiom, FormulaN.allList, List.foldr_cons,
    List.foldr_nil, formulaEvalN]
  rintro a0 a1 a2 a3 ⟨h1, h2, h3⟩
  simp only [formulaEvalN] at h1 h2 h3 ⊢
  rw [← h1, h3, h2]

-- ===================================================================
-- Helper: if A is universally valid, then lkeProvable ([] -> [A])
-- ===================================================================

theorem lkeProvable_of_universally_valid {L : Language}
    (A : FormulaN L)
    (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
    lkeProvable { antecedent := [], succedent := [A] } := by
-- BEGIN PROOF
  apply lkeProvable_of_sequentValid
  intro M s _; exact ⟨A, List.Mem.head _, hvalid M s⟩

-- ===================================================================
-- Helper: every formula in closedEqualityAxioms is universally valid
-- ===================================================================

theorem closedEqualityAxioms_universally_valid {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (A : FormulaN L)
    (hA : A ∈ closedEqualityAxioms hL S) :
    ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s := by
-- BEGIN PROOF
  simp only [closedEqualityAxioms] at hA
  rcases List.mem_append.mp hA with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      intro M s; simp [closedReflAxiom, formulaEvalN, termEval, assignUpdate]
    · rw [List.mem_map] at hFun
      obtain ⟨f, _, hfEq⟩ := hFun; subst hfEq
      exact closedFunCongAxiom_eval hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, _, hPEq⟩ := hPred; subst hPEq
      exact closedPredCongAxiom_eval hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_eval hL

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): se_formulae_lke_provable
-- ===================================================================

/-- Lemma 6.5.3 (companion): Every formula A in
closedEqualityAxioms S is LKe-provable (i.e., the sequent
[] -> [A] is LKe-provable). Each closed equality axiom is a
universally quantified statement about reflexivity or congruence,
derivable from the corresponding equality axiom schemas. -/
theorem se_formulae_lke_provable {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (A : FormulaN L)
    (hA : A ∈ closedEqualityAxioms hL S) :
    lkeProvable { antecedent := [], succedent := [A] } :=
-- BEGIN PROOF
  lkeProvable_of_universally_valid A (closedEqualityAxioms_universally_valid hL S A hA)

theorem folkProvable_onePremise {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (h : folkProvable prem) : folkProvable conc := by
  obtain ⟨t⟩ := h
  exact ⟨.onePremise rule t⟩

theorem folkProvable_twoPremise {L : Language}
    {prem₁ prem₂ conc : Sequent L} (rule : FOLKStep2 prem₁ prem₂ conc)
    (h₁ : folkProvable prem₁) (h₂ : folkProvable prem₂) :
    folkProvable conc := by
  obtain ⟨t₁⟩ := h₁
  obtain ⟨t₂⟩ := h₂
  exact ⟨.twoPremise rule t₁ t₂⟩

theorem folkProvable_weakenLeftList {L : Language}
    (pfx Γ Δ : List (FormulaN L))
    (h : folkProvable (Sequent.mk Γ Δ)) :
    folkProvable (Sequent.mk (pfx ++ Γ) Δ) := by
  induction pfx with
  | nil => simpa using h
  | cons A pfx ih =>
      exact folkProvable_onePremise
        (.weakenLeft A (pfx ++ Γ) Δ) ih

private theorem folkProvable_exchangeLeftAt {L : Language}
    (pfx : List (FormulaN L)) (A B : FormulaN L)
    (sfx Δ : List (FormulaN L))
    (h : folkProvable
      (Sequent.mk (pfx ++ [A, B] ++ sfx) Δ)) :
    folkProvable
      (Sequent.mk (pfx ++ [B, A] ++ sfx) Δ) :=
  folkProvable_onePremise (.exchangeLeft pfx A B sfx Δ) h

private theorem folkProvable_sinkLeft {L : Language}
    (pfx : List (FormulaN L)) (A : FormulaN L)
    (mid sfx Δ : List (FormulaN L))
    (h : folkProvable
      (Sequent.mk (pfx ++ [A] ++ mid ++ sfx) Δ)) :
    folkProvable
      (Sequent.mk (pfx ++ mid ++ [A] ++ sfx) Δ) := by
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B mid ih =>
      have h₁ : folkProvable
          (Sequent.mk (pfx ++ [A, B] ++ (mid ++ sfx)) Δ) := by
        simpa [List.append_assoc] using h
      have h₂ :=
        folkProvable_exchangeLeftAt pfx A B (mid ++ sfx) Δ h₁
      have h₃ : folkProvable
          (Sequent.mk ((pfx ++ [B]) ++ [A] ++ mid ++ sfx) Δ) := by
        simpa [List.append_assoc] using h₂
      have h₄ := ih (pfx ++ [B]) h₃
      simpa [List.append_assoc] using h₄

private theorem folkProvable_floatLeft {L : Language}
    (pfx : List (FormulaN L)) (A : FormulaN L)
    (mid sfx Δ : List (FormulaN L))
    (h : folkProvable
      (Sequent.mk (pfx ++ mid ++ [A] ++ sfx) Δ)) :
    folkProvable
      (Sequent.mk (pfx ++ [A] ++ mid ++ sfx) Δ) := by
  induction mid generalizing pfx with
  | nil => simpa using h
  | cons B mid ih =>
      have h₁ : folkProvable
          (Sequent.mk ((pfx ++ [B]) ++ mid ++ [A] ++ sfx) Δ) := by
        simpa [List.append_assoc] using h
      have h₂ := ih (pfx ++ [B]) h₁
      have h₃ : folkProvable
          (Sequent.mk (pfx ++ [B, A] ++ (mid ++ sfx)) Δ) := by
        simpa [List.append_assoc] using h₂
      have h₄ :=
        folkProvable_exchangeLeftAt pfx B A (mid ++ sfx) Δ h₃
      simpa [List.append_assoc] using h₄

private theorem folkProvable_contractLeftAt {L : Language}
    (pfx : List (FormulaN L)) (A : FormulaN L)
    (sfx Δ : List (FormulaN L))
    (h : folkProvable
      (Sequent.mk (pfx ++ [A, A] ++ sfx) Δ)) :
    folkProvable
      (Sequent.mk (pfx ++ [A] ++ sfx) Δ) := by
  have h₁ : folkProvable
      (Sequent.mk ([A] ++ pfx ++ ([A] ++ sfx)) Δ) :=
    folkProvable_floatLeft [] A pfx ([A] ++ sfx) Δ (by
      simpa [List.append_assoc] using h)
  have h₂ : folkProvable
      (Sequent.mk ([A] ++ [A] ++ pfx ++ sfx) Δ) :=
    folkProvable_floatLeft [A] A pfx sfx Δ (by
      simpa [List.append_assoc] using h₁)
  have h₃ : folkProvable
      (Sequent.mk (A :: (pfx ++ sfx)) Δ) :=
    folkProvable_onePremise
      (.contractLeft A (pfx ++ sfx) Δ) (by
        simpa [List.append_assoc] using h₂)
  exact folkProvable_sinkLeft [] A pfx sfx Δ (by
    simpa [List.append_assoc] using h₃)

private theorem folkProvable_contractSuffix {L : Language}
    (Γ suffix Δ : List (FormulaN L))
    (hMem : ∀ A, A ∈ suffix → A ∈ Γ)
    (h : folkProvable (Sequent.mk (Γ ++ suffix) Δ)) :
    folkProvable (Sequent.mk Γ Δ) := by
  induction suffix with
  | nil => simpa using h
  | cons A suffix ih =>
      have hA : A ∈ Γ := hMem A (List.Mem.head _)
      obtain ⟨before, after, hΓ⟩ :=
        LCS.CutElim.LKe.Equivalence.perm_mem_split A Γ hA
      have h₁ : folkProvable
          (Sequent.mk
            (before ++ [A] ++ (after ++ [A] ++ suffix)) Δ) := by
        rw [hΓ] at h
        simpa [List.append_assoc] using h
      have h₂ : folkProvable
          (Sequent.mk
            ((before ++ [A]) ++ [A] ++ after ++ suffix) Δ) :=
        folkProvable_floatLeft (before ++ [A]) A after suffix Δ
          (by simpa [List.append_assoc] using h₁)
      have h₃ : folkProvable
          (Sequent.mk (before ++ [A] ++ (after ++ suffix)) Δ) :=
        folkProvable_contractLeftAt before A (after ++ suffix) Δ
          (by simpa [List.append_assoc] using h₂)
      have h₄ : folkProvable (Sequent.mk (Γ ++ suffix) Δ) := by
        rw [hΓ]
        simpa [List.append_assoc] using h₃
      exact ih
        (fun B hB => hMem B (List.Mem.tail _ hB)) h₄

/-- Antecedent monotonicity for indexed LK proofs, including
permutation and duplicate contraction. -/
theorem folkProvable_antecedentMono {L : Language}
    (Γ Γ' Δ : List (FormulaN L))
    (hMem : ∀ A, A ∈ Γ → A ∈ Γ')
    (h : folkProvable (Sequent.mk Γ Δ)) :
    folkProvable (Sequent.mk Γ' Δ) := by
  have h₁ := folkProvable_weakenLeftList Γ' Γ Δ h
  exact folkProvable_contractSuffix Γ' Γ Δ hMem h₁

def termSubstTermsList {L : Language} :
    Term L → List Nat → List (Term L) → Term L
  | t, [], _ => t
  | t, _, [] => t
  | t, x :: xs, u :: us =>
      termSubstTermsList (termSubst t u x) xs us

private theorem termSubstTermsList_not_free {L : Language}
    (t : Term L) (xs : List Nat) (us : List (Term L))
    (h : ∀ x ∈ xs, x ∉ termFV t) :
    termSubstTermsList t xs us = t := by
  induction xs generalizing t us with
  | nil => simp [termSubstTermsList]
  | cons x xs ih =>
      cases us with
      | nil => simp [termSubstTermsList]
      | cons u us =>
          simp only [termSubstTermsList]
          rw [termSubst_not_free t u x (h x (List.mem_cons_self))]
          exact ih t us (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem mem_zip_left {α β : Type}
    {xs : List α} {ys : List β} {x : α} {y : β}
    (h : (x, y) ∈ xs.zip ys) : x ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons a xs ih =>
      cases ys with
      | nil => simp at h
      | cons b ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact Or.inl (Prod.mk.inj h).1
          · exact Or.inr (ih h)

private theorem termSubstTermsList_var_of_zip_mem {L : Language}
    (xs : List Nat) (us : List (Term L)) (x : Nat) (u : Term L)
    (hxs : xs.Nodup)
    (hAvoid : ∀ t ∈ us, ∀ y ∈ xs, y ∉ termFV t)
    (hMem : (x, u) ∈ xs.zip us) :
    termSubstTermsList (.var x) xs us = u := by
  induction xs generalizing us with
  | nil => simp at hMem
  | cons y ys ih =>
      cases us with
      | nil => simp at hMem
      | cons t ts =>
          simp only [List.zip_cons_cons, List.mem_cons] at hMem
          simp only [List.nodup_cons] at hxs
          rcases hMem with hHead | hTail
          · have hxy : x = y := (Prod.mk.inj hHead).1
            have hut : u = t := (Prod.mk.inj hHead).2
            subst x
            subst u
            simp only [termSubstTermsList, termSubst, if_true]
            apply termSubstTermsList_not_free
            intro z hz
            exact hAvoid t (List.mem_cons_self)
              z (List.mem_cons_of_mem y hz)
          · have hxMem : x ∈ ys := by
              exact mem_zip_left hTail
            have hxy : x ≠ y := by
              intro h
              subst x
              exact hxs.1 hxMem
            simp only [termSubstTermsList, termSubst, if_neg hxy]
            exact ih ts hxs.2
              (fun t ht z hz =>
                hAvoid t (List.mem_cons_of_mem _ ht)
                  z (List.mem_cons_of_mem _ hz))
              hTail

private theorem termSubstTermsList_const {L : Language}
    (c : L.constSymbols) (xs : List Nat) (us : List (Term L)) :
    termSubstTermsList (Term.const c) xs us = Term.const c := by
  induction xs generalizing us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [termSubstTermsList, termSubst]
          exact ih us

private theorem termSubstTermsList_func {L : Language}
    (f : L.funSymbols) (args : Fin (L.funArity f) → Term L)
    (xs : List Nat) (us : List (Term L)) :
    termSubstTermsList (Term.func f args) xs us =
      Term.func f (fun i => termSubstTermsList (args i) xs us) := by
  induction xs generalizing args us with
  | nil => simp [termSubstTermsList]
  | cons x xs ih =>
      cases us with
      | nil => simp [termSubstTermsList]
      | cons u us =>
          simp only [termSubstTermsList, termSubst]
          rw [ih]

def termMapVars {L : Language}
    (σ : Nat → Term L) : Term L → Term L
  | .var x => σ x
  | .const c => .const c
  | .func f args => .func f (fun i => termMapVars σ (args i))

private theorem termSubstTermsList_twoStage {L : Language}
    (t : Term L) (xs zs : List Nat) (us : List (Term L)) :
    termSubstTermsList
        (termSubstTermsList t xs (zs.map (@Term.var L))) zs us =
      termMapVars
        (fun x => termSubstTermsList
          (termSubstTermsList (.var x) xs (zs.map (@Term.var L))) zs us)
        t := by
  induction t with
  | var x => rfl
  | const c =>
      rw [termSubstTermsList_const, termSubstTermsList_const]
      rfl
  | func f args ih =>
      rw [termSubstTermsList_func, termSubstTermsList_func]
      simp only [termMapVars]
      congr 1
      funext i
      exact ih i

private theorem termSubstTermsList_twoStage_var_at {L : Language}
    (xs zs : List Nat) (us : List (Term L)) (i : Nat)
    (hi : i < xs.length)
    (hXZ : xs.length = zs.length)
    (hZU : zs.length = us.length)
    (hXs : xs.Nodup) (hZs : zs.Nodup)
    (hDisjoint : ∀ z ∈ zs, z ∉ xs)
    (hAvoid : ∀ u ∈ us, ∀ z ∈ zs, z ∉ termFV u) :
    termSubstTermsList
        (termSubstTermsList (.var xs[i]) xs
          (zs.map (@Term.var L))) zs us =
      us[i]'(by omega) := by
  have hiZ : i < zs.length := by omega
  have hiU : i < us.length := by omega
  have hiZip₁ :
      i < (xs.zip (zs.map (@Term.var L))).length := by
    simp only [List.length_zip, List.length_map]
    omega
  have hPair₁ :=
    List.getElem_mem
      (l := xs.zip (zs.map (@Term.var L))) hiZip₁
  rw [List.getElem_zip] at hPair₁
  simp only [List.getElem_map] at hPair₁
  have hAvoid₁ :
      ∀ u ∈ zs.map (@Term.var L), ∀ y ∈ xs,
        y ∉ termFV u := by
    intro u hu y hy
    rw [List.mem_map] at hu
    obtain ⟨z, hz, rfl⟩ := hu
    intro hyz
    change y = z at hyz
    subst y
    exact hDisjoint z hz hy
  have hFirst :
      termSubstTermsList (.var xs[i]) xs
          (zs.map (@Term.var L)) =
        .var zs[i] := by
    exact termSubstTermsList_var_of_zip_mem
      xs (zs.map (@Term.var L)) xs[i] (.var zs[i])
      hXs hAvoid₁ hPair₁
  rw [hFirst]
  have hiZip₂ : i < (zs.zip us).length := by
    simp only [List.length_zip]
    omega
  have hPair₂ := List.getElem_mem (l := zs.zip us) hiZip₂
  rw [List.getElem_zip] at hPair₂
  exact termSubstTermsList_var_of_zip_mem
    zs us zs[i] us[i] hZs hAvoid hPair₂

theorem captureSafeSubst_var_at {L : Language}
    (A : FormulaN L) (vars : List Nat) (us : List (Term L))
    (hLen : vars.length = us.length) (hVars : vars.Nodup)
    (i : Nat) (hi : i < vars.length) :
    let fresh := captureSafeFreshVars A vars us
    termSubstTermsList
        (termSubstTermsList (.var vars[i]) vars
          (fresh.map (@Term.var L))) fresh us =
      us[i]'(by omega) := by
  intro fresh
  apply termSubstTermsList_twoStage_var_at
      vars fresh us i hi
      (by simp [fresh, captureSafeFreshVars]) (by
        simp [fresh, captureSafeFreshVars]
        omega)
      hVars (captureSafeFreshVars_nodup A vars us)
  · intro z hz hzVars
    exact (Nat.lt_irrefl z)
      ((captureSafeFreshVars_gt A vars us z hz).2.1 z hzVars)
  · intro u hu z hz
    exact termFV_gt_maxVar u z
      ((captureSafeFreshVars_gt A vars us z hz).2.2 u hu)

private theorem formulaSubstVars_eq_terms {L : Language}
    (A : FormulaN L) (xs zs : List Nat) :
    formulaSubstVars A xs zs =
      formulaSubstTerms A xs (zs.map (@Term.var L)) := by
  induction xs generalizing A zs with
  | nil => rfl
  | cons x xs ih =>
      cases zs with
      | nil => rfl
      | cons z zs =>
          simp only [formulaSubstVars, formulaSubstTerms, List.map_cons]
          exact ih _ _

private theorem formulaSubstTerms_predN {L : Language}
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L)
    (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.predN P args) xs us =
      FormulaN.predN P
        (fun i => termSubstTermsList (args i) xs us) := by
  induction xs generalizing args us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]
          rfl

private theorem formulaSubstTerms_eq {L : Language}
    (hL : L.hasEquality = true) (s t : Term L)
    (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.eq_ hL s t) xs us =
      FormulaN.eq_ hL
        (termSubstTermsList s xs us)
        (termSubstTermsList t xs us) := by
  induction xs generalizing s t us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]
          rfl

private theorem formulaSubstTerms_neg {L : Language}
    (A : FormulaN L) (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.neg A) xs us =
      FormulaN.neg (formulaSubstTerms A xs us) := by
  induction xs generalizing A us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]

private theorem formulaSubstTerms_conj {L : Language}
    (A B : FormulaN L) (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.conj A B) xs us =
      FormulaN.conj
        (formulaSubstTerms A xs us)
        (formulaSubstTerms B xs us) := by
  induction xs generalizing A B us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]

private theorem formulaSubstTerms_disj {L : Language}
    (A B : FormulaN L) (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.disj A B) xs us =
      FormulaN.disj
        (formulaSubstTerms A xs us)
        (formulaSubstTerms B xs us) := by
  induction xs generalizing A B us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]

private theorem formulaSubstTerms_impl {L : Language}
    (A B : FormulaN L) (xs : List Nat) (us : List (Term L)) :
    formulaSubstTerms (FormulaN.impl A B) xs us =
      FormulaN.impl
        (formulaSubstTerms A xs us)
        (formulaSubstTerms B xs us) := by
  induction xs generalizing A B us with
  | nil => rfl
  | cons x xs ih =>
      cases us with
      | nil => rfl
      | cons u us =>
          simp only [formulaSubstTerms, formulaSubstN]
          rw [ih]

def formulaMapVars {L : Language}
    (σ : Nat → Term L) : FormulaN L → FormulaN L
  | .predN P args => .predN P (fun i => termMapVars σ (args i))
  | .eq_ hL s t => .eq_ hL (termMapVars σ s) (termMapVars σ t)
  | .neg A => .neg (formulaMapVars σ A)
  | .conj A B => .conj (formulaMapVars σ A) (formulaMapVars σ B)
  | .disj A B => .disj (formulaMapVars σ A) (formulaMapVars σ B)
  | .impl A B => .impl (formulaMapVars σ A) (formulaMapVars σ B)
  | .all x A => .all x (formulaMapVars σ A)
  | .ex x A => .ex x (formulaMapVars σ A)

private theorem union_eq_empty_left {α : Type} (s t : Set α)
    (h : s ∪ t = ∅) : s = ∅ := by
  ext x
  constructor
  · intro hx
    have : x ∈ s ∪ t := Or.inl hx
    rw [h] at this
    exact this.elim
  · intro hx
    exact hx.elim

private theorem union_eq_empty_right {α : Type} (s t : Set α)
    (h : s ∪ t = ∅) : t = ∅ := by
  ext x
  constructor
  · intro hx
    have : x ∈ s ∪ t := Or.inr hx
    rw [h] at this
    exact this.elim
  · intro hx
    exact hx.elim

theorem formulaSubstTerms_twoStage {L : Language}
    (A : FormulaN L) (xs zs : List Nat) (us : List (Term L))
    (hOpen : formulaBVN A = ∅) :
    formulaSubstTerms (formulaSubstVars A xs zs) zs us =
      formulaMapVars
        (fun x => termSubstTermsList
          (termSubstTermsList (.var x) xs (zs.map (@Term.var L))) zs us)
        A := by
  rw [formulaSubstVars_eq_terms]
  induction A with
  | predN P args =>
      rw [formulaSubstTerms_predN, formulaSubstTerms_predN]
      simp only [formulaMapVars]
      congr 1
      funext i
      exact termSubstTermsList_twoStage (args i) xs zs us
  | eq_ hEq s t =>
      rw [formulaSubstTerms_eq, formulaSubstTerms_eq]
      simp only [formulaMapVars]
      congr 1
      · exact termSubstTermsList_twoStage s xs zs us
      · exact termSubstTermsList_twoStage t xs zs us
  | neg A ih =>
      rw [formulaSubstTerms_neg, formulaSubstTerms_neg]
      simp only [formulaMapVars]
      exact congrArg FormulaN.neg (ih hOpen)
  | conj A B ihA ihB =>
      rw [formulaSubstTerms_conj, formulaSubstTerms_conj]
      simp only [formulaMapVars]
      exact congr
        (congrArg FormulaN.conj
          (ihA (union_eq_empty_left _ _ hOpen)))
        (ihB (union_eq_empty_right _ _ hOpen))
  | disj A B ihA ihB =>
      rw [formulaSubstTerms_disj, formulaSubstTerms_disj]
      simp only [formulaMapVars]
      exact congr
        (congrArg FormulaN.disj
          (ihA (union_eq_empty_left _ _ hOpen)))
        (ihB (union_eq_empty_right _ _ hOpen))
  | impl A B ihA ihB =>
      rw [formulaSubstTerms_impl, formulaSubstTerms_impl]
      simp only [formulaMapVars]
      exact congr
        (congrArg FormulaN.impl
          (ihA (union_eq_empty_left _ _ hOpen)))
        (ihB (union_eq_empty_right _ _ hOpen))
  | all x A ih =>
      exfalso
      change formulaBVN A ∪ Set.singleton x = ∅ at hOpen
      have hx : x ∈ formulaBVN A ∪ Set.singleton x := Or.inr rfl
      rw [hOpen] at hx
      exact hx
  | ex x A ih =>
      exfalso
      change formulaBVN A ∪ Set.singleton x = ∅ at hOpen
      have hx : x ∈ formulaBVN A ∪ Set.singleton x := Or.inr rfl
      rw [hOpen] at hx
      exact hx

end LCS.CutElim.Interpolation.Equality
end

