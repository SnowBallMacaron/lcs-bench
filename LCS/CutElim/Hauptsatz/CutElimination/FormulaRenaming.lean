import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Rename occurrences of `v` while they are in the scope of a quantifier
binding `v`.  The Boolean records whether the traversal is below such a
quantifier.  Free occurrences encountered from the top level are therefore
left unchanged. -/
def alphaRenameBoundAux {L : Language} (v z : Nat) :
    Bool → FormulaN L → FormulaN L
  | active, .predN P ts =>
      if active then
        .predN P (fun i => termSubst (ts i) (.var z) v)
      else
        .predN P ts
  | active, .eq_ hL t₁ t₂ =>
      if active then
        .eq_ hL (termSubst t₁ (.var z) v) (termSubst t₂ (.var z) v)
      else
        .eq_ hL t₁ t₂
  | active, .neg A => .neg (alphaRenameBoundAux v z active A)
  | active, .conj A B =>
      .conj (alphaRenameBoundAux v z active A)
        (alphaRenameBoundAux v z active B)
  | active, .disj A B =>
      .disj (alphaRenameBoundAux v z active A)
        (alphaRenameBoundAux v z active B)
  | active, .impl A B =>
      .impl (alphaRenameBoundAux v z active A)
        (alphaRenameBoundAux v z active B)
  | active, .all x A =>
      if x = v then
        .all z (alphaRenameBoundAux v z true A)
      else
        .all x (alphaRenameBoundAux v z active A)
  | active, .ex x A =>
      if x = v then
        .ex z (alphaRenameBoundAux v z true A)
      else
        .ex x (alphaRenameBoundAux v z active A)

/-- Selectively alpha-rename every binder labelled `v`, without changing
free occurrences of `v`. -/
def alphaRenameBound {L : Language}
    (A : FormulaN L) (v z : Nat) : FormulaN L :=
  alphaRenameBoundAux v z false A

/-- The body traversal used after changing an individual rule binder. -/
def alphaRenameBinderBody {L : Language}
    (A : FormulaN L) (x v z : Nat) : FormulaN L :=
  if x = v then
    alphaRenameBoundAux v z true A
  else
    alphaRenameBoundAux v z false A

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The corresponding change of a quantifier's binder label. -/
def alphaRenameBinderIndex (x v z : Nat) : Nat :=
  if x = v then z else x

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Pointwise selective alpha-renaming on a finite sequent side. -/
noncomputable def alphaRenameFormulaFinset {L : Language}
    (S : LCS.Finset (FormulaN L)) (v z : Nat) :
    LCS.Finset (FormulaN L) :=
  LCS.Finset.image (fun A => alphaRenameBound A v z) S

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameBound_all {L : Language}
    (x v z : Nat) (A : FormulaN L) :
    alphaRenameBound (.all x A) v z =
      .all (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) := by
  by_cases hxv : x = v
  · simp [alphaRenameBound, alphaRenameBoundAux,
      alphaRenameBinderIndex, alphaRenameBinderBody, hxv]
  · simp [alphaRenameBound, alphaRenameBoundAux,
      alphaRenameBinderIndex, alphaRenameBinderBody, hxv]

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameBound_ex {L : Language}
    (x v z : Nat) (A : FormulaN L) :
    alphaRenameBound (.ex x A) v z =
      .ex (alphaRenameBinderIndex x v z)
        (alphaRenameBinderBody A x v z) := by
  by_cases hxv : x = v
  · simp [alphaRenameBound, alphaRenameBoundAux,
      alphaRenameBinderIndex, alphaRenameBinderBody, hxv]
  · simp [alphaRenameBound, alphaRenameBoundAux,
      alphaRenameBinderIndex, alphaRenameBinderBody, hxv]

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameFormulaFinset_insert {L : Language}
    (A : FormulaN L) (S : LCS.Finset (FormulaN L)) (v z : Nat) :
    alphaRenameFormulaFinset (LCS.Finset.insert A S) v z =
      LCS.Finset.insert (alphaRenameBound A v z)
        (alphaRenameFormulaFinset S v z) := by
  exact LCS.Finset.image_insert _ A S

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameFormulaFinset_union {L : Language}
    (S₁ S₂ : LCS.Finset (FormulaN L)) (v z : Nat) :
    alphaRenameFormulaFinset (LCS.Finset.union S₁ S₂) v z =
      LCS.Finset.union
        (alphaRenameFormulaFinset S₁ v z)
        (alphaRenameFormulaFinset S₂ v z) := by
  apply LCS.Finset.ext
  intro A
  simp only [alphaRenameFormulaFinset, LCS.Finset.mem_image,
    LCS.Finset.mem_union]
  constructor
  · rintro ⟨B, hB | hB, rfl⟩
    · exact Or.inl ⟨B, hB, rfl⟩
    · exact Or.inr ⟨B, hB, rfl⟩
  · rintro (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
    · exact ⟨B, Or.inl hB, rfl⟩
    · exact ⟨B, Or.inr hB, rfl⟩

theorem alphaRenameBoundAux_isNNF {L : Language}
    (A : FormulaN L) (v z : Nat) (active : Bool)
    (hNNF : A.isNNF) :
    (alphaRenameBoundAux v z active A).isNNF := by
  induction A generalizing active with
  | predN P ts =>
      cases active <;> simp [alphaRenameBoundAux, FormulaN.isNNF]
  | eq_ hL t₁ t₂ =>
      cases active <;> simp [alphaRenameBoundAux, FormulaN.isNNF]
  | neg A ih =>
      cases A with
      | predN P ts =>
          cases active <;> simp [alphaRenameBoundAux, FormulaN.isNNF]
      | eq_ hL t₁ t₂ =>
          cases active <;> simp [alphaRenameBoundAux, FormulaN.isNNF]
      | neg A =>
          simp [FormulaN.isNNF] at hNNF
      | conj A B =>
          simp [FormulaN.isNNF] at hNNF
      | disj A B =>
          simp [FormulaN.isNNF] at hNNF
      | impl A B =>
          simp [FormulaN.isNNF] at hNNF
      | all x A =>
          simp [FormulaN.isNNF] at hNNF
      | ex x A =>
          simp [FormulaN.isNNF] at hNNF
  | conj A B ihA ihB =>
      exact ⟨ihA active hNNF.1, ihB active hNNF.2⟩
  | disj A B ihA ihB =>
      exact ⟨ihA active hNNF.1, ihB active hNNF.2⟩
  | impl A B ihA ihB =>
      simp [FormulaN.isNNF] at hNNF
  | all x A ih =>
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, FormulaN.isNNF]
        exact ih true hNNF
      · simp only [if_neg hxv, FormulaN.isNNF]
        exact ih active hNNF
  | ex x A ih =>
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, FormulaN.isNNF]
        exact ih true hNNF
      · simp only [if_neg hxv, FormulaN.isNNF]
        exact ih active hNNF

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameFormulaFinset_isNNF {L : Language}
    (S : LCS.Finset (FormulaN L)) (v z : Nat)
    (hNNF : ∀ A ∈ S, A.isNNF) :
    ∀ A ∈ alphaRenameFormulaFinset S v z, A.isNNF := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := LCS.Finset.mem_image.mp hA
  exact alphaRenameBoundAux_isNNF B v z false (hNNF B hB)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameBound_isAtomic {L : Language}
    (A : FormulaN L) (v z : Nat) (hAtom : A.isAtomic = true) :
    (alphaRenameBound A v z).isAtomic = true := by
  cases A <;>
    simp [FormulaN.isAtomic, alphaRenameBound,
      alphaRenameBoundAux] at hAtom ⊢

theorem alphaRenameBoundAux_degree {L : Language}
    (A : FormulaN L) (v z : Nat) (active : Bool) :
    (alphaRenameBoundAux v z active A).degree = A.degree := by
  induction A generalizing active with
  | predN P ts =>
      cases active <;> simp [alphaRenameBoundAux, FormulaN.degree]
  | eq_ hL t₁ t₂ =>
      cases active <;> simp [alphaRenameBoundAux, FormulaN.degree]
  | neg A ih =>
      cases active <;> cases A <;>
        simp [alphaRenameBoundAux, FormulaN.degree] <;>
        split <;> rfl
  | conj A B ihA ihB =>
      simp [alphaRenameBoundAux, FormulaN.degree, ihA, ihB]
  | disj A B ihA ihB =>
      simp [alphaRenameBoundAux, FormulaN.degree, ihA, ihB]
  | impl A B ihA ihB =>
      simp [alphaRenameBoundAux, FormulaN.degree]
  | all x A ih =>
      simp only [alphaRenameBoundAux]
      split <;> simp [FormulaN.degree, ih]
  | ex x A ih =>
      simp only [alphaRenameBoundAux]
      split <;> simp [FormulaN.degree, ih]

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
theorem alphaRenameBound_degree {L : Language}
    (A : FormulaN L) (v z : Nat) :
    (alphaRenameBound A v z).degree = A.degree :=
  alphaRenameBoundAux_degree A v z false

theorem alphaRenameBoundAux_removes_binder {L : Language}
    (A : FormulaN L) (v z : Nat) (active : Bool)
    (hvz : v ≠ z) :
    v ∉ formulaBVN (alphaRenameBoundAux v z active A) := by
  induction A generalizing active with
  | predN P ts =>
      cases active <;> simp only [alphaRenameBoundAux, formulaBVN] <;>
        intro h <;> exact h
  | eq_ hL t₁ t₂ =>
      cases active <;> simp only [alphaRenameBoundAux, formulaBVN] <;>
        intro h <;> exact h
  | neg A ih =>
      simpa [alphaRenameBoundAux, formulaBVN] using ih active
  | conj A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaBVN]
      exact fun h => h.elim (ihA active) (ihB active)
  | disj A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaBVN]
      exact fun h => h.elim (ihA active) (ihB active)
  | impl A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaBVN]
      exact fun h => h.elim (ihA active) (ihB active)
  | all x A ih =>
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaBVN]
        exact fun h => h.elim (ih true) hvz
      · simp only [if_neg hxv, formulaBVN]
        exact fun h => h.elim (ih active) (Ne.symm hxv)
  | ex x A ih =>
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaBVN]
        exact fun h => h.elim (ih true) hvz
      · simp only [if_neg hxv, formulaBVN]
        exact fun h => h.elim (ih active) (Ne.symm hxv)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
theorem alphaRenameBound_removes_binder {L : Language}
    (A : FormulaN L) (v z : Nat) (hvz : v ≠ z) :
    v ∉ formulaBVN (alphaRenameBound A v z) :=
  alphaRenameBoundAux_removes_binder A v z false hvz

theorem alphaRenameBoundAux_preserves_binder_absence
    {L : Language} (A : FormulaN L) (v z w : Nat) (active : Bool)
    (hwz : w ≠ z) (hwA : w ∉ formulaBVN A) :
    w ∉ formulaBVN (alphaRenameBoundAux v z active A) := by
  induction A generalizing active with
  | predN P ts =>
      cases active <;> simp only [alphaRenameBoundAux, formulaBVN] <;>
        intro h <;> exact h
  | eq_ hL t₁ t₂ =>
      cases active <;> simp only [alphaRenameBoundAux, formulaBVN] <;>
        intro h <;> exact h
  | neg A ih =>
      exact ih active hwA
  | conj A B ihA ihB =>
      intro hw
      rcases hw with hw | hw
      · exact ihA active (fun h => hwA (Or.inl h)) hw
      · exact ihB active (fun h => hwA (Or.inr h)) hw
  | disj A B ihA ihB =>
      intro hw
      rcases hw with hw | hw
      · exact ihA active (fun h => hwA (Or.inl h)) hw
      · exact ihB active (fun h => hwA (Or.inr h)) hw
  | impl A B ihA ihB =>
      intro hw
      rcases hw with hw | hw
      · exact ihA active (fun h => hwA (Or.inl h)) hw
      · exact ihB active (fun h => hwA (Or.inr h)) hw
  | all x A ih =>
      have hwBody : w ∉ formulaBVN A :=
        fun h => hwA (Or.inl h)
      have hwx : w ≠ x :=
        fun h => hwA (Or.inr h)
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaBVN]
        exact fun h => h.elim (ih true hwBody) hwz
      · simp only [if_neg hxv, formulaBVN]
        exact fun h => h.elim (ih active hwBody) hwx
  | ex x A ih =>
      have hwBody : w ∉ formulaBVN A :=
        fun h => hwA (Or.inl h)
      have hwx : w ≠ x :=
        fun h => hwA (Or.inr h)
      simp only [alphaRenameBoundAux]
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaBVN]
        exact fun h => h.elim (ih true hwBody) hwz
      · simp only [if_neg hxv, formulaBVN]
        exact fun h => h.elim (ih active hwBody) hwx

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
theorem alphaRenameBound_preserves_binder_absence
    {L : Language} (A : FormulaN L) (v z w : Nat)
    (hwz : w ≠ z) (hwA : w ∉ formulaBVN A) :
    w ∉ formulaBVN (alphaRenameBound A v z) :=
  alphaRenameBoundAux_preserves_binder_absence A v z w false hwz hwA

theorem alphaRenameBound_eq_self_of_not_bound {L : Language}
    (A : FormulaN L) (v z : Nat) (hvA : v ∉ formulaBVN A) :
    alphaRenameBound A v z = A := by
  unfold alphaRenameBound
  induction A with
  | predN P ts => simp [alphaRenameBoundAux]
  | eq_ hL t₁ t₂ => simp [alphaRenameBoundAux]
  | neg A ih =>
      simp only [alphaRenameBoundAux, FormulaN.neg.injEq]
      exact ih hvA
  | conj A B ihA ihB =>
      simp only [alphaRenameBoundAux, FormulaN.conj.injEq]
      exact
        ⟨ihA (fun h => hvA (Or.inl h)),
         ihB (fun h => hvA (Or.inr h))⟩
  | disj A B ihA ihB =>
      simp only [alphaRenameBoundAux, FormulaN.disj.injEq]
      exact
        ⟨ihA (fun h => hvA (Or.inl h)),
         ihB (fun h => hvA (Or.inr h))⟩
  | impl A B ihA ihB =>
      simp only [alphaRenameBoundAux, FormulaN.impl.injEq]
      exact
        ⟨ihA (fun h => hvA (Or.inl h)),
         ihB (fun h => hvA (Or.inr h))⟩
  | all x A ih =>
      have hvx : v ≠ x := fun h => hvA (Or.inr h)
      have hvBody : v ∉ formulaBVN A :=
        fun h => hvA (Or.inl h)
      simp only [alphaRenameBoundAux, if_neg (Ne.symm hvx)]
      exact congrArg (FormulaN.all x) (ih hvBody)
  | ex x A ih =>
      have hvx : v ≠ x := fun h => hvA (Or.inr h)
      have hvBody : v ∉ formulaBVN A :=
        fun h => hvA (Or.inl h)
      simp only [alphaRenameBoundAux, if_neg (Ne.symm hvx)]
      exact congrArg (FormulaN.ex x) (ih hvBody)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
theorem alphaRenameFormulaFinset_eq_self_of_not_bound
    {L : Language} (S : LCS.Finset (FormulaN L)) (v z : Nat)
    (hS : ∀ A ∈ S, v ∉ formulaBVN A) :
    alphaRenameFormulaFinset S v z = S := by
  apply LCS.Finset.ext
  intro A
  rw [alphaRenameFormulaFinset, LCS.Finset.mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa [alphaRenameBound_eq_self_of_not_bound B v z (hS B hB)]
      using hB
  · intro hA
    exact ⟨A, hA, alphaRenameBound_eq_self_of_not_bound A v z
      (hS A hA)⟩

/-- Free-variable flow for the scope-aware traversal.  In inactive mode
no new free variable is introduced.  In active mode an occurrence of `v`
can only become `z`; every other output variable came from the same input
variable. -/
theorem alphaRenameBoundAux_freeVariable {L : Language}
    (A : FormulaN L) (v z w : Nat) (active : Bool)
    (hw : w ∈ formulaFVN (alphaRenameBoundAux v z active A)) :
    if active then
      (w ∈ formulaFVN A ∧ w ≠ v) ∨ w = z
    else
      w ∈ formulaFVN A := by
  induction A generalizing active w with
  | predN P ts =>
      cases active with
      | false =>
          simpa [alphaRenameBoundAux] using hw
      | true =>
          have hw' :
              w ∈ formulaFVN
                (formulaSubstN (.predN P ts) (.var z) v) := by
            simpa [alphaRenameBoundAux, formulaSubstN] using hw
          rcases
              LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
                (.predN P ts) (.var z) v w hw' with
            ⟨hwA, hwv⟩ | hwz
          · exact Or.inl ⟨hwA, hwv⟩
          · change w = z at hwz
            exact Or.inr hwz
  | eq_ hL t₁ t₂ =>
      cases active with
      | false =>
          simpa [alphaRenameBoundAux] using hw
      | true =>
          have hw' :
              w ∈ formulaFVN
                (formulaSubstN (.eq_ hL t₁ t₂) (.var z) v) := by
            simpa [alphaRenameBoundAux, formulaSubstN] using hw
          rcases
              LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
                (.eq_ hL t₁ t₂) (.var z) v w hw' with
            ⟨hwA, hwv⟩ | hwz
          · exact Or.inl ⟨hwA, hwv⟩
          · change w = z at hwz
            exact Or.inr hwz
  | neg A ih =>
      simp only [alphaRenameBoundAux, formulaFVN] at hw
      simpa only [formulaFVN] using ih w active hw
  | conj A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaFVN] at hw
      cases active with
      | false =>
          exact hw.elim
            (fun h => Or.inl (ihA w false h))
            (fun h => Or.inr (ihB w false h))
      | true =>
          rcases hw with hw | hw
          · rcases ihA w true hw with h | h
            · exact Or.inl ⟨Or.inl h.1, h.2⟩
            · exact Or.inr h
          · rcases ihB w true hw with h | h
            · exact Or.inl ⟨Or.inr h.1, h.2⟩
            · exact Or.inr h
  | disj A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaFVN] at hw
      cases active with
      | false =>
          exact hw.elim
            (fun h => Or.inl (ihA w false h))
            (fun h => Or.inr (ihB w false h))
      | true =>
          rcases hw with hw | hw
          · rcases ihA w true hw with h | h
            · exact Or.inl ⟨Or.inl h.1, h.2⟩
            · exact Or.inr h
          · rcases ihB w true hw with h | h
            · exact Or.inl ⟨Or.inr h.1, h.2⟩
            · exact Or.inr h
  | impl A B ihA ihB =>
      simp only [alphaRenameBoundAux, formulaFVN] at hw
      cases active with
      | false =>
          exact hw.elim
            (fun h => Or.inl (ihA w false h))
            (fun h => Or.inr (ihB w false h))
      | true =>
          rcases hw with hw | hw
          · rcases ihA w true hw with h | h
            · exact Or.inl ⟨Or.inl h.1, h.2⟩
            · exact Or.inr h
          · rcases ihB w true hw with h | h
            · exact Or.inl ⟨Or.inr h.1, h.2⟩
            · exact Or.inr h
  | all x A ih =>
      simp only [alphaRenameBoundAux] at hw
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaFVN] at hw
        rcases ih w true hw.1 with h | h
        · have hOut :
              w ∈ formulaFVN (.all v A) :=
            ⟨h.1, h.2⟩
          cases active <;> simp_all [formulaFVN]
        · exact absurd h hw.2
      · simp only [if_neg hxv, formulaFVN] at hw
        cases active with
        | false =>
            exact ⟨ih w false hw.1, hw.2⟩
        | true =>
            rcases ih w true hw.1 with h | h
            · exact Or.inl ⟨⟨h.1, hw.2⟩, h.2⟩
            · exact Or.inr h
  | ex x A ih =>
      simp only [alphaRenameBoundAux] at hw
      by_cases hxv : x = v
      · simp only [hxv, if_pos, formulaFVN] at hw
        rcases ih w true hw.1 with h | h
        · have hOut :
              w ∈ formulaFVN (.ex v A) :=
            ⟨h.1, h.2⟩
          cases active <;> simp_all [formulaFVN]
        · exact absurd h hw.2
      · simp only [if_neg hxv, formulaFVN] at hw
        cases active with
        | false =>
            exact ⟨ih w false hw.1, hw.2⟩
        | true =>
            rcases ih w true hw.1 with h | h
            · exact Or.inl ⟨⟨h.1, hw.2⟩, h.2⟩
            · exact Or.inr h

theorem alphaRenameBound_freeVariable {L : Language}
    (A : FormulaN L) (v z w : Nat)
    (hw : w ∈ formulaFVN (alphaRenameBound A v z)) :
    w ∈ formulaFVN A := by
  exact alphaRenameBoundAux_freeVariable A v z w false hw

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameBound_preserves_freeVariable_absence
    {L : Language} (A : FormulaN L) (v z w : Nat)
    (hwA : w ∉ formulaFVN A) :
    w ∉ formulaFVN (alphaRenameBound A v z) :=
  fun hw => hwA (alphaRenameBound_freeVariable A v z w hw)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem alphaRenameFormulaFinset_preserves_freshness
    {L : Language} (S : LCS.Finset (FormulaN L)) (v z w : Nat)
    (hS : ∀ A ∈ S, w ∉ formulaFVN A) :
    ∀ A ∈ alphaRenameFormulaFinset S v z, w ∉ formulaFVN A := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := LCS.Finset.mem_image.mp hA
  exact alphaRenameBound_preserves_freeVariable_absence
    B v z w (hS B hB)

end LCS.CutElim.Hauptsatz
end
