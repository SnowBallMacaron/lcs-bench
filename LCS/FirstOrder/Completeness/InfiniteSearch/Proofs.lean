import LCS.FirstOrder.Completeness.InfiniteSearch

namespace LCS.FirstOrder.Completeness.InfiniteSearch

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness

open Classical

helper /-- Theorem 5.5.1 (required helper): Every axiom sequent is G-provable
(under the §5.4.8 standing assumption, via `GProofTreeExt.axiom_`). -/
theorem isAxiom_implies_provable {L : Language} (seq : Sequent L)
    (h : isAxiom seq) : sequentProvableExt seq :=
-- BEGIN PROOF
  ⟨GProofTreeExt.axiom_ seq h⟩

helper /-- Even-index renaming preserves and reflects satisfiability. -/
theorem satisfiableSetN_iff_evenSet {L : Language} (Gamma : Set (FormulaN L)) :
    satisfiableSetN Gamma ↔ satisfiableSetN (evenSet Gamma) := by
  constructor
  · rintro ⟨M, s, hs⟩
    obtain ⟨t, ht⟩ := (satisfiableSetInN_iff_evenSet M Gamma).mp ⟨s, hs⟩
    exact ⟨M, t, ht⟩
  · rintro ⟨M, s, hs⟩
    obtain ⟨t, ht⟩ := (satisfiableSetInN_iff_evenSet M Gamma).mpr ⟨s, hs⟩
    exact ⟨M, t, ht⟩

helper /-- Theorem 5.5.1 (required helper): closureStep1 antecedent
monotonicity -- formulas in prev.antecedent persist. -/
theorem closureStep1_ant_mono {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (A : FormulaN L) :
    A ∈ prev.antecedent → A ∈ (closureStep1 prev t_c t_d).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [closureStep1]
  exact List.mem_append_left _ (List.mem_append_left _ hA)

helper /-- Theorem 5.5.1 (required helper): closureStep1 succedent
monotonicity -- formulas in prev.succedent persist. -/
theorem closureStep1_succ_mono {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (B : FormulaN L) :
    B ∈ prev.succedent → B ∈ (closureStep1 prev t_c t_d).succedent := by
-- BEGIN PROOF
  intro hB; simp only [closureStep1]
  exact List.mem_append_left _ (List.mem_append_left _ hB)

helper /-- Theorem 5.5.1 (required helper): closureStep antecedent
monotonicity -- formulas in prev.antecedent persist through a list
of decomposition steps. -/
theorem closureStep_ant_mono {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L) (A : FormulaN L) :
    A ∈ prev.antecedent → A ∈ (closureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact hA
  | cons t ts ih =>
    simp [List.foldl]
    exact ih (closureStep1 prev t t_d) (closureStep1_ant_mono prev t t_d A hA)

helper /-- Theorem 5.5.1 (required helper): closureStep succedent
monotonicity -- formulas in prev.succedent persist through a list
of decomposition steps. -/
theorem closureStep_succ_mono {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L) (B : FormulaN L) :
    B ∈ prev.succedent → B ∈ (closureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro hB; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact hB
  | cons t ts ih =>
    simp [List.foldl]
    exact ih (closureStep1 prev t t_d) (closureStep1_succ_mono prev t t_d B hB)

helper /-- Theorem 5.5.1 (required helper): Antecedent monotonicity --
formulas at level n persist at level n+1. -/
theorem growingClosure_ant_mono {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (n : Nat) (A : FormulaN L) :
    A ∈ (growingClosure Gamma n).antecedent →
    A ∈ (growingClosure Gamma (n + 1)).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [growingClosure]
  have hCS := closureStep_ant_mono (growingClosure Gamma n)
    ((List.range (n + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (n + 1)) A hA
  split
  · exact List.mem_append_left _ hCS
  · exact hCS

helper /-- Theorem 5.5.1 (required helper): Succedent monotonicity --
formulas at level n persist at level n+1. -/
theorem growingClosure_succ_mono {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (n : Nat) (B : FormulaN L) :
    B ∈ (growingClosure Gamma n).succedent →
    B ∈ (growingClosure Gamma (n + 1)).succedent := by
-- BEGIN PROOF
  intro hB; simp only [growingClosure]
  have hCS := closureStep_succ_mono (growingClosure Gamma n)
    ((List.range (n + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (n + 1)) B hB
  split <;> exact hCS

helper /-- Theorem 5.5.1 (required helper): Extended antecedent monotonicity
-- formulas at level n persist at level m >= n. -/
theorem growingClosure_ant_mono_le {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) {n m : Nat} (h : n ≤ m) (A : FormulaN L) :
    A ∈ (growingClosure Gamma n).antecedent →
    A ∈ (growingClosure Gamma m).antecedent := by
-- BEGIN PROOF
  induction h with
  | refl => exact fun hA => hA
  | step _ ih => exact fun hA => growingClosure_ant_mono Gamma _ A (ih hA)

helper /-- Theorem 5.5.1 (required helper): Extended succedent monotonicity
-- formulas at level n persist at level m >= n. -/
theorem growingClosure_succ_mono_le {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) {n m : Nat} (h : n ≤ m) (B : FormulaN L) :
    B ∈ (growingClosure Gamma n).succedent →
    B ∈ (growingClosure Gamma m).succedent := by
-- BEGIN PROOF
  induction h with
  | refl => exact fun hB => hB
  | step _ ih => exact fun hB => growingClosure_succ_mono Gamma _ B (ih hB)





helper /-- Theorem 5.5.1 (required helper): enumerate m is in the terms
list for the (k+1)-th step when m <= k. -/
theorem enum_in_terms {L : Language} [Countable (Term L)]
    (k m : Nat) (hm : m ≤ k) :
    (Countable.enumerate m : Term L) ∈
      (List.range (k + 2)).map (Countable.enumerate (α := Term L)) := by
-- BEGIN PROOF
  apply List.mem_map_of_mem
  exact List.mem_range.mpr (by omega)

helper /-- Theorem 5.5.1 (required helper): closureStep includes antecedent
formula decompositions in the resulting antecedent. -/
theorem closureStep_decompAnt_ant {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decompAntGrowing A t_c t_d).1,
      X ∈ (closureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro X hX; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (closureStep1 prev t_c t_d).antecedent := by
        simp only [closureStep1]
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨A, hA, hX⟩
      exact closureStep_ant_mono _ tl t_d X hX1
    · exact ih (closureStep1 prev hd t_d) (closureStep1_ant_mono prev hd t_d A hA) htl

helper /-- Theorem 5.5.1 (required helper): closureStep transfers antecedent
decomposition's succedent component to the resulting succedent. -/
theorem closureStep_decompAnt_succ {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decompAntGrowing A t_c t_d).2,
      X ∈ (closureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro X hX; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (closureStep1 prev t_c t_d).succedent := by
        simp only [closureStep1]
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨A, hA, hX⟩
      exact closureStep_succ_mono _ tl t_d X hX1
    · exact ih (closureStep1 prev hd t_d) (closureStep1_ant_mono prev hd t_d A hA) htl

helper /-- Theorem 5.5.1 (required helper): closureStep includes succedent
formula decompositions in the resulting succedent. -/
theorem closureStep_decompSucc_succ {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decompSuccGrowing B t_c t_d).2,
      X ∈ (closureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro X hX; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (closureStep1 prev t_c t_d).succedent := by
        simp only [closureStep1]
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨B, hB, hX⟩
      exact closureStep_succ_mono _ tl t_d X hX1
    · exact ih (closureStep1 prev hd t_d) (closureStep1_succ_mono prev hd t_d B hB) htl

helper /-- Theorem 5.5.1 (required helper): closureStep transfers succedent
decomposition's antecedent component to the resulting antecedent. -/
theorem closureStep_decompSucc_ant {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decompSuccGrowing B t_c t_d).1,
      X ∈ (closureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro X hX; simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (closureStep1 prev t_c t_d).antecedent := by
        simp only [closureStep1]
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨B, hB, hX⟩
      exact closureStep_ant_mono _ tl t_d X hX1
    · exact ih (closureStep1 prev hd t_d) (closureStep1_succ_mono prev hd t_d B hB) htl

helper /-- Theorem 5.5.1 (required helper): Decomposition of antecedent
formula appears in next level's antecedent. -/
theorem decompAnt_in_next_ant {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (A : FormulaN L)
    (hA : A ∈ (growingClosure Gamma k).antecedent)
    (m : Nat) (hm : m ≤ k) :
    ∀ X ∈ (decompAntGrowing A (Countable.enumerate m) (Term.var (k + 1))).1,
      X ∈ (growingClosure Gamma (k + 1)).antecedent := by
-- BEGIN PROOF
  intro X hX
  simp only [growingClosure]
  have ht : (Countable.enumerate m : Term L) ∈
      (List.range (k + 2)).map (Countable.enumerate (α := Term L)) :=
    enum_in_terms (L := L) k m hm
  have hCS := closureStep_decompAnt_ant (growingClosure Gamma k)
    ((List.range (k + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (k + 1)) A (Countable.enumerate m) hA ht X hX
  split
  · exact List.mem_append_left _ hCS
  · exact hCS

helper /-- Theorem 5.5.1 (required helper): Decomposition of antecedent
formula's succedent component appears in next level's succedent. -/
theorem decompAnt_in_next_succ {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (A : FormulaN L)
    (hA : A ∈ (growingClosure Gamma k).antecedent)
    (m : Nat) (hm : m ≤ k) :
    ∀ X ∈ (decompAntGrowing A (Countable.enumerate m) (Term.var (k + 1))).2,
      X ∈ (growingClosure Gamma (k + 1)).succedent := by
-- BEGIN PROOF
  intro X hX
  simp only [growingClosure]
  have ht : (Countable.enumerate m : Term L) ∈
      (List.range (k + 2)).map (Countable.enumerate (α := Term L)) :=
    enum_in_terms (L := L) k m hm
  have hCS := closureStep_decompAnt_succ (growingClosure Gamma k)
    ((List.range (k + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (k + 1)) A (Countable.enumerate m) hA ht X hX
  split <;> exact hCS

helper /-- Theorem 5.5.1 (required helper): Decomposition of succedent
formula appears in next level's succedent. -/
theorem decompSucc_in_next_succ {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (B : FormulaN L)
    (hB : B ∈ (growingClosure Gamma k).succedent)
    (m : Nat) (hm : m ≤ k) :
    ∀ X ∈ (decompSuccGrowing B (Countable.enumerate m) (Term.var (k + 1))).2,
      X ∈ (growingClosure Gamma (k + 1)).succedent := by
-- BEGIN PROOF
  intro X hX
  simp only [growingClosure]
  have ht : (Countable.enumerate m : Term L) ∈
      (List.range (k + 2)).map (Countable.enumerate (α := Term L)) :=
    enum_in_terms (L := L) k m hm
  have hCS := closureStep_decompSucc_succ (growingClosure Gamma k)
    ((List.range (k + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (k + 1)) B (Countable.enumerate m) hB ht X hX
  split <;> exact hCS

helper /-- Theorem 5.5.1 (required helper): Decomposition of succedent
formula's antecedent component appears in next level's antecedent. -/
theorem decompSucc_in_next_ant {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (B : FormulaN L)
    (hB : B ∈ (growingClosure Gamma k).succedent)
    (m : Nat) (hm : m ≤ k) :
    ∀ X ∈ (decompSuccGrowing B (Countable.enumerate m) (Term.var (k + 1))).1,
      X ∈ (growingClosure Gamma (k + 1)).antecedent := by
-- BEGIN PROOF
  intro X hX
  simp only [growingClosure]
  have ht : (Countable.enumerate m : Term L) ∈
      (List.range (k + 2)).map (Countable.enumerate (α := Term L)) :=
    enum_in_terms (L := L) k m hm
  have hCS := closureStep_decompSucc_ant (growingClosure Gamma k)
    ((List.range (k + 2)).map (Countable.enumerate (α := Term L)))
    (Term.var (k + 1)) B (Countable.enumerate m) hB ht X hX
  split
  · exact List.mem_append_left _ hCS
  · exact hCS

helper /-- Theorem 5.5.1 (required helper): Witness that a formula in the
antecedent at level k belongs to the signed limit set as trueF. -/
def inLimitAnt {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (F : FormulaN L)
    (hF : F ∈ (growingClosure Gamma k).antecedent) :
    SignedFormula.trueF F ∈ signedLimitSet Gamma :=
  ⟨k, Or.inl ⟨F, hF, rfl⟩⟩

helper /-- Theorem 5.5.1 (required helper): Witness that a formula in the
succedent at level k belongs to the signed limit set as falseF. -/
def inLimitSucc {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat) (F : FormulaN L)
    (hF : F ∈ (growingClosure Gamma k).succedent) :
    SignedFormula.falseF F ∈ signedLimitSet Gamma :=
  ⟨k, Or.inr ⟨F, hF, rfl⟩⟩

helper /-- Theorem 5.5.1 (required helper): decompAntGrowing preserves
formulaNoEq. -/
theorem decompAntGrowing_noEq {L : Language} (A : FormulaN L) (t_c t_d : Term L)
    (h : formulaNoEq A) :
    (∀ X ∈ (decompAntGrowing A t_c t_d).1, formulaNoEq X) ∧
    (∀ X ∈ (decompAntGrowing A t_c t_d).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => exact ⟨fun _ h' => by simp [decompAntGrowing] at h',
                         fun _ h' => by simp [decompAntGrowing] at h'⟩
  | eq_ _ _ _ => exact h.elim
  | neg X =>
    exact ⟨fun _ h' => by simp [decompAntGrowing] at h',
           fun Z hZ => by simp [decompAntGrowing] at hZ; subst hZ; exact h⟩
  | conj X Y =>
    exact ⟨fun Z hZ => by
             simp [decompAntGrowing] at hZ
             rcases hZ with rfl | rfl
             · exact h.1
             · exact h.2,
           fun _ h' => by simp [decompAntGrowing] at h'⟩
  | disj X Y =>
    exact ⟨fun Z hZ => by
             simp [decompAntGrowing] at hZ
             rcases hZ with rfl | rfl
             · exact h.1
             · exact h.2,
           fun _ h' => by simp [decompAntGrowing] at h'⟩
  | impl X Y =>
    exact ⟨fun Z hZ => by simp [decompAntGrowing] at hZ; subst hZ; exact h.2,
           fun Z hZ => by simp [decompAntGrowing] at hZ; subst hZ; exact h.1⟩
  | all x B =>
    exact ⟨fun Z hZ => by
             simp [decompAntGrowing] at hZ; subst hZ; exact formulaSubstN_noEq B t_c x h,
           fun _ h' => by simp [decompAntGrowing] at h'⟩
  | ex x B =>
    exact ⟨fun Z hZ => by
             simp [decompAntGrowing] at hZ; subst hZ; exact formulaSubstN_noEq B t_d x h,
           fun _ h' => by simp [decompAntGrowing] at h'⟩

helper /-- Theorem 5.5.1 (required helper): decompSuccGrowing preserves
formulaNoEq. -/
theorem decompSuccGrowing_noEq {L : Language} (B : FormulaN L) (t_c t_d : Term L)
    (h : formulaNoEq B) :
    (∀ X ∈ (decompSuccGrowing B t_c t_d).1, formulaNoEq X) ∧
    (∀ X ∈ (decompSuccGrowing B t_c t_d).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases B with
  | predN _ _ => exact ⟨fun _ h' => by simp [decompSuccGrowing] at h',
                         fun _ h' => by simp [decompSuccGrowing] at h'⟩
  | eq_ _ _ _ => exact h.elim
  | neg X =>
    exact ⟨fun Z hZ => by simp [decompSuccGrowing] at hZ; subst hZ; exact h,
           fun _ h' => by simp [decompSuccGrowing] at h'⟩
  | conj X Y =>
    exact ⟨fun _ h' => by simp [decompSuccGrowing] at h',
           fun Z hZ => by
             simp [decompSuccGrowing] at hZ
             rcases hZ with rfl | rfl
             · exact h.1
             · exact h.2⟩
  | disj X Y =>
    exact ⟨fun _ h' => by simp [decompSuccGrowing] at h',
           fun Z hZ => by
             simp [decompSuccGrowing] at hZ
             rcases hZ with rfl | rfl
             · exact h.1
             · exact h.2⟩
  | impl X Y =>
    exact ⟨fun Z hZ => by simp [decompSuccGrowing] at hZ; subst hZ; exact h.1,
           fun Z hZ => by simp [decompSuccGrowing] at hZ; subst hZ; exact h.2⟩
  | ex x A =>
    exact ⟨fun _ h' => by simp [decompSuccGrowing] at h',
           fun Z hZ => by
             simp [decompSuccGrowing] at hZ; subst hZ; exact formulaSubstN_noEq A t_c x h⟩
  | all x A =>
    exact ⟨fun _ h' => by simp [decompSuccGrowing] at h',
           fun Z hZ => by
             simp [decompSuccGrowing] at hZ; subst hZ; exact formulaSubstN_noEq A t_d x h⟩

helper /-- Theorem 5.5.1 (required helper): Characterize antecedent
membership after one closureStep1: either from prev.antecedent,
from an antecedent decomposition, or from a succedent
decomposition. -/
theorem closureStep1N_ant_mem {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (F : FormulaN L)
    (hF : F ∈ (closureStep1 prev t_c t_d).antecedent) :
    F ∈ prev.antecedent ∨
    (∃ A ∈ prev.antecedent, F ∈ (decompAntGrowing A t_c t_d).1) ∨
    (∃ B ∈ prev.succedent, F ∈ (decompSuccGrowing B t_c t_d).1) := by
-- BEGIN PROOF
  unfold closureStep1 at hF
  simp only [List.mem_append] at hF
  rcases hF with ((hF | hF) | hF)
  · exact Or.inl hF
  · exact Or.inr (Or.inl (List.mem_flatMap.mp hF))
  · exact Or.inr (Or.inr (List.mem_flatMap.mp hF))

helper /-- Theorem 5.5.1 (required helper): Characterize succedent
membership after one closureStep1: either from prev.succedent,
from an antecedent decomposition, or from a succedent
decomposition. -/
theorem closureStep1N_succ_mem {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (F : FormulaN L)
    (hF : F ∈ (closureStep1 prev t_c t_d).succedent) :
    F ∈ prev.succedent ∨
    (∃ A ∈ prev.antecedent, F ∈ (decompAntGrowing A t_c t_d).2) ∨
    (∃ B ∈ prev.succedent, F ∈ (decompSuccGrowing B t_c t_d).2) := by
-- BEGIN PROOF
  unfold closureStep1 at hF
  simp only [List.mem_append] at hF
  rcases hF with ((hF | hF) | hF)
  · exact Or.inl hF
  · exact Or.inr (Or.inl (List.mem_flatMap.mp hF))
  · exact Or.inr (Or.inr (List.mem_flatMap.mp hF))

helper /-- Theorem 5.5.1 (required helper): closureStep1 preserves
formulaNoEq for both antecedent and succedent. -/
theorem closureStep1_noEq {L : Language}
    (prev : Sequent L) (t_c t_d : Term L)
    (hAnt : ∀ A ∈ prev.antecedent, formulaNoEq A)
    (hSucc : ∀ B ∈ prev.succedent, formulaNoEq B) :
    (∀ A ∈ (closureStep1 prev t_c t_d).antecedent, formulaNoEq A) ∧
    (∀ B ∈ (closureStep1 prev t_c t_d).succedent, formulaNoEq B) := by
-- BEGIN PROOF
  constructor
  · intro F hF
    rcases closureStep1N_ant_mem prev t_c t_d F hF with h | ⟨A, hA, hFA⟩ | ⟨B, hB, hFB⟩
    · exact hAnt F h
    · exact (decompAntGrowing_noEq A t_c t_d (hAnt A hA)).1 F hFA
    · exact (decompSuccGrowing_noEq B t_c t_d (hSucc B hB)).1 F hFB
  · intro F hF
    rcases closureStep1N_succ_mem prev t_c t_d F hF with h | ⟨A, hA, hFA⟩ | ⟨B, hB, hFB⟩
    · exact hSucc F h
    · exact (decompAntGrowing_noEq A t_c t_d (hAnt A hA)).2 F hFA
    · exact (decompSuccGrowing_noEq B t_c t_d (hSucc B hB)).2 F hFB

helper /-- Theorem 5.5.1 (required helper): closureStep preserves
formulaNoEq for both antecedent and succedent. -/
theorem closureStep_noEq {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (hAnt : ∀ A ∈ prev.antecedent, formulaNoEq A)
    (hSucc : ∀ B ∈ prev.succedent, formulaNoEq B) :
    (∀ A ∈ (closureStep prev terms t_d).antecedent, formulaNoEq A) ∧
    (∀ B ∈ (closureStep prev terms t_d).succedent, formulaNoEq B) := by
-- BEGIN PROOF
  simp only [closureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact ⟨hAnt, hSucc⟩
  | cons t ts ih =>
    simp only [List.foldl]
    have h := closureStep1_noEq prev t t_d hAnt hSucc
    exact ih (closureStep1 prev t t_d) h.1 h.2

helper /-- Theorem 5.5.1 (required helper): growingClosure preserves
formulaNoEq for both antecedent and succedent at all levels. -/
theorem growingClosure_noEq {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A) (n : Nat) :
    (∀ A ∈ (growingClosure Gamma n).antecedent, formulaNoEq A) ∧
    (∀ B ∈ (growingClosure Gamma n).succedent, formulaNoEq B) := by
-- BEGIN PROOF
  induction n with
  | zero =>
    simp only [growingClosure]
    constructor
    · intro A hA
      by_cases hG : Gamma (Countable.enumerate 0)
      · simp [hG] at hA; subst hA; exact hNoEq _ hG
      · simp [hG] at hA
    · intro B hB; simp at hB
  | succ k ih =>
    have hCS := closureStep_noEq (growingClosure Gamma k)
      ((List.range (k + 2)).map (Countable.enumerate (α := Term L)))
      (Term.var (k + 1)) ih.1 ih.2
    constructor
    · intro A hA
      simp only [growingClosure] at hA
      split at hA
      · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hA
        rcases hA with h1 | rfl
        · exact hCS.1 A h1
        · exact hNoEq _ (by assumption)
      · exact hCS.1 A hA
    · intro B hB
      simp only [growingClosure] at hB
      split at hB
      · exact hCS.2 B hB
      · exact hCS.2 B hB

helper /-- Theorem 5.5.1 (companion, limitSet H1): Type-A decomposition — both
components of a type-A formula appear in the signed limit set. -/
theorem limitSet_isHintikka_h1 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) :
    ∀ (a : TypeA L), a.toSigned ∈ signedLimitSet Gamma →
      a.comp1 ∈ signedLimitSet Gamma ∧ a.comp2 ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  intro a ha
  obtain ⟨k, hSf⟩ := ha
  cases a with
  | tConj X Y =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      have hX := decompAnt_in_next_ant Gamma k (.conj X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompAntGrowing])
      have hY := decompAnt_in_next_ant Gamma k (.conj X Y) hF 0 (Nat.zero_le _) Y
        (by simp [decompAntGrowing])
      exact ⟨inLimitAnt Gamma (k + 1) X hX, inLimitAnt Gamma (k + 1) Y hY⟩
    · cases hEq
  | fDisj X Y =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      have hX := decompSucc_in_next_succ Gamma k (.disj X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompSuccGrowing])
      have hY := decompSucc_in_next_succ Gamma k (.disj X Y) hF 0 (Nat.zero_le _) Y
        (by simp [decompSuccGrowing])
      exact ⟨inLimitSucc Gamma (k + 1) X hX, inLimitSucc Gamma (k + 1) Y hY⟩
  | fImpl X Y =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      have hX := decompSucc_in_next_ant Gamma k (.impl X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompSuccGrowing])
      have hY := decompSucc_in_next_succ Gamma k (.impl X Y) hF 0 (Nat.zero_le _) Y
        (by simp [decompSuccGrowing])
      exact ⟨inLimitAnt Gamma (k + 1) X hX, inLimitSucc Gamma (k + 1) Y hY⟩
  | tNeg X =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      have hX := decompAnt_in_next_succ Gamma k (.neg X) hF 0 (Nat.zero_le _) X
        (by simp [decompAntGrowing])
      exact ⟨inLimitSucc Gamma (k + 1) X hX, inLimitSucc Gamma (k + 1) X hX⟩
    · cases hEq
  | fNeg X =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      have hX := decompSucc_in_next_ant Gamma k (.neg X) hF 0 (Nat.zero_le _) X
        (by simp [decompSuccGrowing])
      exact ⟨inLimitAnt Gamma (k + 1) X hX, inLimitAnt Gamma (k + 1) X hX⟩

helper /-- Theorem 5.5.1 (companion, limitSet H2): Type-B decomposition — at
least one component of a type-B formula is in the signed limit set.
With overdecomposition, both components are in the closure. -/
theorem limitSet_isHintikka_h2 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) :
    ∀ (b : TypeB L), b.toSigned ∈ signedLimitSet Gamma →
      b.comp1 ∈ signedLimitSet Gamma ∨ b.comp2 ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  intro b hb
  obtain ⟨k, hSf⟩ := hb
  cases b with
  | fConj X Y =>
    rcases hSf with ⟨_, _, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      have hX := decompSucc_in_next_succ Gamma k (.conj X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompSuccGrowing])
      exact Or.inl (inLimitSucc Gamma (k + 1) X hX)
  | tDisj X Y =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨_, _, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      have hX := decompAnt_in_next_ant Gamma k (.disj X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompAntGrowing])
      exact Or.inl (inLimitAnt Gamma (k + 1) X hX)
    · cases hEq
  | tImpl X Y =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨_, _, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      have hX := decompAnt_in_next_succ Gamma k (.impl X Y) hF 0 (Nat.zero_le _) X
        (by simp [decompAntGrowing])
      exact Or.inl (inLimitSucc Gamma (k + 1) X hX)
    · cases hEq

helper /-- Theorem 5.5.1 (companion, limitSet H3): Type-C universal — for every
term t over the occurrence language that is free for the bound variable,
the C(t) instance is in the signed limit set.
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka_h3 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) :
    ∀ (c : TypeC L), c.toSigned ∈ signedLimitSet Gamma →
      ∀ (t : Term L), (termFunSyms t ⊆ signedSetFunSyms (signedLimitSet Gamma) ∧ termConstSyms t ⊆ signedSetConstSyms (signedLimitSet Gamma)) →
      ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  intro c hc t _ht hfree
  obtain ⟨k, hSf⟩ := hc
  obtain ⟨m, hm⟩ := Countable.enumerate_surj t
  let N := max k m
  cases c with
  | tAll x B =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      have hFN := growingClosure_ant_mono_le Gamma (Nat.le_max_left k m) _ hF
      have hComp := decompAnt_in_next_ant Gamma N (.all x B) hFN m (Nat.le_max_right k m)
        (formulaSubstN B (Countable.enumerate m) x) (by simp [decompAntGrowing])
      exact ⟨N + 1, Or.inl ⟨formulaSubstN B t x, by rw [← hm]; exact hComp,
        by simp [TypeC.comp, ← hm]⟩⟩
    · cases hEq
  | fEx x B =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      have hFN := growingClosure_succ_mono_le Gamma (Nat.le_max_left k m) _ hF
      have hComp := decompSucc_in_next_succ Gamma N (.ex x B) hFN m (Nat.le_max_right k m)
        (formulaSubstN B (Countable.enumerate m) x) (by simp [decompSuccGrowing])
      exact ⟨N + 1, Or.inr ⟨formulaSubstN B t x, by rw [← hm]; exact hComp,
        by simp [TypeC.comp, ← hm]⟩⟩

helper /-- Theorem 5.5.1 (companion, limitSet H4): Type-D existential — there
exists a term t such that D(t) is in the signed limit set. The witness
is a variable chosen beyond the bound variables of the quantified body.
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka_h4 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) :
    ∀ (d : TypeD L), d.toSigned ∈ signedLimitSet Gamma →
      ∃ (t : Term L), (termFunSyms t ⊆ signedSetFunSyms (signedLimitSet Gamma) ∧ termConstSyms t ⊆ signedSetConstSyms (signedLimitSet Gamma)) ∧
      ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  intro d hd
  obtain ⟨k, hSf⟩ := hd
  cases d with
  | tEx x B =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      let N := max k (formulaMaxBVN B)
      have hfree : isFreeForN (Term.var (N + 1)) x B := by
        apply isFreeForN_of_bv_disjoint
        intro v hv hbv
        have he : v = N + 1 := hv
        subst v
        have hb := formulaBVN_lt_formulaMaxBVN B (N + 1) hbv
        have hn := Nat.le_max_right k (formulaMaxBVN B)
        omega
      have hComp := decompAnt_in_next_ant Gamma N (.ex x B) (growingClosure_ant_mono_le Gamma (Nat.le_max_left k (formulaMaxBVN B)) _ hF) 0 (Nat.zero_le _)
        (formulaSubstN B (Term.var (N + 1)) x) (by simp [decompAntGrowing])
      exact ⟨Term.var (N + 1), ⟨fun _ h => h.elim, fun _ h => by cases h⟩, hfree, N + 1, Or.inl ⟨formulaSubstN B (Term.var (N + 1)) x,
        hComp, by simp [TypeD.comp]⟩⟩
    · cases hEq
  | fAll x B =>
    rcases hSf with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      let N := max k (formulaMaxBVN B)
      have hfree : isFreeForN (Term.var (N + 1)) x B := by
        apply isFreeForN_of_bv_disjoint
        intro v hv hbv
        have he : v = N + 1 := hv
        subst v
        have hb := formulaBVN_lt_formulaMaxBVN B (N + 1) hbv
        have hn := Nat.le_max_right k (formulaMaxBVN B)
        omega
      have hComp := decompSucc_in_next_succ Gamma N (.all x B) (growingClosure_succ_mono_le Gamma (Nat.le_max_left k (formulaMaxBVN B)) _ hF) 0 (Nat.zero_le _)
        (formulaSubstN B (Term.var (N + 1)) x) (by simp [decompSuccGrowing])
      exact ⟨Term.var (N + 1), ⟨fun _ h => h.elim, fun _ h => by cases h⟩, hfree, N + 1, Or.inr ⟨formulaSubstN B (Term.var (N + 1)) x,
        hComp, by simp [TypeD.comp]⟩⟩

helper /-- Theorem 5.5.1 (companion, limitSet H5): Variable membership is
trivial since H = Set.univ (fun _ => True). -/
theorem limitSet_isHintikka_h5 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) :
    ∀ (sf : SignedFormula L), sf ∈ signedLimitSet Gamma →
      ∀ (x : Nat), x ∈ signedFormulaFreeVars sf →
        (fun _ => True) (Term.var x : Term L) := by
-- BEGIN PROOF
  intro _ _ _ _; trivial

helper /-- Theorem 5.5.1 (companion, limitSet H6): isFreeFor for quantified
formulae — discharged from the caller-supplied hNFB standing
assumption (rectified bound variables). -/
theorem limitSet_isHintikka_h6 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hNFB : ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      (SignedFormula.trueF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ signedLimitSet Gamma) →
      isFreeForN t x A) :
    ∀ (x : Nat) (A : FormulaN L) (t : Term L), (fun _ => True) t →
      (SignedFormula.trueF (.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.trueF (.ex x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (.ex x A) ∈ signedLimitSet Gamma) →
      isFreeForN t x A := by
-- BEGIN PROOF
  intro x A t _ht hQ
  exact hNFB x A t hQ

helper /-- Theorem 5.5.1 (companion, limitSet hNoEq): No eq_ formula appears in
the signed limit set — follows from hNoEq on Gamma via
growingClosure_noEq preservation. -/
theorem limitSet_isHintikka_hNoEq {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A) :
    ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
      SignedFormula.trueF (FormulaN.eq_ hL t1 t2) ∉ signedLimitSet Gamma ∧
      SignedFormula.falseF (FormulaN.eq_ hL t1 t2) ∉ signedLimitSet Gamma := by
-- BEGIN PROOF
  intro hL t1 t2
  constructor
  · intro ⟨n, hsf⟩
    rcases hsf with ⟨A, hA, hEq⟩ | ⟨_, _, hEq⟩
    · have := SignedFormula.trueF.inj hEq; subst this
      exact (growingClosure_noEq Gamma hNoEq n).1 _ hA
    · cases hEq
  · intro ⟨n, hsf⟩
    rcases hsf with ⟨_, _, hEq⟩ | ⟨B, hB, hEq⟩
    · cases hEq
    · have := SignedFormula.falseF.inj hEq; subst this
      exact (growingClosure_noEq Gamma hNoEq n).2 _ hB

helper /-- Theorem 5.5.1 (companion, witness H0): No complementary atomic pair
along the path — wraps searchTree_path_no_complementary_atoms. -/
theorem limitSet_isHintikka_via_witness_h0 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ pathSignedSet w f ∧
        SignedFormula.falseF A ∈ pathSignedSet w f) := by
-- BEGIN PROOF
  intro A hAtom hBoth
  exact searchTree_path_no_complementary_atoms w f hPath A hAtom hBoth

helper /-- Theorem 5.5.1 (companion, witness H1): Type-A decomposition along
the path — first conjunct of searchTree_path_hintikka_propositional. -/
theorem limitSet_isHintikka_via_witness_h1 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (a : TypeA L), a.toSigned ∈ pathSignedSet w f →
      a.comp1 ∈ pathSignedSet w f ∧ a.comp2 ∈ pathSignedSet w f := by
-- BEGIN PROOF
  intro a ha
  exact (searchTree_path_hintikka_propositional w f hPath).1 a ha

helper /-- Theorem 5.5.1 (companion, witness H2): Type-B decomposition along
the path — second conjunct of searchTree_path_hintikka_propositional. -/
theorem limitSet_isHintikka_via_witness_h2 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (b : TypeB L), b.toSigned ∈ pathSignedSet w f →
      b.comp1 ∈ pathSignedSet w f ∨ b.comp2 ∈ pathSignedSet w f := by
-- BEGIN PROOF
  intro b hb
  exact (searchTree_path_hintikka_propositional w f hPath).2 b hb

helper /-- Theorem 5.5.1 (companion, witness H3): Type-C universal along the
path — wraps searchTree_path_hintikka_typeC.
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka_via_witness_h3 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (c : TypeC L), c.toSigned ∈ pathSignedSet w f →
      ∀ (t : Term L), (t ∈ safeTermsN seq ∧ termFunSyms t ⊆ signedSetFunSyms (pathSignedSet w f) ∧
        termConstSyms t ⊆ signedSetConstSyms (pathSignedSet w f)) →
      ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ pathSignedSet w f := by
-- BEGIN PROOF
  intro c hc t ht hfree
  exact searchTree_path_hintikka_typeC w f hPath c hc t ht.1 hfree

helper /-- Theorem 5.5.1 (companion, witness H4): Type-D existential along the
path — uses the fresh-variable witness from searchTree_path_hintikka_typeD_var.
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka_via_witness_h4 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (d : TypeD L), d.toSigned ∈ pathSignedSet w f →
      ∃ (t : Term L), (t ∈ safeTermsN seq ∧ termFunSyms t ⊆ signedSetFunSyms (pathSignedSet w f) ∧
        termConstSyms t ⊆ signedSetConstSyms (pathSignedSet w f)) ∧
      ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ pathSignedSet w f := by
-- BEGIN PROOF
  intro d hd
  obtain ⟨x, hx, hfree, hcomp⟩ := searchTree_path_hintikka_typeD_var w f hPath d hd
  exact ⟨Term.var x, ⟨hx, fun _ h => h.elim, fun _ h => by cases h⟩, hfree, hcomp⟩

helper /-- Theorem 5.5.1 (companion, witness H6): isFreeFor for quantified
formulae along the path — wraps searchTree_path_freeFor. -/
theorem limitSet_isHintikka_via_witness_h6 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (x : Nat) (A : FormulaN L) (t : Term L), t ∈ safeTermsN seq →
      (SignedFormula.trueF (.all x A) ∈ pathSignedSet w f ∨
       SignedFormula.falseF (.all x A) ∈ pathSignedSet w f ∨
       SignedFormula.trueF (.ex x A) ∈ pathSignedSet w f ∨
       SignedFormula.falseF (.ex x A) ∈ pathSignedSet w f) →
      isFreeForN t x A := by
-- BEGIN PROOF
  intro x A t ht hQ
  exact searchTree_path_freeFor w f hPath x A t ht hQ

helper /-- Theorem 5.5.1 (companion, witness hNoEq): No eq_ formula appears in
the path's signed set — wraps searchTree_path_no_eq. -/
theorem limitSet_isHintikka_via_witness_hNoEq {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
      SignedFormula.trueF (FormulaN.eq_ hL t1 t2) ∉ pathSignedSet w f ∧
      SignedFormula.falseF (FormulaN.eq_ hL t1 t2) ∉ pathSignedSet w f := by
-- BEGIN PROOF
  intro hL t1 t2
  exact searchTree_path_no_eq w f hPath hL t1 t2

helper /-- Theorem 5.5.1 (companion, path Hintikka): Given a SearchTreeData with an infinite path f,
the signed set collected along f is a Hintikka set (with
H consists of safe terms over the symbols occurring in the path set).

The Hintikka conditions follow from the SearchTreeData path properties (H0-H6).

Each IsHintikkaSet field maps directly to a SearchTreeData field:
- h0  <- path_no_complementary_atoms
- h1  <- path_hintikka_propositional (first conjunct)
- h2  <- path_hintikka_propositional (second conjunct)
- h3  <- path_hintikka_typeC
- h4  <- path_hintikka_typeD
- h5  <- free vars of path formulas have safe variable terms
- h6  <- path_freeFor (restricted to safeTermsN)
- hTA <- the occurrence-language term algebra
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka_via_witness {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality)
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    IsHintikkaSet L hL
      (fun t => t ∈ safeTermsN seq ∧ termFunSyms t ⊆ signedSetFunSyms (pathSignedSet w f) ∧
        termConstSyms t ⊆ signedSetConstSyms (pathSignedSet w f)) (pathSignedSet w f) :=
-- BEGIN PROOF
{
  hTA := safeReductTerms_isTermAlgebraOver seq (pathSignedSet w f)
  h0 := limitSet_isHintikka_via_witness_h0 w f hPath
  h1 := limitSet_isHintikka_via_witness_h1 w f hPath
  h2 := limitSet_isHintikka_via_witness_h2 w f hPath
  h3 := limitSet_isHintikka_via_witness_h3 w f hPath
  h4 := limitSet_isHintikka_via_witness_h4 w f hPath
  h5 := fun sf hsf x hx => ⟨limitSet_isHintikka_via_witness_h5 w f hPath sf hsf x hx,
    fun _ h => h.elim, fun _ h => by cases h⟩
  h6 := fun x A t ht hQ => limitSet_isHintikka_via_witness_h6 w f hPath x A t ht.1 hQ
}

helper /-- Theorem 5.5.1 (required helper): The path signed set contains
the signed versions of the root sequent's formulae. Since the root
sequent equals seq (by root_sequent), every formula in
seq.antecedent appears as trueF in the path set, and every formula
in seq.succedent appears as falseF. -/
theorem pathSignedSetN_contains_root {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    (∀ A ∈ seq.antecedent, SignedFormula.trueF A ∈ pathSignedSet w f) ∧
    (∀ B ∈ seq.succedent, SignedFormula.falseF B ∈ pathSignedSet w f) := by
-- BEGIN PROOF
  constructor
  · intro A hA
    refine ⟨0, hPath 0, Or.inl ⟨A, ?_, rfl⟩⟩
    -- List.ofFn (Fin 0 => f i) reduces to [] by definition
    -- nodeSequent [] root_mem = seq by root_sequent
    -- The proof argument for nodeSequent is hPath 0, but since
    -- List.ofFn (Fin 0 => f i) = [] definitionally, this matches root_mem.
    change A ∈ (w.nodeSequent [] _).antecedent
    rw [w.root_sequent]; exact hA
  · intro B hB
    refine ⟨0, hPath 0, Or.inr ⟨B, ?_, rfl⟩⟩
    change B ∈ (w.nodeSequent [] _).succedent
    rw [w.root_sequent]; exact hB

end LCS.FirstOrder.Completeness.InfiniteSearch
