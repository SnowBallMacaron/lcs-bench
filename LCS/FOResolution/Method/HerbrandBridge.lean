import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.GroundResolution
import LCS.CutElim.Hauptsatz
import LCS.Herbrand.SHGTheorem.Herbrand

/-!
# FOResolution.Method.HerbrandBridge

Untagged support for the Herbrand step in first-order resolution completeness.
The construction turns an exact nonempty enumeration of a clause set into a
closed universal-prenex sentence.  The empty clause is handled separately, so
the matrix never reaches `clauseToFormula`'s falsum fallback.
-/

namespace LCS.FOResolution.Method.HerbrandBridge

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.GroundResolution
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SHGTheorem.Herbrand

/-- Conjoin a head formula with a tail without an empty-list fallback. -/
def headConjunction {L : Language}
    (head : FormulaN L) : List (FormulaN L) → FormulaN L
  | [] => head
  | next :: rest => FormulaN.conj head (headConjunction next rest)

/-- The polarity-preserving conjunction of the formulae represented by a
nonempty list of clauses. -/
def clauseMatrix {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)) :
    FormulaN L :=
  headConjunction ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A head)
    (tail.map ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A))

/-- The deduplicated union of the variables occurring in the clause formulae. -/
def clauseVariablePrefix {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)) :
    List Nat :=
  (((head :: tail).map ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A)).flatMap formulaVarsList).eraseDups

/-- The universal closure of the nonempty clause conjunction. -/
def clauseSentence {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)) :
    FormulaN L :=
  Formula.prependAlls ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail)
    ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)

/-- Evaluation of a head-seeded conjunction is equivalent to evaluation of
its head and every member of its tail. -/
theorem formulaEvalN_headConjunction {L : Language}
    (M : Structure L) :
    ∀ (head : FormulaN L) (tail : List (FormulaN L)) (s : Assignment M),
      formulaEvalN M (headConjunction head tail) s ↔
        formulaEvalN M head s ∧
          ∀ next ∈ tail, formulaEvalN M next s := by
  intro head tail
  induction tail generalizing head with
  | nil =>
    intro s
    simp [headConjunction]
  | cons next rest ih =>
    intro s
    simp only [headConjunction, formulaEvalN]
    constructor
    · rintro ⟨hHead, hTail⟩
      have hRest := (ih next s).mp hTail
      refine ⟨hHead, ?_⟩
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hRest.1
      · exact hRest.2 F hF
    · rintro ⟨hHead, hAll⟩
      refine ⟨hHead, (ih next s).mpr ?_⟩
      refine ⟨hAll next (List.mem_cons_self), ?_⟩
      intro F hF
      exact hAll F (List.mem_cons_of_mem next hF)

/-- Free variables of a head-seeded conjunction come from one of its
constituents. -/
theorem formulaFVN_headConjunction {L : Language}
    (head : FormulaN L) (tail : List (FormulaN L)) (n : Nat) :
    formulaFVN (headConjunction head tail) n ↔
      formulaFVN head n ∨
        ∃ next ∈ tail, formulaFVN next n := by
  induction tail generalizing head with
  | nil =>
    simp [headConjunction]
  | cons next rest ih =>
    simp only [headConjunction, formulaFVN, Set.union]
    rw [ih next]
    simp only [List.mem_cons]
    constructor
    · rintro (hHead | hNext | ⟨F, hF, hn⟩)
      · exact Or.inl hHead
      · exact Or.inr ⟨next, Or.inl rfl, hNext⟩
      · exact Or.inr ⟨F, Or.inr hF, hn⟩
    · rintro (hHead | ⟨F, rfl | hF, hn⟩)
      · exact Or.inl hHead
      · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr ⟨F, hF, hn⟩)

/-- A head-seeded conjunction preserves quantifier-freeness. -/
theorem headConjunction_isQuantifierFree {L : Language}
    (head : FormulaN L) (tail : List (FormulaN L))
    (hHead : isQuantifierFree head)
    (hTail : ∀ F ∈ tail, isQuantifierFree F) :
    isQuantifierFree (headConjunction head tail) := by
  induction tail generalizing head with
  | nil =>
    simpa [headConjunction] using hHead
  | cons next rest ih =>
    simp only [headConjunction, isQuantifierFree]
    refine ⟨hHead, ih next ?_ ?_⟩
    · exact hTail next (List.mem_cons_self)
    · intro F hF
      exact hTail F (List.mem_cons_of_mem next hF)

/-- A head-seeded conjunction preserves NNF. -/
theorem headConjunction_isNNF {L : Language}
    (head : FormulaN L) (tail : List (FormulaN L))
    (hHead : FormulaN.isNNF head)
    (hTail : ∀ F ∈ tail, FormulaN.isNNF F) :
    FormulaN.isNNF (headConjunction head tail) := by
  induction tail generalizing head with
  | nil =>
    simpa [headConjunction] using hHead
  | cons next rest ih =>
    simp only [headConjunction, FormulaN.isNNF]
    refine ⟨hHead, ih next ?_ ?_⟩
    · exact hTail next (List.mem_cons_self)
    · intro F hF
      exact hTail F (List.mem_cons_of_mem next hF)

/-- A head-seeded conjunction preserves absence of equality formulae. -/
theorem headConjunction_noEq {L : Language}
    (head : FormulaN L) (tail : List (FormulaN L))
    (hHead : formulaNoEq head)
    (hTail : ∀ F ∈ tail, formulaNoEq F) :
    formulaNoEq (headConjunction head tail) := by
  induction tail generalizing head with
  | nil =>
    simpa [headConjunction] using hHead
  | cons next rest ih =>
    simp only [headConjunction, formulaNoEq]
    refine ⟨hHead, ih next ?_ ?_⟩
    · exact hTail next (List.mem_cons_self)
    · intro F hF
      exact hTail F (List.mem_cons_of_mem next hF)

/-- The polarity-preserving formula of a literal is quantifier-free. -/
theorem litToFormula_isQuantifierFree {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) :
    isQuantifierFree ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit) := by
  cases lit with
  | pos atom =>
    cases atom <;>
      simp [clauseToFormula.litToFormula, FOAtomCore.toFormula,
        isQuantifierFree]
  | neg atom =>
    cases atom <;>
      simp [clauseToFormula.litToFormula, FOAtomCore.toFormula,
        isQuantifierFree]

/-- The polarity-preserving formula of a literal is in NNF. -/
theorem litToFormula_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) :
    FormulaN.isNNF ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit) := by
  cases lit with
  | pos atom =>
    cases atom <;>
      simp [clauseToFormula.litToFormula, FOAtomCore.toFormula,
        FormulaN.isNNF]
  | neg atom =>
    cases atom <;>
      simp [clauseToFormula.litToFormula, FOAtomCore.toFormula,
        FormulaN.isNNF]

/-- In a language without equality, the polarity-preserving formula of a
literal contains no equality formula. -/
theorem litToFormula_noEq {L : Language}
    (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    formulaNoEq ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit) := by
  cases lit with
  | pos atom =>
    cases atom with
    | predN _ _ =>
      trivial
    | eq_ hEq _ _ =>
      have hFalse : False := by
        cases hNoEq.symm.trans hEq
      exact hFalse.elim
  | neg atom =>
    cases atom with
    | predN _ _ =>
      trivial
    | eq_ hEq _ _ =>
      have hFalse : False := by
        cases hNoEq.symm.trans hEq
      exact hFalse.elim

/-- A nonempty clause maps to a quantifier-free formula without using the
empty-clause fallback. -/
theorem clauseToFormula_isQuantifierFree_of_ne_nil {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) :
    ∀ (C : FOClause L hNoEq), C ≠ [] →
      isQuantifierFree ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
  intro C hC
  induction C with
  | nil =>
    exact (hC rfl).elim
  | cons lit rest ih =>
    cases rest with
    | nil =>
      simpa [clauseToFormula] using (litToFormula_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) lit
    | cons next rest =>
      simp only [clauseToFormula, isQuantifierFree]
      refine ⟨(litToFormula_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) lit, ?_⟩
      exact ih (by simp)

/-- A nonempty clause maps to an NNF formula without requiring the arbitrary
falsum witness `A` itself to be in NNF. -/
theorem clauseToFormula_isNNF_of_ne_nil {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) :
    ∀ (C : FOClause L hNoEq), C ≠ [] →
      FormulaN.isNNF ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
  intro C hC
  induction C with
  | nil =>
    exact (hC rfl).elim
  | cons lit rest ih =>
    cases rest with
    | nil =>
      simpa [clauseToFormula] using (litToFormula_isNNF (hNoEq := by all_goals exact hNoEq)) lit
    | cons next rest =>
      simp only [clauseToFormula, FormulaN.isNNF]
      refine ⟨(litToFormula_isNNF (hNoEq := by all_goals exact hNoEq)) lit, ?_⟩
      exact ih (by simp)

/-- A nonempty clause in a language without equality maps to a formula with
no equality subformula. -/
theorem clauseToFormula_noEq_of_ne_nil {L : Language}
    (hNoEq : L.withoutEquality) (A : FormulaN L) :
    ∀ (C : FOClause L hNoEq), C ≠ [] →
      formulaNoEq ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
  intro C hC
  induction C with
  | nil =>
    exact (hC rfl).elim
  | cons lit rest ih =>
    cases rest with
    | nil =>
      simpa [clauseToFormula] using (litToFormula_noEq (hNoEq := hNoEq)) lit
    | cons next rest =>
      simp only [clauseToFormula, formulaNoEq]
      refine ⟨(litToFormula_noEq (hNoEq := hNoEq)) lit, ?_⟩
      exact ih (by simp)

/-- The matrix of nonempty clauses is quantifier-free. -/
theorem clauseMatrix_isQuantifierFree {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hNonempty : ∀ C ∈ head :: tail, C ≠ []) :
    isQuantifierFree ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) := by
  apply headConjunction_isQuantifierFree
  · exact (clauseToFormula_isQuantifierFree_of_ne_nil (hNoEq := by all_goals exact hNoEq)) A head
      (hNonempty head (List.mem_cons_self))
  · intro F hF
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    exact (clauseToFormula_isQuantifierFree_of_ne_nil (hNoEq := by all_goals exact hNoEq)) A C
      (hNonempty C (List.mem_cons_of_mem head hC))

/-- The matrix of nonempty clauses is in NNF. -/
theorem clauseMatrix_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hNonempty : ∀ C ∈ head :: tail, C ≠ []) :
    FormulaN.isNNF ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) := by
  apply headConjunction_isNNF
  · exact (clauseToFormula_isNNF_of_ne_nil (hNoEq := by all_goals exact hNoEq)) A head
      (hNonempty head (List.mem_cons_self))
  · intro F hF
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    exact (clauseToFormula_isNNF_of_ne_nil (hNoEq := by all_goals exact hNoEq)) A C
      (hNonempty C (List.mem_cons_of_mem head hC))

/-- The matrix of nonempty clauses contains no equality formula when the
language has no equality. -/
theorem clauseMatrix_noEq {L : Language}
    (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hNonempty : ∀ C ∈ head :: tail, C ≠ []) :
    formulaNoEq ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) := by
  apply headConjunction_noEq
  · exact (clauseToFormula_noEq_of_ne_nil (hNoEq := hNoEq)) A head
      (hNonempty head (List.mem_cons_self))
  · intro F hF
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    exact (clauseToFormula_noEq_of_ne_nil (hNoEq := hNoEq)) A C
      (hNonempty C (List.mem_cons_of_mem head hC))

/-- The prefix is exactly the deduplicated flattened variable lists of the
source clause formulae. -/
theorem mem_clauseVariablePrefix_iff {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (n : Nat) :
    n ∈ (clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail ↔
      ∃ C ∈ head :: tail,
        n ∈ formulaVarsList ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
  constructor
  · intro h
    rw [clauseVariablePrefix, List.mem_eraseDups,
      List.mem_flatMap] at h
    obtain ⟨F, hF, hn⟩ := h
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    exact ⟨C, hC, hn⟩
  · rintro ⟨C, hC, hn⟩
    rw [clauseVariablePrefix, List.mem_eraseDups,
      List.mem_flatMap]
    exact ⟨(clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C, List.mem_map_of_mem hC, hn⟩

/-- `eraseDups` on a list of natural numbers is duplicate-free. -/
theorem eraseDups_nodup_nat (l : List Nat) :
    l.eraseDups.Nodup := by
  suffices h : ∀ (n : Nat) (l : List Nat),
      l.length ≤ n → l.eraseDups.Nodup by
    exact h l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hLength
    cases l with
    | nil => exact List.nodup_nil
    | cons _ tail =>
      exact (Nat.not_succ_le_zero tail.length hLength).elim
  | succ k ih =>
    intro l hLength
    cases l with
    | nil => exact List.nodup_nil
    | cons head tail =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter]
        intro ⟨_, hne⟩
        rw [beq_self_eq_true' head] at hne
        exact Bool.noConfusion hne
      · apply ih
        have hTail : tail.length ≤ k := by
          change Nat.succ tail.length ≤ Nat.succ k at hLength
          exact Nat.le_of_succ_le_succ hLength
        exact Nat.le_trans (List.length_filter_le _ _) hTail

/-- The constructed variable prefix is duplicate-free. -/
theorem clauseVariablePrefix_nodup {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)) :
    ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail).Nodup :=
  eraseDups_nodup_nat _

/-- The constructed prefix covers every free variable of the matrix. -/
theorem clauseVariablePrefix_covers_matrix {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (n : Nat) (hn : formulaFVN ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) n) :
    n ∈ (clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail := by
  rw [(mem_clauseVariablePrefix_iff (hNoEq := by all_goals exact hNoEq))]
  rcases (formulaFVN_headConjunction
    ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A head)
    (tail.map ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A)) n).mp hn with hHead | hTail
  · exact ⟨head, List.mem_cons_self,
      formulaVarsList_cover ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A head) n hHead⟩
  · obtain ⟨F, hF, hFV⟩ := hTail
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    exact ⟨C, List.mem_cons_of_mem head hC,
      formulaVarsList_cover ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) n hFV⟩

/-- Free variables left after prepending universals are precisely free
variables of the matrix that do not occur in the prefix. -/
theorem formulaFVN_prependAlls_iff {L : Language}
    (vars : List Nat) (matrix : FormulaN L) (n : Nat) :
    formulaFVN (Formula.prependAlls vars matrix) n ↔
      formulaFVN matrix n ∧ n ∉ vars := by
  induction vars with
  | nil =>
    simp [Formula.prependAlls]
  | cons var rest ih =>
    simp only [Formula.prependAlls, formulaFVN, Set.diff, Set.singleton]
    rw [ih]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨⟨hFV, hRest⟩, hNe⟩
      exact ⟨hFV, fun hMem => hMem.elim (fun h => hNe h) hRest⟩
    · rintro ⟨hFV, hMem⟩
      refine ⟨⟨hFV, ?_⟩, ?_⟩
      · intro hRest
        exact hMem (Or.inr hRest)
      · intro hEq
        exact hMem (Or.inl hEq)

/-- A universal prefix covering all matrix free variables makes a closed
formula. -/
theorem prependAlls_isClosed_of_cover {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hCover : ∀ n, formulaFVN matrix n → n ∈ vars) :
    FormulaN.isClosed (Formula.prependAlls vars matrix) := by
  unfold FormulaN.isClosed
  funext n
  apply propext
  constructor
  · intro hFV
    have h := (formulaFVN_prependAlls_iff vars matrix n).mp hFV
    exact (h.2 (hCover n h.1)).elim
  · intro h
    exact h.elim

/-- A quantifier-free formula has no bound variables. -/
theorem formulaBVN_eq_empty_of_isQuantifierFree {L : Language}
    (F : FormulaN L) (hQF : isQuantifierFree F) :
    formulaBVN F = ∅ := by
  induction F with
  | predN _ _ | eq_ _ _ _ =>
    rfl
  | neg F ih =>
    exact ih hQF
  | conj F G ihF ihG | disj F G ihF ihG | impl F G ihF ihG =>
    rw [formulaBVN, ihF hQF.1, ihG hQF.2]
    funext n
    apply propext
    simp [Set.union, Set.empty]
  | all _ _ | ex _ _ =>
    exact hQF.elim

/-- A quantifier-free formula has distinct quantifier bindings vacuously. -/
theorem distinctQuantifierBindings_of_isQuantifierFree {L : Language}
    (F : FormulaN L) (hQF : isQuantifierFree F) :
    distinctQuantifierBindings F := by
  induction F with
  | predN _ _ | eq_ _ _ _ =>
    trivial
  | neg F ih =>
    exact ih hQF
  | conj F G ihF ihG | disj F G ihF ihG | impl F G ihF ihG =>
    simp only [distinctQuantifierBindings]
    refine ⟨ihF hQF.1, ihG hQF.2, ?_⟩
    intro n hBoth
    have hEmpty := formulaBVN_eq_empty_of_isQuantifierFree F hQF.1
    rw [hEmpty] at hBoth
    exact hBoth.1.elim
  | all _ _ | ex _ _ =>
    exact hQF.elim

/-- Membership in the bound-variable set after prepending universals. -/
theorem formulaBVN_prependAlls_iff {L : Language}
    (vars : List Nat) (matrix : FormulaN L) (n : Nat) :
    formulaBVN (Formula.prependAlls vars matrix) n ↔
      formulaBVN matrix n ∨ n ∈ vars := by
  induction vars with
  | nil =>
    simp [Formula.prependAlls]
  | cons var rest ih =>
    simp only [Formula.prependAlls, formulaBVN, Set.union, Set.singleton,
      ih, List.mem_cons]
    constructor
    · rintro ((hMatrix | hRest) | hVar)
      · exact Or.inl hMatrix
      · exact Or.inr (Or.inr hRest)
      · exact Or.inr (Or.inl hVar)
    · rintro (hMatrix | hVar | hRest)
      · exact Or.inl (Or.inl hMatrix)
      · exact Or.inr hVar
      · exact Or.inl (Or.inr hRest)

/-- A duplicate-free universal prefix over a quantifier-free matrix has
distinct quantifier bindings. -/
theorem prependAlls_distinctQuantifierBindings {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hNodup : vars.Nodup)
    (hQF : isQuantifierFree matrix) :
    distinctQuantifierBindings (Formula.prependAlls vars matrix) := by
  have hMatrixBV : formulaBVN matrix = (∅ : Set Nat) :=
    formulaBVN_eq_empty_of_isQuantifierFree matrix hQF
  have hMatrixDistinct : distinctQuantifierBindings matrix :=
    distinctQuantifierBindings_of_isQuantifierFree matrix hQF
  induction vars with
  | nil =>
    simpa [Formula.prependAlls] using hMatrixDistinct
  | cons var rest ih =>
    have hNodup' := List.nodup_cons.mp hNodup
    simp only [Formula.prependAlls, distinctQuantifierBindings]
    refine ⟨ih hNodup'.2, ?_⟩
    intro hBV
    rcases (formulaBVN_prependAlls_iff rest matrix var).mp hBV with
      hMatrix | hRest
    · rw [hMatrixBV] at hMatrix
      exact hMatrix.elim
    · exact hNodup'.1 hRest

/-- A closed formula has no free/bound overlap. -/
theorem boundVarsFresh_of_isClosed {L : Language}
    (F : FormulaN L) (hClosed : FormulaN.isClosed F) :
    boundVarsFresh F := by
  intro n hBoth
  unfold FormulaN.isClosed at hClosed
  rw [hClosed] at hBoth
  exact hBoth.1.elim

/-- The constructed sentence is rectified. -/
theorem clauseSentence_isRectified {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hNonempty : ∀ C ∈ head :: tail, C ≠ []) :
    isRectified ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) := by
  have hQF := (clauseMatrix_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) A head tail hNonempty
  have hClosed : FormulaN.isClosed ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) := by
    apply prependAlls_isClosed_of_cover
    exact (clauseVariablePrefix_covers_matrix (hNoEq := by all_goals exact hNoEq)) A head tail
  refine ⟨boundVarsFresh_of_isClosed _ hClosed, ?_⟩
  exact prependAlls_distinctQuantifierBindings
    ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail)
    ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
    ((clauseVariablePrefix_nodup (hNoEq := by all_goals exact hNoEq)) A head tail) hQF

/-- Prepending universal quantifiers preserves NNF. -/
theorem prependAlls_isNNF {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hNNF : FormulaN.isNNF matrix) :
    FormulaN.isNNF (Formula.prependAlls vars matrix) := by
  induction vars with
  | nil =>
    simpa [Formula.prependAlls] using hNNF
  | cons _ rest ih =>
    simpa [Formula.prependAlls, FormulaN.isNNF] using ih

/-- Prepending universal quantifiers preserves absence of equality. -/
theorem prependAlls_noEq {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hNoEq : formulaNoEq matrix) :
    formulaNoEq (Formula.prependAlls vars matrix) := by
  induction vars with
  | nil =>
    simpa [Formula.prependAlls] using hNoEq
  | cons _ rest ih =>
    simpa [Formula.prependAlls, formulaNoEq] using ih

/-- A universal prefix over a quantifier-free matrix is universal-prenex. -/
theorem prependAlls_isUniversalPrenex {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hQF : isQuantifierFree matrix) :
    Formula.isUniversalPrenex (Formula.prependAlls vars matrix) := by
  induction vars with
  | nil =>
    cases matrix <;>
      simp_all [Formula.prependAlls, Formula.isUniversalPrenex,
        isQuantifierFree]
  | cons _ rest ih =>
    simpa [Formula.prependAlls, Formula.isUniversalPrenex] using ih

/-- Stripping the leading universal quantifiers recovers the whole supplied
prefix and the quantifier-free matrix exactly. -/
theorem stripAllPrenex_prependAlls_eq {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hQF : isQuantifierFree matrix) :
    Formula.stripAllPrenex (Formula.prependAlls vars matrix) =
      (vars, matrix) := by
  induction vars with
  | nil =>
    cases matrix <;>
      simp_all [Formula.prependAlls, Formula.stripAllPrenex,
        isQuantifierFree]
  | cons var rest ih =>
    simp only [Formula.prependAlls, Formula.stripAllPrenex, ih]

/-- A universal prefix over a quantifier-free matrix is prenex in the
Chapter 7 sense and contains only universal quantifiers. -/
theorem prependAlls_universalPrenexFormula {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hQF : isQuantifierFree matrix) :
    UniversalPrenexFormula (Formula.prependAlls vars matrix) := by
  induction vars with
  | nil =>
      constructor
      · exact qf_isPrenex matrix hQF
      · intro p hp
        cases matrix <;>
          simp_all [Formula.prependAlls, prenexPrefix,
            isQuantifierFree]
  | cons var rest ih =>
      constructor
      · change isPrenex (Formula.prependAlls rest matrix)
        exact ih.1
      · intro p hp
        simp only [Formula.prependAlls, prenexPrefix,
          List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · exact ih.2 p hp

/-- Chapter 7 prefix extraction recovers exactly the variables prepended by
`Formula.prependAlls`. -/
theorem prenexPrefix_prependAlls_map_snd_eq {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hQF : isQuantifierFree matrix) :
    (prenexPrefix (Formula.prependAlls vars matrix)).map Prod.snd =
      vars := by
  induction vars with
  | nil =>
      cases matrix <;>
        simp_all [Formula.prependAlls, prenexPrefix,
          isQuantifierFree]
  | cons var rest ih =>
      simp [Formula.prependAlls, prenexPrefix, ih]

/-- Chapter 7 matrix extraction removes exactly the universal prefix supplied
by `Formula.prependAlls`. -/
theorem prenexMatrix_prependAlls_eq {L : Language}
    (vars : List Nat) (matrix : FormulaN L)
    (hQF : isQuantifierFree matrix) :
    prenexMatrix (Formula.prependAlls vars matrix) = matrix := by
  induction vars with
  | nil =>
      cases matrix <;>
        simp_all [Formula.prependAlls, prenexMatrix,
          isQuantifierFree]
  | cons var rest ih =>
      simp [Formula.prependAlls, prenexMatrix, ih]

/-- Instantiating a universal prefix is enough to evaluate its matrix under
any target assignment, provided the starting assignment already agrees with
the target outside the remaining prefix. -/
theorem formulaEvalN_prependAlls_to_assignment {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (matrix : FormulaN L) (target : Assignment M) :
    ∀ (vars : List Nat) (start : Assignment M),
      (∀ n, formulaFVN matrix n → n ∉ vars → start n = target n) →
      formulaEvalN M (Formula.prependAlls vars matrix) start →
      formulaEvalN M matrix target := by
  intro vars
  induction vars with
  | nil =>
    intro start hAgree hEval
    apply (coincidenceLemmaN M matrix start target ?_).mp hEval
    intro n hn
    exact hAgree n hn (by simp)
  | cons var rest ih =>
    intro start hAgree hEval
    simp only [Formula.prependAlls, formulaEvalN] at hEval
    apply ih (assignUpdate start var (target var)) ?_ (hEval (target var))
    intro n hn hNotRest
    by_cases hEq : n = var
    · subst n
      simp [assignUpdate]
    · rw [assignUpdate]
      simp only [hEq, if_false]
      apply hAgree n hn
      intro hMem
      rcases List.mem_cons.mp hMem with h | h
      · exact hEq h
      · exact hNotRest h

/-- A satisfying assignment for the closed universal sentence yields
pointwise evaluation of its matrix under every assignment. -/
theorem clauseSentence_matrix_valid {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (start : Assignment M)
    (hSentence : formulaEvalN M ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) start) :
    ∀ target : Assignment M,
      formulaEvalN M ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) target := by
  intro target
  apply (formulaEvalN_prependAlls_to_assignment (hNoEq := by all_goals exact hNoEq))
    M ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) target
    ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail) start
  · intro n hn hNotPrefix
    exact (hNotPrefix ((clauseVariablePrefix_covers_matrix (hNoEq := by all_goals exact hNoEq))
      A head tail n hn)).elim
  · exact hSentence

/-- Every source clause formula is true whenever the matrix is true. -/
theorem clauseToFormula_eval_of_matrix_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (s : Assignment M)
    (hMatrix : formulaEvalN M ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) s) :
    ∀ C ∈ head :: tail,
      formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s := by
  have hConj := (formulaEvalN_headConjunction M
    ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A head)
    (tail.map ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A)) s).mp hMatrix
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact hConj.1
  · exact hConj.2 _ (List.mem_map_of_mem hC)

/-- Exact source enumeration and source unsatisfiability transfer to semantic
unsatisfiability of the constructed universal sentence. -/
theorem clauseSentence_isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hExact : ∀ C, S C ↔ C ∈ head :: tail)
    (hUnsat : (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) S) :
    Formula.isUnsatisfiable ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) := by
  intro hSat
  obtain ⟨M, start, hSentence⟩ := hSat
  apply hUnsat
  refine ⟨M, ?_⟩
  intro C hSC s
  apply clauseToFormula_exists_of_true hNoEq M s A C
  apply (clauseToFormula_eval_of_matrix_eval (hNoEq := by all_goals exact hNoEq)) M A head tail s
  · exact (clauseSentence_matrix_valid (hNoEq := by all_goals exact hNoEq)) M A head tail start hSentence s
  · exact (hExact C).mp hSC

/-- The proof properties carried by an exact nonempty clause enumeration.
All constructed formulae are definitionally tied to `head` and `tail`; no
arbitrary formula witness is stored. -/
structure ClauseSentenceProperties {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)) : Prop where
  source_exact : ∀ C, S C ↔ C ∈ head :: tail
  source_without_empty : ¬ S []
  language_without_equality : L.withoutEquality
  clauses_nonempty : ∀ C ∈ head :: tail, C ≠ []
  prefix_exact :
    ∀ n, n ∈ (clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail ↔
      ∃ C ∈ head :: tail,
        n ∈ formulaVarsList ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C)
  prefix_nodup : ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail).Nodup
  matrix_quantifier_free : isQuantifierFree ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
  matrix_nnf : FormulaN.isNNF ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_nnf : FormulaN.isNNF ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_no_equality : formulaNoEq ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_closed : FormulaN.isClosed ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_rectified : isRectified ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_universal_prenex :
    Formula.isUniversalPrenex ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_full_prefix :
    Formula.stripAllPrenex ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) =
      ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail, (clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
  sentence_unsatisfiable :
    Formula.isUnsatisfiable ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail)

/-- An existing indexed G2 proof and its exact midsequent expose a nonempty
list of full-prefix instances of the canonical clause matrix. The list is the
actual mid-antecedent enumeration, and G2 soundness makes it semantically
unsatisfiable. This bridge consumes `T` and `hMid`; it does not construct
either witness. -/
theorem clauseSentence_midsequent_matrixInstances
    {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FormulaN L)]
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hP : (ClauseSentenceProperties (hNoEq := by all_goals exact hNoEq)) A S head tail)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail))
      LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.1.toList ≠ [] ∧
      (∀ target, target ∈ mid.1.toList →
        ∃ substitutions : List (Nat × Term L),
          substitutions.map Prod.fst =
              (clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail ∧
            replayQuantifierSubstitutionsFormula substitutions
              ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) = target) ∧
      ∀ (M : Structure L) (s : Assignment M),
        ∃ target ∈ mid.1.toList,
          ¬ formulaEvalN M target s := by
  classical
  let source := (clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail
  have hSource : UniversalPrenexFormula source := by
    dsimp [source, clauseSentence]
    exact prependAlls_universalPrenexFormula
      ((clauseVariablePrefix (hNoEq := by all_goals exact hNoEq)) A head tail)
      ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) hP.matrix_quantifier_free
  have hDistinct : distinctQuantifierBindings source := by
    exact hP.sentence_rectified.2
  rcases universalPrenexSingleton_midsequentFullPrefixList
      source hSource hDistinct mid hMid with
    ⟨hSuccedent, occurrence, instances, _hAbove,
      hAllSubLeft, _hInstancesNonempty, hOfList,
      hInstances⟩
  have hRootNonempty :
      LCS.Finset.singleton source ≠ LCS.Finset.empty := by
    intro hEmpty
    have hSourceMem : source ∈ LCS.Finset.singleton source :=
      (LCS.Finset.mem_singleton source source).mpr rfl
    rw [hEmpty] at hSourceMem
    exact LCS.Finset.not_mem_empty hSourceMem
  have hMidNonempty : mid.1 ≠ LCS.Finset.empty :=
    antecedent_ne_empty_of_allSubLeftOnPath
      occurrence.path hAllSubLeft hRootNonempty
  refine ⟨finset_toList_ne_nil_of_ne_empty mid.1 hMidNonempty,
    ?_, ?_⟩
  · intro target hTarget
    have hTargetMid : target ∈ mid.1 :=
      (LCS.Finset.mem_toList mid.1 target).mp hTarget
    have hTargetInstances : target ∈ instances := by
      apply LCS.Finset.mem_ofList.mp
      rw [hOfList]
      exact hTargetMid
    obtain ⟨substitutions, _hLineage, hPrefix, hReplay⟩ :=
      hInstances target hTargetInstances
    refine ⟨substitutions, ?_, ?_⟩
    · simpa only [source, clauseSentence,
        prenexPrefix_prependAlls_map_snd_eq
          (clauseVariablePrefix hNoEq A head tail)
          (clauseMatrix hNoEq A head tail) hP.matrix_quantifier_free]
        using hPrefix
    · simpa only [source, clauseSentence,
        prenexMatrix_prependAlls_eq
          (clauseVariablePrefix hNoEq A head tail)
          (clauseMatrix hNoEq A head tail) hP.matrix_quantifier_free]
        using hReplay
  · intro M s
    apply Classical.byContradiction
    intro hNoCounterexample
    have hAntecedent :
        ∀ target, target ∈ mid.1 → formulaEvalN M target s := by
      intro target hTarget
      have hTargetList : target ∈ mid.1.toList :=
        (LCS.Finset.mem_toList mid.1 target).mpr hTarget
      apply Classical.byContradiction
      intro hFalse
      exact hNoCounterexample ⟨target, hTargetList, hFalse⟩
    have hSuccedentFalse :
        ∀ target, target ∈ mid.2 → ¬ formulaEvalN M target s := by
      intro target hTarget
      rw [hSuccedent] at hTarget
      exact (LCS.Finset.not_mem_empty hTarget).elim
    exact g2nnf_tree_soundness hNoEq M occurrence.node
      ⟨s, hAntecedent, hSuccedentFalse⟩

private def replaySingleSubst {L : Language}
    (x : Nat) (t : Term L) : Nat → Term L :=
  fun y => if y = x then t else .var y

private def replaySimultaneousSubst {L : Language} :
    List (Nat × Term L) → Nat → Term L
  | [] => identitySubst
  | (x, t) :: rest =>
      SubstitutionCore.substCompose (replaySimultaneousSubst rest)
        (replaySingleSubst x t)

private theorem termSubst_eq_replaySingleSubst {L : Language}
    (source replacement : Term L) (x : Nat) :
    termSubst source replacement x =
      termSubstAll source (replaySingleSubst x replacement) := by
  induction source with
  | var y =>
      simp [termSubst, termSubstAll, replaySingleSubst]
  | const =>
      rfl
  | func f args ih =>
      simp only [termSubst, termSubstAll]
      congr 1
      funext i
      exact ih i

private theorem formulaSubstN_eq_replaySingleSubst_of_qf
    {L : Language}
    (F : FormulaN L) (replacement : Term L) (x : Nat)
    (hQF : isQuantifierFree F) :
    formulaSubstN F replacement x =
      substLit.substFormula (replaySingleSubst x replacement) F := by
  induction F with
  | predN P args =>
      simp only [formulaSubstN, substLit.substFormula]
      congr 1
      funext i
      exact termSubst_eq_replaySingleSubst (args i) replacement x
  | eq_ hL lhs rhs =>
      simp only [formulaSubstN, substLit.substFormula]
      congr 1
      · exact termSubst_eq_replaySingleSubst lhs replacement x
      · exact termSubst_eq_replaySingleSubst rhs replacement x
  | neg F ih =>
      exact congrArg FormulaN.neg (ih hQF)
  | conj F G ihF ihG =>
      simp only [formulaSubstN, substLit.substFormula]
      congr 1
      · exact ihF hQF.1
      · exact ihG hQF.2
  | disj F G ihF ihG =>
      simp only [formulaSubstN, substLit.substFormula]
      congr 1
      · exact ihF hQF.1
      · exact ihG hQF.2
  | impl F G ihF ihG =>
      simp only [formulaSubstN, substLit.substFormula]
      congr 1
      · exact ihF hQF.1
      · exact ihG hQF.2
  | all _ _ | ex _ _ =>
      exact hQF.elim

private theorem substFormula_identity {L : Language}
    (F : FormulaN L) :
    substLit.substFormula identitySubst F = F := by
  induction F with
  | predN P args =>
      simp only [substLit.substFormula]
      congr 1
      funext i
      exact termSubstAll_identity (args i)
  | eq_ hL lhs rhs =>
      simp only [substLit.substFormula]
      rw [termSubstAll_identity, termSubstAll_identity]
  | neg F ih =>
      exact congrArg FormulaN.neg ih
  | conj F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | disj F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | impl F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | all x F ih =>
      exact congrArg (FormulaN.all x) ih
  | ex x F ih =>
      exact congrArg (FormulaN.ex x) ih

private theorem substFormula_comp_local {L : Language}
    (F : FormulaN L) (sigma theta : Nat → Term L) :
    substLit.substFormula sigma (substLit.substFormula theta F) =
      substLit.substFormula (SubstitutionCore.substCompose sigma theta) F := by
  induction F with
  | predN P args =>
      simp only [substLit.substFormula]
      congr 1
      funext i
      exact SubstitutionCore.termSubstAll_compose (args i) theta sigma
  | eq_ hL lhs rhs =>
      simp only [substLit.substFormula]
      congr 1
      · exact SubstitutionCore.termSubstAll_compose lhs theta sigma
      · exact SubstitutionCore.termSubstAll_compose rhs theta sigma
  | neg F ih =>
      exact congrArg FormulaN.neg ih
  | conj F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | disj F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | impl F G ihF ihG =>
      simp only [substLit.substFormula]
      congr 1 <;> assumption
  | all x F ih =>
      exact congrArg (FormulaN.all x) ih
  | ex x F ih =>
      exact congrArg (FormulaN.ex x) ih

private theorem replayFormula_eq_substFormula_of_qf {L : Language}
    (substitutions : List (Nat × Term L))
    (F : FormulaN L) (hQF : isQuantifierFree F) :
    replayQuantifierSubstitutionsFormula substitutions F =
      substLit.substFormula
        (replaySimultaneousSubst substitutions) F := by
  induction substitutions generalizing F with
  | nil =>
      exact (substFormula_identity F).symm
  | cons substitution rest ih =>
      obtain ⟨x, replacement⟩ := substitution
      simp only [replayQuantifierSubstitutionsFormula,
        replaySimultaneousSubst]
      rw [ih (formulaSubstN F replacement x)
          (qf_formulaSubstN F replacement x hQF),
        formulaSubstN_eq_replaySingleSubst_of_qf
          F replacement x hQF]
      exact substFormula_comp_local F
        (replaySimultaneousSubst rest)
        (replaySingleSubst x replacement)

private theorem clauseEval_of_isSatisfied {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (C : FOClause L hNoEq)
    (hSat : (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s C) :
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s := by
  obtain ⟨lit, hLit, hLitSat⟩ := hSat
  apply (clauseToFormula_true_of_mem (hNoEq := by all_goals exact hNoEq)) M s A C lit hLit
  cases lit <;> exact hLitSat

private theorem false_substituted_matrix_source_clause
    {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (A : FormulaN L) (head : FOClause L hNoEq)
    (tail : List (FOClause L hNoEq))
    (sigma : Nat → Term L)
    (hQF : isQuantifierFree ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail))
    (hFalse :
      ¬ formulaEvalN M
        (substLit.substFormula sigma ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)) s) :
    ∃ C ∈ head :: tail,
      ¬ (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C) := by
  apply Classical.byContradiction
  intro hNoFalseClause
  have hAllSatisfied :
      ∀ C ∈ head :: tail,
        (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C) := by
    intro C hC
    apply Classical.byContradiction
    intro hFalseC
    exact hNoFalseClause ⟨C, hC, hFalseC⟩
  apply hFalse
  apply ((substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
    (isQF_implies_substFreshFor sigma
      ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) hQF)).mpr
  apply (formulaEvalN_headConjunction M
    ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A head)
    (tail.map ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A))
    (fun x => termEval M s (sigma x))).mpr
  constructor
  · apply ((substLits_clauseToFormula_eval (hNoEq := by all_goals exact hNoEq))
      M s A sigma head ((clauseQF (hNoEq := by all_goals exact hNoEq)) head)).mp
    exact (clauseEval_of_isSatisfied (hNoEq := by all_goals exact hNoEq)) M s A _
      (hAllSatisfied head List.mem_cons_self)
  · intro F hF
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hF
    apply ((substLits_clauseToFormula_eval (hNoEq := by all_goals exact hNoEq))
      M s A sigma C ((clauseQF (hNoEq := by all_goals exact hNoEq)) C)).mp
    exact (clauseEval_of_isSatisfied (hNoEq := by all_goals exact hNoEq)) M s A _
      (hAllSatisfied C (List.mem_cons_of_mem head hC))

private theorem substLit_comp_local {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (sigma theta : Nat → Term L) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) theta lit) =
      (substLit (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma theta) lit := by
  cases lit with
  | pos atom | neg atom =>
      simp only [substLit]
      congr 1
      cases atom with
      | predN P args =>
          simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
          congr 1
          funext i
          exact SubstitutionCore.termSubstAll_compose (args i) theta sigma
      | eq_ hL lhs rhs =>
          simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
          congr 1
          · exact SubstitutionCore.termSubstAll_compose lhs theta sigma
          · exact SubstitutionCore.termSubstAll_compose rhs theta sigma

private theorem substLits_comp_local {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (sigma theta : Nat → Term L) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) theta C) =
      (substLits (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma theta) C := by
  simp only [substLits, List.map_map]
  apply List.map_congr_left
  intro lit _
  exact (substLit_comp_local (hNoEq := by all_goals exact hNoEq)) lit sigma theta

private theorem seed_lift_substLits_eq {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (sigma : Nat → Term L) :
    (substLits (hNoEq := by all_goals exact hNoEq)) FreshGroundLanguage.seedSubst
        ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C)) =
      (substLits (hNoEq := by all_goals exact hNoEq))
        (SubstitutionCore.substCompose FreshGroundLanguage.seedSubst
          (FreshGroundLanguage.liftSubst sigma))
        ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C) := by
  rw [(FreshGroundLanguage.liftClause_substLits (hNoEq := by all_goals exact hNoEq))]
  exact (substLits_comp_local (hNoEq := by all_goals exact hNoEq))
    ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C)
    FreshGroundLanguage.seedSubst
    (FreshGroundLanguage.liftSubst sigma)

private def freshGroundReduct {L : Language}
    (M : Structure (FreshGroundLanguage L)) : Structure L where
  carrier := M.carrier
  carrierNonempty := M.carrierNonempty
  interpFunc := M.interpFunc
  interpConst := fun c => M.interpConst (Sum.inl c)
  interpPred := M.interpPred

private theorem termEval_liftTerm_reduct {L : Language}
    (M : Structure (FreshGroundLanguage L))
    (s : Assignment M) (t : Term L) :
    termEval M s (FreshGroundLanguage.liftTerm t) =
      termEval (freshGroundReduct M) s t := by
  induction t with
  | var =>
      rfl
  | const =>
      rfl
  | func f args ih =>
      simp only [FreshGroundLanguage.liftTerm, termEval,
        freshGroundReduct]
      congr 1
      funext i
      exact ih i

private theorem atomEval_liftAtom_reduct {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure (FreshGroundLanguage L))
    (s : Assignment M) (atom : FOAtom L hNoEq) :
    formulaEvalN M ((FreshGroundLanguage.liftAtom (hNoEq := by all_goals exact hNoEq)) atom).toFormula s ↔
      formulaEvalN (freshGroundReduct M) atom.toFormula s := by
  cases atom with
  | predN P args =>
      change
        M.interpPred P
            (fun i => termEval M s
              (FreshGroundLanguage.liftTerm (args i))) ↔
          M.interpPred P
            (fun i => termEval (freshGroundReduct M) s (args i))
      simp only [termEval_liftTerm_reduct]
  | eq_ hL lhs rhs =>
      simp only [FreshGroundLanguage.liftAtom, FOAtomCore.toFormula,
        formulaEvalN]
      rw [termEval_liftTerm_reduct M s lhs,
        termEval_liftTerm_reduct M s rhs]
      exact Iff.rfl

private theorem literalSatisfied_liftLiteral_reduct {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure (FreshGroundLanguage L))
    (s : Assignment M) (lit : FOLiteral L hNoEq) :
    (FOLiteral.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s
        ((FreshGroundLanguage.liftLiteral (hNoEq := by all_goals exact hNoEq)) lit) ↔
      (FOLiteral.isSatisfied (hNoEq := by all_goals exact hNoEq)) (freshGroundReduct M) s lit := by
  cases lit with
  | pos atom =>
      exact (atomEval_liftAtom_reduct (hNoEq := by all_goals exact hNoEq)) M s atom
  | neg atom =>
      exact not_congr ((atomEval_liftAtom_reduct (hNoEq := by all_goals exact hNoEq)) M s atom)

private theorem clauseSatisfied_liftClause_reduct {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure (FreshGroundLanguage L))
    (s : Assignment M) (C : FOClause L hNoEq) :
    (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C) ↔
      (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) (freshGroundReduct M) s C := by
  constructor
  · rintro ⟨lit, hLit, hSat⟩
    obtain ⟨source, hSource, rfl⟩ := List.mem_map.mp hLit
    exact ⟨source, hSource,
      ((literalSatisfied_liftLiteral_reduct (hNoEq := by all_goals exact hNoEq)) M s source).mp hSat⟩
  · rintro ⟨lit, hLit, hSat⟩
    refine ⟨(FreshGroundLanguage.liftLiteral (hNoEq := by all_goals exact hNoEq)) lit,
      List.mem_map_of_mem hLit, ?_⟩
    exact ((literalSatisfied_liftLiteral_reduct (hNoEq := by all_goals exact hNoEq)) M s lit).mpr hSat

private theorem literalSatisfied_substLit {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (sigma : Nat → Term L) (lit : FOLiteral L hNoEq) :
    (FOLiteral.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit) ↔
      (FOLiteral.isSatisfied (hNoEq := by all_goals exact hNoEq)) M
        (fun x => termEval M s (sigma x)) lit := by
  cases lit with
  | pos atom =>
      simpa [FOLiteral.isSatisfied, clauseToFormula.litToFormula,
        substLit] using
        (substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma (.pos atom)
          ((litToFormula_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) (.pos atom))
  | neg atom =>
      simpa [FOLiteral.isSatisfied, clauseToFormula.litToFormula,
        substLit, formulaEvalN, negM] using
        (substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma (.neg atom)
          ((litToFormula_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) (.neg atom))

private theorem clauseSatisfied_substLits {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (sigma : Nat → Term L) (C : FOClause L hNoEq) :
    (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C) ↔
      (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M
        (fun x => termEval M s (sigma x)) C := by
  constructor
  · rintro ⟨lit, hLit, hSat⟩
    obtain ⟨source, hSource, rfl⟩ := List.mem_map.mp hLit
    exact ⟨source, hSource,
      ((literalSatisfied_substLit (hNoEq := by all_goals exact hNoEq)) M s sigma source).mp hSat⟩
  · rintro ⟨lit, hLit, hSat⟩
    refine ⟨(substLit (hNoEq := by all_goals exact hNoEq)) sigma lit, List.mem_map_of_mem hLit, ?_⟩
    exact ((literalSatisfied_substLit (hNoEq := by all_goals exact hNoEq)) M s sigma lit).mpr hSat

private theorem seededLift_satisfied_iff {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure (FreshGroundLanguage L))
    (s : Assignment M) (C : FOClause L hNoEq) :
    (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) M s
        ((substLits (hNoEq := by all_goals exact hNoEq)) FreshGroundLanguage.seedSubst
          ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C)) ↔
      (FOClause.isSatisfied (hNoEq := by all_goals exact hNoEq)) (freshGroundReduct M)
        (fun _ => termEval M s FreshGroundLanguage.seed) C := by
  rw [(clauseSatisfied_substLits (hNoEq := by all_goals exact hNoEq)),
    (clauseSatisfied_liftClause_reduct (hNoEq := by all_goals exact hNoEq))]
  rfl

/-- Proof of Theorem 8.5.1 (Herbrand bridge): the actual mid-antecedent
    occurrences, crossed with the source clauses and grounded by the fresh
    seed, form a finite unsatisfiable set of exact source instances. -/
theorem clauseSentence_midsequent_groundInstances
    {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FormulaN L)]
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq))
    (hP : (ClauseSentenceProperties (hNoEq := by all_goals exact hNoEq)) A S head tail)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail))
      LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    ∃ Sg : List (FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)),
      (∀ c ∈ Sg, (FOClause.isGround (by all_goals exact hNoEq)) c) ∧
      (∀ c ∈ Sg,
        ∃ (C : FOClause L hNoEq)
          (sigma : Nat → Term (FreshGroundLanguage L)),
          S C ∧
            c = (substLits (hNoEq := by all_goals exact hNoEq)) sigma
              ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq)) C)) ∧
      (GroundClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Sg := by
  classical
  obtain ⟨_hMidNonempty, hInstances, hMidFalse⟩ :=
    (clauseSentence_midsequent_matrixInstances (hNoEq := by all_goals exact hNoEq))
      A S head tail hP mid hMid
  let substitutionsFor :
      FormulaN L → List (Nat × Term L) :=
    fun target =>
      if h : target ∈ mid.1.toList then
        Classical.choose (hInstances target h)
      else
        []
  let replayFor : FormulaN L → Nat → Term L :=
    fun target =>
      replaySimultaneousSubst (substitutionsFor target)
  let groundInstance :
      FormulaN L → FOClause L hNoEq →
        FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) :=
    fun target C =>
      (substLits (hNoEq := by all_goals exact hNoEq)) FreshGroundLanguage.seedSubst
        ((FreshGroundLanguage.liftClause (hNoEq := by all_goals exact hNoEq))
          ((substLits (hNoEq := by all_goals exact hNoEq)) (replayFor target) C))
  let Sg : List (FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :=
    mid.1.toList.flatMap fun target =>
      (head :: tail).map (groundInstance target)
  refine ⟨Sg, ?_, ?_, ?_⟩
  · intro c hC
    obtain ⟨target, _hTarget, hC⟩ :=
      List.mem_flatMap.mp (show c ∈ Sg from hC)
    obtain ⟨C, _hSource, rfl⟩ := List.mem_map.mp hC
    exact (FreshGroundLanguage.substLits_seed_isGround (hNoEq := by all_goals exact hNoEq)) _
  · intro c hC
    obtain ⟨target, _hTarget, hC⟩ :=
      List.mem_flatMap.mp (show c ∈ Sg from hC)
    obtain ⟨C, hSource, rfl⟩ := List.mem_map.mp hC
    refine ⟨C,
      SubstitutionCore.substCompose FreshGroundLanguage.seedSubst
        (FreshGroundLanguage.liftSubst (replayFor target)),
      (hP.source_exact C).mpr hSource, ?_⟩
    exact (seed_lift_substLits_eq (hNoEq := by all_goals exact hNoEq)) C (replayFor target)
  · intro M s
    let reduct := freshGroundReduct M
    let seedAssignment : Assignment reduct :=
      fun _ => termEval M s FreshGroundLanguage.seed
    obtain ⟨target, hTarget, hTargetFalse⟩ :=
      hMidFalse reduct seedAssignment
    have hReplay :
        replayQuantifierSubstitutionsFormula
            (substitutionsFor target)
            ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) =
          target := by
      dsimp [substitutionsFor]
      rw [dif_pos hTarget]
      exact (Classical.choose_spec (hInstances target hTarget)).2
    have hSubstTarget :
        substLit.substFormula (replayFor target)
            ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) =
          target := by
      calc
        substLit.substFormula (replayFor target)
            ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) =
            substLit.substFormula
              (replaySimultaneousSubst (substitutionsFor target))
              ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) := rfl
        _ = replayQuantifierSubstitutionsFormula
              (substitutionsFor target)
              ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail) :=
          (replayFormula_eq_substFormula_of_qf
            (substitutionsFor target)
            ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail)
            hP.matrix_quantifier_free).symm
        _ = target := hReplay
    have hSubstFalse :
        ¬ formulaEvalN reduct
          (substLit.substFormula (replayFor target)
            ((clauseMatrix (hNoEq := by all_goals exact hNoEq)) A head tail))
          seedAssignment := by
      rw [hSubstTarget]
      exact hTargetFalse
    obtain ⟨C, hSource, hCFalse⟩ :=
      (false_substituted_matrix_source_clause (hNoEq := by all_goals exact hNoEq))
        reduct seedAssignment A head tail
        (replayFor target) hP.matrix_quantifier_free hSubstFalse
    refine ⟨groundInstance target C, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨target, hTarget, List.mem_map_of_mem hSource⟩
    · intro hSat
      apply hCFalse
      exact ((seededLift_satisfied_iff (hNoEq := by all_goals exact hNoEq)) M s
        ((substLits (hNoEq := by all_goals exact hNoEq)) (replayFor target) C)).mp hSat

/-- Proof-level package for the nonempty-clause branch.  The data witnesses
remain under a proposition because `Set.Finite` stores its exact enumeration
in `Prop`. -/
def ClauseSentenceCertificate {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (S : FOClause L hNoEq → Prop) : Prop :=
  ∃ (head : FOClause L hNoEq) (tail : List (FOClause L hNoEq)),
    (ClauseSentenceProperties (hNoEq := by all_goals exact hNoEq)) A S head tail

/-- A finite unsatisfiable predicate-valued clause set either already
contains the empty clause, or has an exact nonempty enumeration whose
canonical universal sentence carries all properties needed by the Herbrand
route.  The result remains in `Prop`: `Set.Finite` stores its exact list
enumeration propositionally and does not provide an executable extractor. -/
theorem finite_unsatisfiable_empty_or_clauseSentence {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (A : FormulaN L) (S : FOClause L hNoEq → Prop)
    (hFinite : Set.Finite S)
    (hUnsat : (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) S) :
    S [] ∨ (ClauseSentenceCertificate (hNoEq := by all_goals exact hNoEq)) A S := by
  obtain ⟨clauses, hExact⟩ := hFinite
  by_cases hEmpty : ([] : FOClause L hNoEq) ∈ clauses
  · exact Or.inl ((hExact []).mpr hEmpty)
  · have hSourceWithoutEmpty : ¬ S [] :=
      fun h => hEmpty ((hExact []).mp h)
    cases clauses with
    | nil =>
      exfalso
      apply hUnsat
      let M : Structure L := {
        carrier := Unit
        carrierNonempty := ⟨()⟩
        interpFunc := fun _ _ => ()
        interpConst := fun _ => ()
        interpPred := fun _ _ => False
      }
      refine ⟨M, ?_⟩
      intro C hSC
      have hMem : C ∈ ([] : List (FOClause L hNoEq)) := (hExact C).mp hSC
      exact (List.not_mem_nil hMem).elim
    | cons head tail =>
      have hNonempty : ∀ C ∈ head :: tail, C ≠ [] := by
        intro C hC hNil
        subst C
        exact hEmpty hC
      have hMatrixQF :=
        (clauseMatrix_isQuantifierFree (hNoEq := by all_goals exact hNoEq)) A head tail hNonempty
      have hMatrixNNF :=
        (clauseMatrix_isNNF (hNoEq := by all_goals exact hNoEq)) A head tail hNonempty
      have hMatrixNoEq :=
        (clauseMatrix_noEq (hNoEq := hNoEq)) A head tail hNonempty
      have hClosed : FormulaN.isClosed ((clauseSentence (hNoEq := by all_goals exact hNoEq)) A head tail) := by
        apply prependAlls_isClosed_of_cover
        exact (clauseVariablePrefix_covers_matrix (hNoEq := by all_goals exact hNoEq)) A head tail
      refine Or.inr ⟨head, tail, {
        source_exact := hExact
        source_without_empty := hSourceWithoutEmpty
        language_without_equality := hNoEq
        clauses_nonempty := hNonempty
        prefix_exact := (mem_clauseVariablePrefix_iff (hNoEq := by all_goals exact hNoEq)) A head tail
        prefix_nodup := (clauseVariablePrefix_nodup (hNoEq := by all_goals exact hNoEq)) A head tail
        matrix_quantifier_free := hMatrixQF
        matrix_nnf := hMatrixNNF
        sentence_nnf := prependAlls_isNNF _ _ hMatrixNNF
        sentence_no_equality := prependAlls_noEq _ _ hMatrixNoEq
        sentence_closed := hClosed
        sentence_rectified :=
          (clauseSentence_isRectified (hNoEq := by all_goals exact hNoEq)) A head tail hNonempty
        sentence_universal_prenex :=
          prependAlls_isUniversalPrenex _ _ hMatrixQF
        sentence_full_prefix :=
          stripAllPrenex_prependAlls_eq _ _ hMatrixQF
        sentence_unsatisfiable :=
          (clauseSentence_isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) A S head tail hExact hUnsat
      }⟩

end LCS.FOResolution.Method.HerbrandBridge
