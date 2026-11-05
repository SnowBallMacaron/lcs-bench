import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.Model
import LCS.FirstOrder.Gentzen.Hintikka.SearchClosure

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Theorem 5.5.1 (companion): Maximum bound variable index + 1 in a FormulaN. All bound variable
indices v satisfy v < formulaMaxBVN A. Returns 0 for atomic formulas. -/
def formulaMaxBVN {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg A => formulaMaxBVN A
  | .conj A B | .disj A B | .impl A B => max (formulaMaxBVN A) (formulaMaxBVN B)
  | .all x A | .ex x A => max (x + 1) (formulaMaxBVN A)

/-- Theorem 5.5.1 (companion): Maximum bound variable index + 1 across all formulas in a sequent. -/
def seqMaxBVN {L : Language} (seq : Sequent L) : Nat :=
  (seq.antecedent ++ seq.succedent).foldl (fun acc A => max acc (formulaMaxBVN A)) 0

/-- Bound variable indices are strictly less than formulaMaxBVN. -/
theorem formulaBVN_lt_formulaMaxBVN {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v ∈ formulaBVN A) : v < formulaMaxBVN A := by
  induction A with
  | predN _ _ | eq_ _ _ _ => exact absurd hv id
  | neg A ih => exact ih hv
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    rcases hv with h | h
    · exact Nat.lt_of_lt_of_le (ihA h) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ihB h) (Nat.le_max_right _ _)
  | all x A ih | ex x A ih =>
    rcases hv with h | h
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)
    · have : v = x := h; simp only [formulaMaxBVN]; omega

theorem foldl_max_bv_le_init {L : Language} (ls : List (FormulaN L)) (init : Nat) :
    init ≤ ls.foldl (fun acc A => max acc (formulaMaxBVN A)) init := by
-- BEGIN PROOF
  induction ls generalizing init with
  | nil => exact Nat.le_refl _
  | cons _ tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_bv_mem_le {L : Language} (ls : List (FormulaN L)) (init : Nat)
    (A : FormulaN L) (hA : A ∈ ls) :
    formulaMaxBVN A ≤ ls.foldl (fun acc B => max acc (formulaMaxBVN B)) init := by
-- BEGIN PROOF
  induction ls generalizing init with
  | nil => cases hA
  | cons _ tl ih =>
    cases hA with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_bv_le_init tl _)
    | tail _ htl => exact ih _ htl

/-- Theorem 5.5.1 (companion): Bound variable index is bounded by seqMaxBVN + 1. -/
theorem seqBV_lt_seqMaxBVN {L : Language} (seq : Sequent L) (v : Nat)
    (A : FormulaN L) (hA : A ∈ (seq.antecedent ++ seq.succedent))
    (hv : v ∈ formulaBVN A) : v < seqMaxBVN seq + 1 := by
-- BEGIN PROOF
  have h1 := formulaBVN_lt_formulaMaxBVN A v hv
  have h2 := foldl_max_bv_mem_le (seq.antecedent ++ seq.succedent) 0 A hA
  simp only [seqMaxBVN]; omega

/-- safeTermsN nonempty: `Term.var (seqMaxBVN seq + 1)` is a safe term
because its only free variable (`seqMaxBVN seq + 1`) exceeds every
bound variable index in the sequent. -/
theorem safeTermsN_isGenTermAlg_nonempty {L : Language} (seq : Sequent L) :
    ∃ t, t ∈ safeTermsN seq := by
-- BEGIN PROOF
  refine ⟨Term.var (seqMaxBVN seq + 1), fun v hv A hA hbv => ?_⟩
  have : v = seqMaxBVN seq + 1 := hv; subst this
  exact absurd (seqBV_lt_seqMaxBVN seq _ A hA hbv) (Nat.lt_irrefl _)

/-- safeTermsN is a generated term algebra. -/
noncomputable def safeTermsN_isGenTermAlg {L : Language} (seq : Sequent L) :
    IsGeneratedTermAlgebra L (safeTermsN seq) := {
  nonempty := safeTermsN_isGenTermAlg_nonempty seq
  closedConst := fun c v hv => absurd hv id
  closedFunc := fun f ts hall v hv A hA =>
    let ⟨i, hi⟩ := hv; hall i v hi A hA
  closedSubterm := fun f ts ht i v hv A hA =>
    ht v ⟨i, hv⟩ A hA
}

/-- Term.var (freshBase + k) is in safeTermsN for any SearchTreeData.
Uses freshBase_bound to show the variable index exceeds all bound
variable indices in the sequent. -/
theorem freshVar_in_safeTermsN {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq) (k : Nat) :
    Term.var (w.freshBase + k) ∈ safeTermsN seq := by
-- BEGIN PROOF
  intro v hv A hA hbv
  -- v ∈ termFV (Term.var (freshBase + k)) means v = freshBase + k
  have hveq : v = w.freshBase + k := hv
  subst hveq
  -- v ∈ formulaBVN A means v < freshBase by freshBase_bound
  have := w.freshBase_bound (w.freshBase + k) A hA hbv
  omega

/-- If no free variable of t is a bound variable of A, then t is free
for x in A. Key lemma for Hintikka set condition H6. -/
theorem isFreeForN_of_bv_disjoint {L : Language} (t : Term L) (x : Nat) (A : FormulaN L)
    (h : ∀ v, v ∈ termFV t → v ∉ formulaBVN A) : isFreeForN t x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => trivial
  | neg A ih => exact ih (fun v hv => h v hv)
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    exact ⟨ihA (fun v hv hm => h v hv (Or.inl hm)),
           ihB (fun v hv hm => h v hv (Or.inr hm))⟩
  | all y A ih | ex y A ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨fun hv => h y hv (Or.inr rfl),
                     ih (fun v hv hm => h v hv (Or.inl hm))⟩

/-- Bound variables are preserved (not increased) by substitution. -/
theorem formulaBVN_formulaSubstN {L : Language} (A : FormulaN L) (t : Term L)
    (x : Nat) (v : Nat) :
    v ∈ formulaBVN (formulaSubstN A t x) → v ∈ formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => exact id
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    intro hv; rcases hv with h | h
    · exact Or.inl (ihA h)
    · exact Or.inr (ihB h)
  | all y A ih | ex y A ih =>
    intro hv
    simp only [formulaSubstN] at hv
    split at hv
    · simp only [formulaBVN] at hv ⊢
      rcases hv with h | h
      · exact Or.inl (ih h)
      · exact Or.inr h
    · exact hv

/-- Property: all BV in a sequent trace to BV of the root sequent. -/
def seqBVinRoot {L : Language} (root cur : Sequent L) : Prop :=
  ∀ A ∈ (cur.antecedent ++ cur.succedent), ∀ v ∈ formulaBVN A,
    ∃ B ∈ (root.antecedent ++ root.succedent), v ∈ formulaBVN B

/-- BV of decomposeAntFormula outputs trace to BV of the input.
Each decomposition rule produces subformulas or substitution instances
whose BV ⊆ parent's BV. -/
theorem decomposeAntFormula_bv_subset {L : Language}
    (A : FormulaN L) (t_c t_d : Term L) (X : FormulaN L) (v : Nat)
    (hBV : v ∈ formulaBVN X)
    (hX : X ∈ (decomposeAntFormula A t_c t_d).1 ∨ X ∈ (decomposeAntFormula A t_c t_d).2) :
    v ∈ formulaBVN A := by
-- BEGIN PROOF
  cases A with
  | conj P Q =>
    simp [decomposeAntFormula] at hX
    rcases hX with rfl | rfl
    · simp [formulaBVN]; exact Or.inl hBV
    · simp [formulaBVN]; exact Or.inr hBV
  | disj _ _ => simp [decomposeAntFormula] at hX
  | impl _ _ => simp [decomposeAntFormula] at hX
  | neg P =>
    simp [decomposeAntFormula] at hX; subst hX
    simp [formulaBVN]; exact hBV
  | all x B =>
    simp [decomposeAntFormula] at hX; subst hX
    simp [formulaBVN]; exact Or.inl (formulaBVN_formulaSubstN B t_c x v hBV)
  | ex x B =>
    simp [decomposeAntFormula] at hX; subst hX
    simp [formulaBVN]; exact Or.inl (formulaBVN_formulaSubstN B t_d x v hBV)
  | predN _ _ => simp [decomposeAntFormula] at hX
  | eq_ _ _ _ => simp [decomposeAntFormula] at hX

/-- BV of decomposeSuccFormula outputs trace to BV of the input. -/
theorem decomposeSuccFormula_bv_subset {L : Language}
    (B : FormulaN L) (t_c t_d : Term L) (X : FormulaN L) (v : Nat)
    (hBV : v ∈ formulaBVN X)
    (hX : X ∈ (decomposeSuccFormula B t_c t_d).1 ∨ X ∈ (decomposeSuccFormula B t_c t_d).2) :
    v ∈ formulaBVN B := by
-- BEGIN PROOF
  cases B with
  | conj _ _ => simp [decomposeSuccFormula] at hX
  | disj P Q =>
    simp [decomposeSuccFormula] at hX
    rcases hX with rfl | rfl
    · simp [formulaBVN]; exact Or.inl hBV
    · simp [formulaBVN]; exact Or.inr hBV
  | impl P Q =>
    simp [decomposeSuccFormula] at hX
    rcases hX with rfl | rfl
    · simp [formulaBVN]; exact Or.inl hBV
    · simp [formulaBVN]; exact Or.inr hBV
  | neg P =>
    simp [decomposeSuccFormula] at hX; subst hX
    simp [formulaBVN]; exact hBV
  | ex x A =>
    simp [decomposeSuccFormula] at hX; subst hX
    simp [formulaBVN]; exact Or.inl (formulaBVN_formulaSubstN A t_c x v hBV)
  | all x A =>
    simp [decomposeSuccFormula] at hX; subst hX
    simp [formulaBVN]; exact Or.inl (formulaBVN_formulaSubstN A t_d x v hBV)
  | predN _ _ => simp [decomposeSuccFormula] at hX
  | eq_ _ _ _ => simp [decomposeSuccFormula] at hX

/-- BV of typeBCompAnt outputs trace to BV of the input. -/
theorem typeBCompAnt_bv_subset {L : Language}
    (A : FormulaN L) (bit : Nat) (X : FormulaN L) (v : Nat)
    (hBV : v ∈ formulaBVN X)
    (hX : X ∈ (typeBCompAnt A bit).1 ∨ X ∈ (typeBCompAnt A bit).2) :
    v ∈ formulaBVN A := by
-- BEGIN PROOF
  cases A with
  | disj P Q =>
    simp [typeBCompAnt] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaBVN]
    · exact Or.inl hBV
    · exact Or.inr hBV
  | impl P Q =>
    simp [typeBCompAnt] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaBVN]
    · exact Or.inl hBV
    · exact Or.inr hBV
  | conj _ _ => simp [typeBCompAnt] at hX
  | neg _ => simp [typeBCompAnt] at hX
  | all _ _ => simp [typeBCompAnt] at hX
  | ex _ _ => simp [typeBCompAnt] at hX
  | predN _ _ => simp [typeBCompAnt] at hX
  | eq_ _ _ _ => simp [typeBCompAnt] at hX

/-- BV of typeBCompSucc outputs trace to BV of the input. -/
theorem typeBCompSucc_bv_subset {L : Language}
    (B : FormulaN L) (bit : Nat) (X : FormulaN L) (v : Nat)
    (hBV : v ∈ formulaBVN X)
    (hX : X ∈ (typeBCompSucc B bit).1 ∨ X ∈ (typeBCompSucc B bit).2) :
    v ∈ formulaBVN B := by
-- BEGIN PROOF
  cases B with
  | conj P Q =>
    simp [typeBCompSucc] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaBVN]
    · exact Or.inl hBV
    · exact Or.inr hBV
  | disj _ _ => simp [typeBCompSucc] at hX
  | impl _ _ => simp [typeBCompSucc] at hX
  | neg _ => simp [typeBCompSucc] at hX
  | all _ _ => simp [typeBCompSucc] at hX
  | ex _ _ => simp [typeBCompSucc] at hX
  | predN _ _ => simp [typeBCompSucc] at hX
  | eq_ _ _ _ => simp [typeBCompSucc] at hX

/-- searchClosureStep1 preserves seqBVinRoot. -/
theorem searchClosureStep1_bvInRoot {L : Language}
    (root prev : Sequent L) (t_c t_d : Term L)
    (h : seqBVinRoot root prev) :
    seqBVinRoot root (searchClosureStep1 prev t_c t_d) := by
-- BEGIN PROOF
  intro X hX v hv
  simp only [searchClosureStep1, List.mem_append] at hX
  rcases hX with ((hX1 | hX2) | hX3) | ((hX4 | hX5) | hX6)
  · exact h X (List.mem_append_left _ hX1) v hv
  · simp [collectDecompAnt, List.mem_flatMap] at hX2
    obtain ⟨F, hF, hXF⟩ := hX2
    exact h F (List.mem_append_left _ hF) v (decomposeAntFormula_bv_subset F t_c t_d X v hv (Or.inl hXF))
  · simp [collectDecompSuccAnt, List.mem_flatMap] at hX3
    obtain ⟨F, hF, hXF⟩ := hX3
    exact h F (List.mem_append_right _ hF) v (decomposeSuccFormula_bv_subset F t_c t_d X v hv (Or.inl hXF))
  · exact h X (List.mem_append_right _ hX4) v hv
  · simp [collectDecompAntSucc, List.mem_flatMap] at hX5
    obtain ⟨F, hF, hXF⟩ := hX5
    exact h F (List.mem_append_left _ hF) v (decomposeAntFormula_bv_subset F t_c t_d X v hv (Or.inr hXF))
  · simp [collectDecompSucc, List.mem_flatMap] at hX6
    obtain ⟨G, hG, hXG⟩ := hX6
    exact h G (List.mem_append_right _ hG) v (decomposeSuccFormula_bv_subset G t_c t_d X v hv (Or.inr hXG))

/-- searchClosureStep preserves seqBVinRoot. -/
theorem searchClosureStep_bvInRoot {L : Language}
    (root prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (h : seqBVinRoot root prev) :
    seqBVinRoot root (searchClosureStep prev terms t_d) := by
-- BEGIN PROOF
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact h
  | cons hd tl ih => exact ih _ (searchClosureStep1_bvInRoot root prev hd t_d h)

/-- branchStep preserves seqBVinRoot. -/
theorem branchStep_bvInRoot {L : Language} [Countable (Term L)]
    (root prev : Sequent L) (depth freshBase bit : Nat)
    (rootSeq : Sequent L)
    (h : seqBVinRoot root prev) :
    seqBVinRoot root (branchStep prev depth freshBase bit rootSeq) := by
-- BEGIN PROOF
  let linear := searchClosureStep prev
    (branchTerms rootSeq depth freshBase)
    (Term.var (freshBase + depth))
  have hLinBV : seqBVinRoot root linear :=
    searchClosureStep_bvInRoot root prev _ _ h
  intro X hX v hv
  simp only [branchStep, List.mem_append] at hX
  rcases hX with (hLin | hBr) | (hLin | hBr)
  · -- X in linear.antecedent
    exact hLinBV X (List.mem_append_left _ hLin) v hv
  · -- X in collectBranchAntNew prev.antecedent bit
    simp [collectBranchAntNew, List.mem_flatMap] at hBr
    obtain ⟨F, hF, hXF⟩ := hBr
    exact h F (List.mem_append_left _ hF) v
      (typeBCompAnt_bv_subset F bit X v hv (Or.inl hXF))
  · -- X in linear.succedent
    exact hLinBV X (List.mem_append_right _ hLin) v hv
  · -- X in collectBranchSuccNew
    simp [collectBranchSuccNew, List.mem_append, List.mem_flatMap] at hBr
    rcases hBr with ⟨F, hF, hXF⟩ | ⟨G, hG, hXG⟩
    · exact h F (List.mem_append_left _ hF) v
        (typeBCompAnt_bv_subset F bit X v hv (Or.inr hXF))
    · exact h G (List.mem_append_right _ hG) v
        (typeBCompSucc_bv_subset G bit X v hv (Or.inr hXG))

/-- branchingNodeSeqF preserves seqBVinRoot at all depths. -/
theorem branchingNodeSeqF_bvInRoot {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat) (n : Nat) :
    seqBVinRoot seq (branchingNodeSeqF seq freshBase f n) := by
-- BEGIN PROOF
  induction n with
  | zero => intro A hA v hv; exact ⟨A, hA, hv⟩
  | succ k ih =>
    simp only [branchingNodeSeqF]
    exact branchStep_bvInRoot seq _ k freshBase (f k) seq ih

-- ===================================================================
-- FV tracking: termFV_termSubst, formulaFVN_formulaSubstN
-- ===================================================================

/-- FV of term substitution: if y ∈ FV(termSubst t s x), then either
y was already in FV(t) with y ≠ x, or x was in FV(t) and y ∈ FV(s). -/
theorem termFV_termSubst {L : Language} (t s : Term L) (x y : Nat)
    (hy : y ∈ termFV (termSubst t s x)) :
    (y ∈ termFV t ∧ y ≠ x) ∨ (x ∈ termFV t ∧ y ∈ termFV s) := by
-- BEGIN PROOF
  induction t with
  | var i =>
    simp only [termSubst] at hy; split at hy
    · next h => exact Or.inr ⟨h.symm ▸ rfl, hy⟩
    · next h => have hyi : y = i := hy; exact Or.inl ⟨hyi ▸ rfl, hyi ▸ h⟩
  | const c => exact absurd hy id
  | func f ts ih =>
    simp only [termSubst, termFV] at hy; obtain ⟨j, hj⟩ := hy
    rcases ih j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨j, h1⟩, h2⟩
    · exact Or.inr ⟨⟨j, h1⟩, h2⟩

/-- FV of formulaSubstN: if y ∈ FV(A[t/x]), then either y ∈ FV(A) with
y ≠ x, or y ∈ FV(t). This tracks how free variables flow through
substitution. -/
theorem formulaFVN_formulaSubstN {L : Language} (A : FormulaN L) (t : Term L) (x y : Nat)
    (hy : y ∈ formulaFVN (formulaSubstN A t x)) :
    (y ∈ formulaFVN A ∧ y ≠ x) ∨ y ∈ termFV t := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢; obtain ⟨j, hj⟩ := hy
    rcases termFV_termSubst (ts j) t x y hj with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact Or.inl ⟨⟨j, h1⟩, h2⟩
    · exact Or.inr h2
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢
    rcases hy with h1 | h2
    · rcases termFV_termSubst t1 t x y h1 with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr h2
    · rcases termFV_termSubst t2 t x y h2 with ⟨h1, h2⟩ | ⟨_, h2⟩
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr h2
  | neg A ih => simp only [formulaSubstN, formulaFVN] at hy ⊢; exact ih hy
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hy ⊢; rcases hy with h | h
    · rcases ihA h with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr h1
    · rcases ihB h with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr h1
  | all i A ih | ex i A ih =>
    simp only [formulaSubstN] at hy; split at hy
    · next hne =>
      simp only [formulaFVN] at hy ⊢; obtain ⟨hA, hni⟩ := hy
      rcases ih hA with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨⟨h1, hni⟩, h2⟩
      · exact Or.inr h1
    · next hne =>
      have hxi : x = i := by simp [bne] at hne; exact hne
      simp only [formulaFVN] at hy ⊢
      exact Or.inl ⟨hy, fun heq => hy.2 (hxi ▸ heq)⟩

-- ===================================================================
-- seqFVavoidsBV: FV of path formulas avoid BV of root
-- ===================================================================

/-- Property: all FV in a sequent avoid BV of the root sequent.
Analogous to seqBVinRoot but tracks free variables instead of bound. -/
def seqFVavoidsBV {L : Language} (root cur : Sequent L) : Prop :=
  ∀ A ∈ (cur.antecedent ++ cur.succedent), ∀ y ∈ formulaFVN A,
    ∀ B ∈ (root.antecedent ++ root.succedent), y ∉ formulaBVN B

/-- FV of decomposeAntFormula outputs trace to FV(parent) or FV(terms).
If y ∈ FV(X) where X is a decomposition output, then either
y ∈ FV(A) (the parent formula) or y ∈ FV(t_c) or y ∈ FV(t_d). -/
theorem decomposeAntFormula_fv_subset {L : Language}
    (A : FormulaN L) (t_c t_d : Term L) (X : FormulaN L) (y : Nat)
    (hFV : y ∈ formulaFVN X)
    (hX : X ∈ (decomposeAntFormula A t_c t_d).1 ∨ X ∈ (decomposeAntFormula A t_c t_d).2) :
    y ∈ formulaFVN A ∨ y ∈ termFV t_c ∨ y ∈ termFV t_d := by
-- BEGIN PROOF
  cases A with
  | conj P Q =>
    simp [decomposeAntFormula] at hX
    rcases hX with rfl | rfl
    · exact Or.inl (Or.inl hFV)
    · exact Or.inl (Or.inr hFV)
  | disj _ _ => simp [decomposeAntFormula] at hX
  | impl _ _ => simp [decomposeAntFormula] at hX
  | neg P => simp [decomposeAntFormula] at hX; subst hX; exact Or.inl hFV
  | all x B =>
    simp [decomposeAntFormula] at hX; subst hX
    rcases formulaFVN_formulaSubstN B t_c x y hFV with ⟨h1, h2⟩ | h1
    · exact Or.inl (show y ∈ formulaFVN (.all x B) from ⟨h1, h2⟩)
    · exact Or.inr (Or.inl h1)
  | ex x B =>
    simp [decomposeAntFormula] at hX; subst hX
    rcases formulaFVN_formulaSubstN B t_d x y hFV with ⟨h1, h2⟩ | h1
    · exact Or.inl (show y ∈ formulaFVN (.ex x B) from ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h1)
  | predN _ _ => simp [decomposeAntFormula] at hX
  | eq_ _ _ _ => simp [decomposeAntFormula] at hX

/-- FV of decomposeSuccFormula outputs trace to FV(parent) or FV(terms). -/
theorem decomposeSuccFormula_fv_subset {L : Language}
    (B : FormulaN L) (t_c t_d : Term L) (X : FormulaN L) (y : Nat)
    (hFV : y ∈ formulaFVN X)
    (hX : X ∈ (decomposeSuccFormula B t_c t_d).1 ∨ X ∈ (decomposeSuccFormula B t_c t_d).2) :
    y ∈ formulaFVN B ∨ y ∈ termFV t_c ∨ y ∈ termFV t_d := by
-- BEGIN PROOF
  cases B with
  | conj _ _ => simp [decomposeSuccFormula] at hX
  | disj P Q =>
    simp [decomposeSuccFormula] at hX
    rcases hX with rfl | rfl
    · exact Or.inl (Or.inl hFV)
    · exact Or.inl (Or.inr hFV)
  | impl P Q =>
    simp [decomposeSuccFormula] at hX
    rcases hX with rfl | rfl
    · exact Or.inl (Or.inl hFV)
    · exact Or.inl (Or.inr hFV)
  | neg P => simp [decomposeSuccFormula] at hX; subst hX; exact Or.inl hFV
  | ex x A =>
    simp [decomposeSuccFormula] at hX; subst hX
    rcases formulaFVN_formulaSubstN A t_c x y hFV with ⟨h1, h2⟩ | h1
    · exact Or.inl (show y ∈ formulaFVN (.ex x A) from ⟨h1, h2⟩)
    · exact Or.inr (Or.inl h1)
  | all x A =>
    simp [decomposeSuccFormula] at hX; subst hX
    rcases formulaFVN_formulaSubstN A t_d x y hFV with ⟨h1, h2⟩ | h1
    · exact Or.inl (show y ∈ formulaFVN (.all x A) from ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h1)
  | predN _ _ => simp [decomposeSuccFormula] at hX
  | eq_ _ _ _ => simp [decomposeSuccFormula] at hX

/-- FV of typeBCompAnt outputs are a subset of FV(parent). -/
theorem typeBCompAnt_fv_subset {L : Language}
    (A : FormulaN L) (bit : Nat) (X : FormulaN L) (y : Nat)
    (hFV : y ∈ formulaFVN X)
    (hX : X ∈ (typeBCompAnt A bit).1 ∨ X ∈ (typeBCompAnt A bit).2) :
    y ∈ formulaFVN A := by
-- BEGIN PROOF
  cases A with
  | disj P Q =>
    simp [typeBCompAnt] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaFVN]
    · exact Or.inl hFV
    · exact Or.inr hFV
  | impl P Q =>
    simp [typeBCompAnt] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaFVN]
    · exact Or.inl hFV
    · exact Or.inr hFV
  | conj _ _ => simp [typeBCompAnt] at hX
  | neg _ => simp [typeBCompAnt] at hX
  | all _ _ => simp [typeBCompAnt] at hX
  | ex _ _ => simp [typeBCompAnt] at hX
  | predN _ _ => simp [typeBCompAnt] at hX
  | eq_ _ _ _ => simp [typeBCompAnt] at hX

/-- FV of typeBCompSucc outputs are a subset of FV(parent). -/
theorem typeBCompSucc_fv_subset {L : Language}
    (B : FormulaN L) (bit : Nat) (X : FormulaN L) (y : Nat)
    (hFV : y ∈ formulaFVN X)
    (hX : X ∈ (typeBCompSucc B bit).1 ∨ X ∈ (typeBCompSucc B bit).2) :
    y ∈ formulaFVN B := by
-- BEGIN PROOF
  cases B with
  | conj P Q =>
    simp [typeBCompSucc] at hX
    split at hX <;> simp at hX <;> subst hX <;> simp [formulaFVN]
    · exact Or.inl hFV
    · exact Or.inr hFV
  | disj _ _ => simp [typeBCompSucc] at hX
  | impl _ _ => simp [typeBCompSucc] at hX
  | neg _ => simp [typeBCompSucc] at hX
  | all _ _ => simp [typeBCompSucc] at hX
  | ex _ _ => simp [typeBCompSucc] at hX
  | predN _ _ => simp [typeBCompSucc] at hX
  | eq_ _ _ _ => simp [typeBCompSucc] at hX

/-- searchClosureStep1 preserves seqFVavoidsBV, assuming both t_c and
t_d have FV that avoid BV of root. -/
theorem searchClosureStep1_fvSafe {L : Language}
    (root prev : Sequent L) (t_c t_d : Term L)
    (h : seqFVavoidsBV root prev)
    (htc : ∀ v ∈ termFV t_c, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B)
    (htd : ∀ v ∈ termFV t_d, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B) :
    seqFVavoidsBV root (searchClosureStep1 prev t_c t_d) := by
-- BEGIN PROOF
  intro X hX y hFV B hB
  simp only [searchClosureStep1, List.mem_append] at hX
  rcases hX with ((hX1 | hX2) | hX3) | ((hX4 | hX5) | hX6)
  · exact h X (List.mem_append_left _ hX1) y hFV B hB
  · simp [collectDecompAnt, List.mem_flatMap] at hX2
    obtain ⟨F, hF, hXF⟩ := hX2
    rcases decomposeAntFormula_fv_subset F t_c t_d X y hFV (Or.inl hXF) with hF' | htc' | htd'
    · exact h F (List.mem_append_left _ hF) y hF' B hB
    · exact htc y htc' B hB
    · exact htd y htd' B hB
  · simp [collectDecompSuccAnt, List.mem_flatMap] at hX3
    obtain ⟨G, hG, hXG⟩ := hX3
    rcases decomposeSuccFormula_fv_subset G t_c t_d X y hFV (Or.inl hXG) with hG' | htc' | htd'
    · exact h G (List.mem_append_right _ hG) y hG' B hB
    · exact htc y htc' B hB
    · exact htd y htd' B hB
  · exact h X (List.mem_append_right _ hX4) y hFV B hB
  · simp [collectDecompAntSucc, List.mem_flatMap] at hX5
    obtain ⟨F, hF, hXF⟩ := hX5
    rcases decomposeAntFormula_fv_subset F t_c t_d X y hFV (Or.inr hXF) with hF' | htc' | htd'
    · exact h F (List.mem_append_left _ hF) y hF' B hB
    · exact htc y htc' B hB
    · exact htd y htd' B hB
  · simp [collectDecompSucc, List.mem_flatMap] at hX6
    obtain ⟨G, hG, hXG⟩ := hX6
    rcases decomposeSuccFormula_fv_subset G t_c t_d X y hFV (Or.inr hXG) with hG' | htc' | htd'
    · exact h G (List.mem_append_right _ hG) y hG' B hB
    · exact htc y htc' B hB
    · exact htd y htd' B hB

/-- searchClosureStep preserves seqFVavoidsBV, when all terms in the
list and the eigenvariable have safe FV. -/
theorem searchClosureStep_fvSafe {L : Language}
    (root prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (h : seqFVavoidsBV root prev)
    (hterms : ∀ t ∈ terms, ∀ v ∈ termFV t, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B)
    (htd : ∀ v ∈ termFV t_d, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B) :
    seqFVavoidsBV root (searchClosureStep prev terms t_d) := by
-- BEGIN PROOF
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact h
  | cons hd tl ih =>
    have h1 : seqFVavoidsBV root (searchClosureStep1 prev hd t_d) :=
      searchClosureStep1_fvSafe root prev hd t_d h
        (hterms hd (List.Mem.head tl))
        htd
    exact ih _ h1 (fun t ht => hterms t (List.Mem.tail hd ht))

/-- branchStep preserves seqFVavoidsBV, when branchTerms and the
eigenvariable have safe FV. -/
theorem branchStep_fvSafe {L : Language} [Countable (Term L)]
    (root prev : Sequent L) (depth freshBase bit : Nat)
    (rootSeq : Sequent L)
    (h : seqFVavoidsBV root prev)
    (hTermsSafe : ∀ t ∈ branchTerms rootSeq depth freshBase,
      ∀ v ∈ termFV t, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B)
    (hEigen : ∀ v ∈ termFV (show Term L from Term.var (freshBase + depth)),
      ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B) :
    seqFVavoidsBV root (branchStep prev depth freshBase bit rootSeq) := by
-- BEGIN PROOF
  let linear := searchClosureStep prev
    (branchTerms rootSeq depth freshBase)
    (Term.var (freshBase + depth))
  have hLinFV : seqFVavoidsBV root linear :=
    searchClosureStep_fvSafe root prev _ _ h hTermsSafe hEigen
  intro X hX y hFV B hB
  simp only [branchStep, List.mem_append] at hX
  rcases hX with (hLin | hBr) | (hLin | hBr)
  · exact hLinFV X (List.mem_append_left _ hLin) y hFV B hB
  · simp [collectBranchAntNew, List.mem_flatMap] at hBr
    obtain ⟨F, hF, hXF⟩ := hBr
    exact h F (List.mem_append_left _ hF) y
      (typeBCompAnt_fv_subset F bit X y hFV (Or.inl hXF)) B hB
  · exact hLinFV X (List.mem_append_right _ hLin) y hFV B hB
  · simp [collectBranchSuccNew, List.mem_append, List.mem_flatMap] at hBr
    rcases hBr with ⟨F, hF, hXF⟩ | ⟨G, hG, hXG⟩
    · exact h F (List.mem_append_left _ hF) y
        (typeBCompAnt_fv_subset F bit X y hFV (Or.inr hXF)) B hB
    · exact h G (List.mem_append_right _ hG) y
        (typeBCompSucc_fv_subset G bit X y hFV (Or.inr hXG)) B hB

/-- branchTerms FV are safe when rootSeq = root: terms in branchTerms are
filtered to safeTermsN root, so their FV avoids BV(root). The
eigenvariable Term.var(freshBase+depth) is also safe when freshBase > BV. -/
theorem branchTerms_fv_safe {L : Language} [Countable (Term L)]
    (root : Sequent L) (depth freshBase : Nat)
    (hFB : ∀ v, ∀ A ∈ (root.antecedent ++ root.succedent), v ∈ formulaBVN A → v < freshBase) :
    ∀ t ∈ branchTerms root depth freshBase,
      ∀ v ∈ termFV t, ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B := by
-- BEGIN PROOF
  intro t ht v hv B hB
  simp only [branchTerms, List.mem_append, List.mem_filter, List.mem_singleton] at ht
  rcases ht with ⟨_, htSafe⟩ | rfl
  · -- t passes the safeTermsN filter
    have : ∀ (p : Prop), Decidable p := Classical.propDecidable
    have hSafe : t ∈ safeTermsN root := by
      simp [decide_eq_true_eq] at htSafe; exact htSafe
    exact hSafe v hv B hB
  · -- t = Term.var (freshBase + depth), so FV = {freshBase + depth}
    simp [termFV] at hv; subst hv
    intro hvB; exact absurd (hFB _ B hB hvB) (by omega)

/-- Eigenvariable Term.var(freshBase+k) has FV that avoids BV(root). -/
theorem eigenvar_fv_safe {L : Language}
    (root : Sequent L) (freshBase k : Nat)
    (hFB : ∀ v, ∀ A ∈ (root.antecedent ++ root.succedent), v ∈ formulaBVN A → v < freshBase) :
    ∀ v ∈ termFV (show Term L from Term.var (freshBase + k)),
      ∀ B ∈ (root.antecedent ++ root.succedent), v ∉ formulaBVN B := by
-- BEGIN PROOF
  intro v hv B hB hvB
  simp [termFV] at hv; subst hv
  exact absurd (hFB _ B hB hvB) (by omega)

/-- branchingNodeSeqF preserves seqFVavoidsBV at all depths, when
the root has crossNoFreeBound and freshBase > all BV. -/
theorem branchingNodeSeqF_fvSafe {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat) (n : Nat)
    (hCross : crossNoFreeBound seq)
    (hFB : ∀ v, ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∈ formulaBVN A → v < freshBase) :
    seqFVavoidsBV seq (branchingNodeSeqF seq freshBase f n) := by
-- BEGIN PROOF
  induction n with
  | zero =>
    -- Base case: branchingNodeSeqF at depth 0 = seq
    intro A hA y hFV B hB
    exact hCross y ⟨A, hA, hFV⟩ B hB
  | succ k ih =>
    simp only [branchingNodeSeqF]
    exact branchStep_fvSafe seq _ k freshBase (f k) seq ih
      (branchTerms_fv_safe seq k freshBase hFB)
      (eigenvar_fv_safe seq freshBase k hFB)

/-- Along an infinite path, the nodeSequent at depth n equals
branchingNodeSeqF seq freshBase f n. Proved by induction using
root_sequent (base) and path_expansion (step). -/
theorem nodeSeq_eq_branchingNodeSeqF {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    (n : Nat) :
    w.nodeSequent (List.ofFn (fun i : Fin n => f i)) (hPath n) =
    branchingNodeSeqF seq w.freshBase f n := by
-- BEGIN PROOF
  induction n with
  | zero => simp [branchingNodeSeqF]; exact w.root_sequent
  | succ k ih =>
    have hexp := w.path_expansion f k hPath
    rw [hexp]; simp only [branchingNodeSeqF]; rw [ih]

/-- Theorem 5.5.1 (companion, H5): isFreeFor holds for quantified formulae along
any infinite path, for terms in safeTermsN. The textbook (section 5.4.7)
only requires isFreeFor for terms in the term algebra H, not all terms.
The restriction to safeTermsN (terms whose free vars avoid bound vars)
makes this provable: BV of path formulas trace back to the root
sequent's BV, and safe terms' FV are disjoint from root BV. -/
theorem searchTree_path_freeFor {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      t ∈ safeTermsN seq →
      (SignedFormula.trueF (FormulaN.all x A) ∈ S ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ S ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ S ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ S) →
      isFreeForN t x A := by
-- BEGIN PROOF
  intro S x A t ht hQ
  -- The formula all/ex x A appears at some depth k along the path.
  -- By path_expansion, nodeSequent at depth k = branchingNodeSeqF seq freshBase f k.
  -- By branchingNodeSeqF_bvInRoot, BV of A trace to root sequent's BV.
  -- Since t ∈ safeTermsN seq, t's FV avoids root BV, hence avoids BV of A.
  -- By isFreeForN_of_bv_disjoint, isFreeForN t x A.
  -- Extract the depth k where the quantified formula first appears.
  have hFormula : ∃ k, ∃ (hk : (List.ofFn (fun i : Fin k => f i)) ∈ w.treeDom.dom),
      (.all x A ∈ (w.nodeSequent _ hk).antecedent ∨
       .all x A ∈ (w.nodeSequent _ hk).succedent ∨
       .ex x A ∈ (w.nodeSequent _ hk).antecedent ∨
       .ex x A ∈ (w.nodeSequent _ hk).succedent) := by
    rcases hQ with ⟨k, hk, hAk⟩ | ⟨k, hk, hAk⟩ | ⟨k, hk, hAk⟩ | ⟨k, hk, hAk⟩
    all_goals (refine ⟨k, hk, ?_⟩)
    · left; rcases hAk with ⟨F, hF, hFeq⟩ | ⟨F, _, hFeq⟩
      · exact SignedFormula.trueF.inj hFeq ▸ hF
      · exact absurd hFeq (by intro h; cases h)
    · right; left; rcases hAk with ⟨F, _, hFeq⟩ | ⟨F, hF, hFeq⟩
      · exact absurd hFeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hFeq ▸ hF
    · right; right; left; rcases hAk with ⟨F, hF, hFeq⟩ | ⟨F, _, hFeq⟩
      · exact SignedFormula.trueF.inj hFeq ▸ hF
      · exact absurd hFeq (by intro h; cases h)
    · right; right; right; rcases hAk with ⟨F, _, hFeq⟩ | ⟨F, hF, hFeq⟩
      · exact absurd hFeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hFeq ▸ hF
  obtain ⟨k, hk, hFormula⟩ := hFormula
  -- Use isFreeForN_of_bv_disjoint: need ∀ v ∈ termFV t, v ∉ formulaBVN A
  apply isFreeForN_of_bv_disjoint
  intro v hv hbv
  -- BV of A is a subset of BV of the quantified formula
  have hbv_quant : ∀ (F : FormulaN L),
      (F = .all x A ∨ F = .ex x A) → v ∈ formulaBVN F := by
    intro F hF; rcases hF with rfl | rfl
    · exact Or.inl hbv  -- BV(.all x A) = BV(A) ∪ {x}, so BV(A) ⊆ BV(.all x A)
    · exact Or.inl hbv  -- BV(.ex x A) = BV(A) ∪ {x}, so BV(A) ⊆ BV(.ex x A)
  -- The quantified formula is in the nodeSequent at depth k.
  -- nodeSequent at depth k = branchingNodeSeqF seq freshBase f k (by path_expansion induction).
  -- By branchingNodeSeqF_bvInRoot, there exists B in root seq with v ∈ BV(B).
  -- Since t ∈ safeTermsN seq, v ∉ BV(B) for all B in seq. Contradiction.
  -- For now, we use path_expansion to relate nodeSequent to branchingNodeSeqF.
  -- The connection requires that nodeSequent along the path matches branchingNodeSeqF.
  -- We establish this by induction using path_expansion.
  -- Get the quantified formula in the combined list of the sequent at depth k
  have hInSeqK : ∃ F ∈ ((w.nodeSequent _ hk).antecedent ++ (w.nodeSequent _ hk).succedent),
      v ∈ formulaBVN F := by
    rcases hFormula with h1 | h2 | h3 | h4
    · exact ⟨.all x A, List.mem_append_left _ h1, Or.inl hbv⟩
    · exact ⟨.all x A, List.mem_append_right _ h2, Or.inl hbv⟩
    · exact ⟨.ex x A, List.mem_append_left _ h3, Or.inl hbv⟩
    · exact ⟨.ex x A, List.mem_append_right _ h4, Or.inl hbv⟩
  obtain ⟨F, hF, hvF⟩ := hInSeqK
  -- Rewrite F's membership via nodeSeq_eq_branchingNodeSeqF
  rw [nodeSeq_eq_branchingNodeSeqF w f hPath k] at hF
  -- By branchingNodeSeqF_bvInRoot, v ∈ BV(B) for some B in root seq
  obtain ⟨B, hB, hvB⟩ := branchingNodeSeqF_bvInRoot seq w.freshBase f k F hF v hvF
  -- Since t ∈ safeTermsN seq and v ∈ termFV t, v ∉ BV(B). Contradiction.
  exact ht v hv B hB hvB

/-- Theorem 5.5.1 (companion, H3): Along any infinite path in the search tree,
for every type-C formula in S and every safe term t (t ∈ safeTermsN seq),
C(t) is in S whenever t is free for its bound variable. Safe terms
include the terms of the occurrence-language algebra used by IsHintikkaSet. -/
theorem searchTree_path_hintikka_typeC {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (c : TypeC L), c.toSigned ∈ S →
      ∀ (t : Term L), t ∈ safeTermsN seq → ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ S := by
-- BEGIN PROOF
  intro S c hc t ht_safe hfree
  cases c with
  | tAll x A =>
    -- trueF (all x A) ∈ S: all x A in antecedent at depth k
    obtain ⟨k, _, hAk⟩ := hc
    have hAnt : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    -- Get j such that enumerate j = t
    obtain ⟨j, hj⟩ := Countable.enumerate_surj t
    -- Work at depth N = max(k, j) where both the formula and t are available
    let N := max k j
    have hAnt_N := path_ant_mono_le w f hPath (Nat.le_max_left k j) _ hAnt
    have hexp := w.path_expansion f N hPath
    -- enumerate j is safe since t = enumerate j and t ∈ safeTermsN seq
    have ht_safe' : Countable.enumerate (α := Term L) j ∈ safeTermsN seq := hj ▸ ht_safe
    open Classical in
    have ht : Countable.enumerate (α := Term L) j ∈ branchTerms seq N w.freshBase := by
      simp only [branchTerms]
      apply List.mem_append_left
      rw [List.mem_filter]
      exact ⟨List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩,
             decide_eq_true_eq.mpr ht_safe'⟩
    have hcomp : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (decomposeAntFormula (.all x A) (Countable.enumerate j) (Term.var (w.freshBase + N))).1 := by
      simp [decomposeAntFormula]
    have hX : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (branchStep (w.nodeSequent _ (hPath N)) N w.freshBase (f N) seq).antecedent :=
      branchStep_decompAnt _ N w.freshBase (f N) seq _ _ hAnt_N ht _ hcomp
    rw [← hexp] at hX; rw [hj] at hX
    exact ⟨N + 1, hPath (N + 1), Or.inl ⟨formulaSubstN A t x, hX, rfl⟩⟩
  | fEx x A =>
    -- falseF (ex x A) ∈ S: ex x A in succedent at depth k
    obtain ⟨k, _, hAk⟩ := hc
    have hSucc : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    obtain ⟨j, hj⟩ := Countable.enumerate_surj t
    let N := max k j
    have hSucc_N := path_succ_mono_le w f hPath (Nat.le_max_left k j) _ hSucc
    have hexp := w.path_expansion f N hPath
    have ht_safe' : Countable.enumerate (α := Term L) j ∈ safeTermsN seq := hj ▸ ht_safe
    open Classical in
    have ht : Countable.enumerate (α := Term L) j ∈ branchTerms seq N w.freshBase := by
      simp only [branchTerms]
      apply List.mem_append_left
      rw [List.mem_filter]
      exact ⟨List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩,
             decide_eq_true_eq.mpr ht_safe'⟩
    have hcomp : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (decomposeSuccFormula (.ex x A) (Countable.enumerate j) (Term.var (w.freshBase + N))).2 := by
      simp [decomposeSuccFormula]
    have hX : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (branchStep (w.nodeSequent _ (hPath N)) N w.freshBase (f N) seq).succedent :=
      branchStep_decompSucc _ N w.freshBase (f N) seq _ _ hSucc_N ht _ hcomp
    rw [← hexp] at hX; rw [hj] at hX
    exact ⟨N + 1, hPath (N + 1), Or.inr ⟨formulaSubstN A t x, hX, rfl⟩⟩

/-- Theorem 5.5.1 (companion, H4): Along any infinite path in the search tree,
for every type-D formula in S, there exists a term t free for its bound
variable such that D(t) is in S. -/
theorem searchTree_path_hintikka_typeD {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (d : TypeD L), d.toSigned ∈ S →
      ∃ (t : Term L), ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S := by
-- BEGIN PROOF
  intro S d hd
  cases d with
  | tEx x A =>
    -- trueF (ex x A) ∈ S: ex x A in antecedent at depth k
    -- Witness: t_d = Term.var (freshBase + k)
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hAnt : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    have hexp := w.path_expansion f k hPath
    have ht : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeAntFormula (.ex x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).1 := by
      simp [decomposeAntFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
      branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt ht _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inr (Or.inl hdQ)))
    exact ⟨Term.var (w.freshBase + k), hfree, k + 1, hPath (k + 1), Or.inl ⟨_, hX, rfl⟩⟩
  | fAll x A =>
    -- falseF (all x A) ∈ S: all x A in succedent at depth k
    -- Witness: t_d = Term.var (freshBase + k)
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hSucc : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    have hexp := w.path_expansion f k hPath
    have ht : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeSuccFormula (.all x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).2 := by
      simp [decomposeSuccFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
      branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc ht _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inl hdQ))
    exact ⟨Term.var (w.freshBase + k), hfree, k + 1, hPath (k + 1), Or.inr ⟨_, hX, rfl⟩⟩

/-- searchTree_path_hintikka_typeD with safeTermsN membership.
The type-D witness Term.var(freshBase+k) is in safeTermsN because
freshBase exceeds all bound variable indices in the root sequent. -/
theorem searchTree_path_hintikka_typeD_safe {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (d : TypeD L), d.toSigned ∈ S →
      ∃ (t : Term L), t ∈ safeTermsN seq ∧ ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S := by
-- BEGIN PROOF
  intro S d hd
  cases d with
  | tEx x A =>
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hAnt : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    have hexp := w.path_expansion f k hPath
    have ht_bt : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeAntFormula (.ex x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).1 := by
      simp [decomposeAntFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
      branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt ht_bt _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inr (Or.inl hdQ)))
    exact ⟨Term.var (w.freshBase + k), freshVar_in_safeTermsN w k, hfree,
           k + 1, hPath (k + 1), Or.inl ⟨_, hX, rfl⟩⟩
  | fAll x A =>
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hSucc : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    have hexp := w.path_expansion f k hPath
    have ht_bt : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeSuccFormula (.all x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).2 := by
      simp [decomposeSuccFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
      branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc ht_bt _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inl hdQ))
    exact ⟨Term.var (w.freshBase + k), freshVar_in_safeTermsN w k, hfree,
           k + 1, hPath (k + 1), Or.inr ⟨_, hX, rfl⟩⟩

/-- Type-D expansion along a search path has a fresh variable witness. -/
theorem searchTree_path_hintikka_typeD_var {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (d : TypeD L), d.toSigned ∈ S →
      ∃ x, Term.var x ∈ safeTermsN seq ∧ ∃ h : isFreeForN (Term.var x) d.var d.body, d.comp (Term.var x) h ∈ S := by
-- BEGIN PROOF
  intro S d hd
  cases d with
  | tEx x A =>
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hAnt : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    have hexp := w.path_expansion f k hPath
    have ht_bt : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeAntFormula (.ex x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).1 := by
      simp [decomposeAntFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
      branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt ht_bt _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inr (Or.inl hdQ)))
    exact ⟨w.freshBase + k, freshVar_in_safeTermsN w k, hfree,
           k + 1, hPath (k + 1), Or.inl ⟨_, hX, rfl⟩⟩
  | fAll x A =>
    have hdQ := hd
    obtain ⟨k, _, hAk⟩ := hd
    have hSucc : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    have hexp := w.path_expansion f k hPath
    have ht_bt : Term.var (w.freshBase + k) ∈ branchTerms seq k w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (decomposeSuccFormula (.all x A) (Term.var (w.freshBase + k)) (Term.var (w.freshBase + k))).2 := by
      simp [decomposeSuccFormula]
    have hX : formulaSubstN A (Term.var (w.freshBase + k)) x ∈
        (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
      branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc ht_bt _ hcomp
    rw [← hexp] at hX
    have hfree := searchTree_path_freeFor w f hPath x A
      (Term.var (w.freshBase + k)) (freshVar_in_safeTermsN w k) (Or.inr (Or.inl hdQ))
    exact ⟨w.freshBase + k, freshVar_in_safeTermsN w k, hfree,
           k + 1, hPath (k + 1), Or.inr ⟨_, hX, rfl⟩⟩

/-- Nodes on an infinite path are never axioms: if a node were an axiom,
axiom_is_leaf would prevent the path from continuing. -/
theorem path_node_not_axiom {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    (n : Nat) : ¬ isAxiom (w.nodeSequent _ (hPath n)) := by
-- BEGIN PROOF
  intro hAx
  have hNoChild := w.axiom_is_leaf _ (hPath n) hAx
  have haddr := ofFn_succ_append f n
  have hChild : (List.ofFn (fun i : Fin n => f i)) ++ [f n] ∈ w.treeDom.dom :=
    haddr ▸ hPath (n + 1)
  exact hNoChild (dom_child_zero w.treeDom _ (f n) hChild)

/-- Theorem 5.5.1 (companion, no equality): No eq_ formula appears along any
infinite path in the search tree. The search procedure is for languages
without equality; eq_ never appears in the input sequent and expansion
rules never introduce it. -/
theorem searchTree_path_no_eq {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
      SignedFormula.trueF (FormulaN.eq_ hL t1 t2) ∉ S ∧
      SignedFormula.falseF (FormulaN.eq_ hL t1 t2) ∉ S := by
-- BEGIN PROOF
  intro S hL t1 t2
  constructor
  · -- trueF (eq_ t1 t2) ∉ S
    intro ⟨n, _hn, hAn⟩
    have hAnt : FormulaN.eq_ hL t1 t2 ∈ (w.nodeSequent _ (hPath n)).antecedent := by
      rcases hAn with ⟨X, hX, hXeq⟩ | ⟨Y, _hY, hYeq⟩
      · exact SignedFormula.trueF.inj hXeq ▸ hX
      · exact absurd hYeq (by intro h; cases h)
    -- node_seqNoEq for non-axiom nodes
    have hne := (w.node_seqNoEq _ (hPath n) (path_node_not_axiom w f hPath n)).1 _ hAnt
    exact absurd hne (by simp [formulaNoEq])
  · -- falseF (eq_ t1 t2) ∉ S
    intro ⟨n, _hn, hAn⟩
    have hSucc : FormulaN.eq_ hL t1 t2 ∈ (w.nodeSequent _ (hPath n)).succedent := by
      rcases hAn with ⟨X, _hX, hXeq⟩ | ⟨Y, hY, hYeq⟩
      · exact absurd hXeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hYeq ▸ hY
    have hne := (w.node_seqNoEq _ (hPath n) (path_node_not_axiom w f hPath n)).2 _ hSucc
    exact absurd hne (by simp [formulaNoEq])

/-- Theorem 5.5.1 (companion, conversion): When the search tree is
finite and the input sequent is valid, it can be converted to a
`GProofTreeExt` proving the sequent (under the §5.4.8 standing
assumption). -/
theorem searchTree_finite_valid_to_proof {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq) :
    w.treeDom.IsFinite → sequentProvableExt seq :=
-- BEGIN PROOF
  fun hFin => w.provable_if_finite hFin

-- ===================================================================
-- infinitePath_yields_hintikkaSet
-- ===================================================================

/-- Safe terms using only symbols of S form a term algebra over L_S. -/
theorem safeReductTerms_isTermAlgebraOver {L : Language} (seq : Sequent L)
    (S : Set (SignedFormula L)) :
    IsTermAlgebraOver L S (fun t => t ∈ safeTermsN seq ∧
      termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S) := by
  refine { nonempty := ?_, symbols := fun _ h => h.2, closedFunc := ?_, closedConst := ?_ }
  · refine ⟨Term.var (seqMaxBVN seq + 1), ?_, ?_, ?_⟩
    · intro v hv A hA hbv
      have hv' : v = seqMaxBVN seq + 1 := hv
      subst v
      exact absurd (seqBV_lt_seqMaxBVN seq _ A hA hbv) (Nat.lt_irrefl _)
    · intro f hf; exact hf.elim
    · intro c hc; cases hc
  · intro f hf ts hts
    refine ⟨(safeTermsN_isGenTermAlg seq).closedFunc f ts (fun i => (hts i).1), ?_, ?_⟩
    · intro g hg
      rcases hg with rfl | ⟨i, hi⟩
      · exact hf
      · exact (hts i).2.1 g hi
    · intro c hc
      obtain ⟨i, hi⟩ := (termConstSyms_func_iff f ts c).mp hc
      exact (hts i).2.2 c hi
  · intro c hc
    refine ⟨(safeTermsN_isGenTermAlg seq).closedConst c, ?_, ?_⟩
    · intro f hf; exact hf.elim
    · intro d hd
      have heq : d = c := Term.const.inj (List.mem_singleton.mp hd)
      exact heq ▸ hc

/-- Theorem 5.5.1 (companion): An infinite search path yields a Hintikka
set over the safe terms of the reduct L′ = L_S, whose symbols occur in the
path formulae (the TERM₀ seeds). The term algebra is over this occurrence
language; closure under every symbol of the ambient L is not required.
The extracted S contains the signed versions of the input formulae. -/
theorem infinitePath_yields_hintikkaSet {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) (seq : Sequent L) (w : SearchTreeData L seq)
    (hPath : w.treeDom.HasInfinitePath) :
    ∃ (S : Set (SignedFormula L)) (H : Set (Term L)),
      IsHintikkaSet L hL H S ∧
      (∀ A ∈ seq.antecedent, SignedFormula.trueF A ∈ S) ∧
      (∀ B ∈ seq.succedent, SignedFormula.falseF B ∈ S) := by
-- BEGIN PROOF
  obtain ⟨f, hPath'⟩ := hPath
  let S := w.pathSignedSet f hPath'
  let H : Set (Term L) := fun t => t ∈ safeTermsN seq ∧
    termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S
  refine ⟨S, H, ?_, ?_, ?_⟩
  · -- IsHintikkaSet L H S
    exact {
      hTA := safeReductTerms_isTermAlgebraOver seq S
      h0 := searchTree_path_no_complementary_atoms w f hPath'
      h1 := (searchTree_path_hintikka_propositional w f hPath').1
      h2 := (searchTree_path_hintikka_propositional w f hPath').2
      h3 := fun c hc t ht => searchTree_path_hintikka_typeC w f hPath' c hc t ht.1
      h4 := fun d hd => by
        obtain ⟨x, hx, hfree, hcomp⟩ := searchTree_path_hintikka_typeD_var w f hPath' d hd
        exact ⟨Term.var x, ⟨hx, fun _ h => h.elim, fun _ h => by cases h⟩, hfree, hcomp⟩
      h5 := fun sf hsf xv hxv => by
        refine ⟨?_, fun _ h => h.elim, fun _ h => by cases h⟩
        -- H5: free vars of path formulas ∈ safeTermsN.
        -- sf ∈ S means it's trueF A or falseF A for some A at depth n.
        -- xv ∈ signedFormulaFreeVars sf means xv ∈ formulaFVN A.
        -- Need: Term.var xv ∈ safeTermsN seq.
        obtain ⟨n, hn, hFormula⟩ := hsf
        have hFVsafe := branchingNodeSeqF_fvSafe seq w.freshBase f n
          w.input_crossNoFreeBound w.freshBase_bound
        rw [nodeSeq_eq_branchingNodeSeqF w f hPath' n] at hFormula
        -- Term.var xv ∈ safeTermsN seq means: xv ∉ BV(B) for all B ∈ seq
        show Term.var xv ∈ safeTermsN seq
        intro v hv B hB
        -- v ∈ termFV (Term.var xv) = {xv}, so v = xv
        have hvxv : v = xv := hv
        rw [hvxv]
        -- xv ∈ FV(some formula in branchingNodeSeqF) → xv ∉ BV(B)
        rcases hFormula with ⟨A, hA, hsf_eq⟩ | ⟨A, hA, hsf_eq⟩
        · have hxvFV : xv ∈ formulaFVN A := by
            rw [hsf_eq] at hxv; exact hxv
          exact hFVsafe A (List.mem_append_left _ hA) xv hxvFV B hB
        · have hxvFV : xv ∈ formulaFVN A := by
            rw [hsf_eq] at hxv; exact hxv
          exact hFVsafe A (List.mem_append_right _ hA) xv hxvFV B hB
      h6 := fun x A t ht hQ => searchTree_path_freeFor w f hPath' x A t ht.1 hQ
    }
  · -- ∀ A ∈ seq.antecedent, trueF A ∈ S
    intro A hA
    refine ⟨0, hPath' 0, Or.inl ⟨A, ?_, rfl⟩⟩
    change A ∈ (w.nodeSequent [] _).antecedent
    rw [w.root_sequent]; exact hA
  · -- ∀ B ∈ seq.succedent, falseF B ∈ S
    intro B hB
    refine ⟨0, hPath' 0, Or.inr ⟨B, ?_, rfl⟩⟩
    change B ∈ (w.nodeSequent [] _).succedent
    rw [w.root_sequent]; exact hB

-- ===================================================================
-- finiteClosedTree_to_proofTree
-- ===================================================================

/-- Theorem 5.5.1 (companion, normalized conversion): Converting a
finite closed normalized search tree to a `GProofTreeExt` (under the
§5.4.8 standing assumption). When the search tree is finite, delegates
to `searchTree_finite_valid_to_proof`. -/
theorem finiteClosedTree_to_proofTree {L : Language} [Countable (Term L)]
    (seq : Sequent L)
    (w : SearchTreeData L seq)
    (hFinite : w.treeDom.IsFinite) :
    sequentProvableExt seq :=
-- BEGIN PROOF
  searchTree_finite_valid_to_proof w hFinite

end LCS.FirstOrder.Gentzen.Hintikka
end

