import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Symbols
import Attach
import LCS.CutElim.Interpolation.ProofSubstitution.Basic.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
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
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Lemma 6.5.1: Variable and constant substitution in LK proof trees
-- ===================================================================

-- ===================================================================
-- Substitution infrastructure
-- ===================================================================

/-- Lemma 6.5.1 (required def): Apply variable substitution `[z/y]`
pointwise to every formula in the antecedent and succedent of a
sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def sequentSubstVar {L : Language}
    (s : Sequent L) (z y : Nat) : Sequent L :=
  { antecedent := s.antecedent.map (fun A => formulaSubstN A (.var z) y)
    succedent := s.succedent.map (fun A => formulaSubstN A (.var z) y) }

/-- Lemma 6.5.1 (required def): Replace every occurrence of the
constant symbol `c` in a term by the variable `z`. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def termSubstConst {L : Language}
    (t : Term L) (z : Nat) (c : L.constSymbols) : Term L :=
  match t with
  | .var x => .var x
  | .const c' => if c' = c then .var z else .const c'
  | .func f ts => .func f (fun i => termSubstConst (ts i) z c)

/-- Lemma 6.5.1 (required def): Replace every occurrence of the
constant symbol `c` in a formula by the variable `z`, recursing
through subformulae and subterms. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) : FormulaN L :=
  match A with
  | .predN P ts => .predN P (fun i => termSubstConst (ts i) z c)
  | .eq_ hL t1 t2 => .eq_ hL (termSubstConst t1 z c) (termSubstConst t2 z c)
  | .conj A B => .conj (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .disj A B => .disj (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .impl A B => .impl (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .neg A => .neg (formulaSubstConst A z c)
  | .all x A => .all x (formulaSubstConst A z c)
  | .ex x A => .ex x (formulaSubstConst A z c)

/-- Lemma 6.5.1 (required def): Apply constant-for-variable
substitution `[z/c]` pointwise to every formula in the antecedent
and succedent of a sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def sequentSubstConst {L : Language}
    (s : Sequent L) (z : Nat) (c : L.constSymbols) : Sequent L :=
  { antecedent := s.antecedent.map (fun A => formulaSubstConst A z c)
    succedent := s.succedent.map (fun A => formulaSubstConst A z c) }

-- ===================================================================
-- Substitution helper lemmas (preserved — these are pure formula/term lemmas)
-- ===================================================================

theorem termSubst_var_comm {L : Language}
    (s t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x) :
    termSubst (termSubst s t x) (.var z) y =
    termSubst (termSubst s (.var z) y) (termSubst t (.var z) y) x := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> by_cases hvy : v = y <;> simp_all [termSubst]
  | const c => simp [termSubst]
  | func f ts ih => simp only [termSubst]; congr 1; ext i; exact ih i

theorem formulaSubst_var_comm {L : Language}
    (A : FormulaN L) (t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x)
    (hNB : ¬ formulaBVN A y) :
    formulaSubstN (formulaSubstN A t x) (.var z) y =
    formulaSubstN (formulaSubstN A (.var z) y) (termSubst t (.var z) y) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp [formulaSubstN]; congr 1; ext i; exact termSubst_var_comm _ _ _ _ _ hxy hzx
  | eq_ _ t1 t2 => simp [formulaSubstN, termSubst_var_comm _ _ _ _ _ hxy hzx]
  | conj A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | disj A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | impl A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | neg A ih => simp [formulaSubstN, ih hNB]
  | all w A ih =>
    have hA : ¬ formulaBVN A y := fun h => hNB (Or.inl h)
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    by_cases hxw : x = w
    · subst hxw; simp [formulaSubstN, hyw]
    · simp [formulaSubstN, hxw, hyw, ih hA]
  | ex w A ih =>
    have hA : ¬ formulaBVN A y := fun h => hNB (Or.inl h)
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    by_cases hxw : x = w
    · subst hxw; simp [formulaSubstN, hyw]
    · simp [formulaSubstN, hxw, hyw, ih hA]

-- Term free variables are preserved or mapped under variable substitution.
theorem termFV_termSubst_var {L : Language}
    (s : Term L) (y z w : Nat) (hwz : w ≠ z)
    (h : w ∉ termFV s) :
    w ∉ termFV (termSubst s (.var z) y) := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]; split
    · simp [termFV]; exact hwz
    · exact h
  | const c => exact h
  | func f ts ih =>
    simp only [termSubst, termFV] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- isFreeForN for a variable that doesn't appear bound in A.
theorem isFreeFor_var_notBV {L : Language}
    (A : FormulaN L) (x z : Nat) (hNoBV : ¬ formulaBVN A z) :
    isFreeForN (.var z) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | neg A ih => exact ih hNoBV
  | all y A ih =>
    simp only [isFreeForN]
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hzy : z ≠ y := fun h => hNoBV (Or.inr (h ▸ rfl))
      exact ⟨fun hmem => hzy hmem.symm, ih (fun h => hNoBV (Or.inl h))⟩
  | ex y A ih =>
    simp only [isFreeForN]
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hzy : z ≠ y := fun h => hNoBV (Or.inr (h ▸ rfl))
      exact ⟨fun hmem => hzy hmem.symm, ih (fun h => hNoBV (Or.inl h))⟩

-- isFreeForN preservation under variable substitution.
theorem isFreeFor_var_subst {L : Language}
    (A : FormulaN L) (t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x)
    (hfree : isFreeForN t x A) (hNB : ¬ formulaBVN A y) (hNoZ : ¬ formulaBVN A z) :
    isFreeForN (termSubst t (.var z) y) x (formulaSubstN A (.var z) y) := by
-- BEGIN PROOF
  induction A with
  | predN P ts => trivial
  | eq_ _ t1 t2 => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | neg A ih => exact ih hfree hNB hNoZ
  | all w A ih =>
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
    simp only [formulaSubstN, show (y != w) = true from by simp [hyw], ite_true, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right; exact ⟨termFV_termSubst_var t y z w (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
    simp only [formulaSubstN, show (y != w) = true from by simp [hyw], ite_true, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right; exact ⟨termFV_termSubst_var t y z w (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h))⟩

-- Term-level: constant substitution commutes with variable substitution.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem termSubstConst_termSubst_comm {L : Language}
    (s t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols) (hzx : z ≠ x) :
    termSubstConst (termSubst s t x) z c =
    termSubst (termSubstConst s z c) (termSubstConst t z c) x := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> simp_all [termSubstConst, termSubst]
  | const c' =>
    simp only [termSubst, termSubstConst]
    by_cases hcc : c' = c
    · subst hcc; simp [termSubst, hzx]
    · simp [termSubst, termSubstConst, hcc]
  | func f ts ih => simp only [termSubst, termSubstConst]; congr 1; ext i; exact ih i

-- Constant substitution commutes with variable substitution in formulas.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem formulaSubstConst_formulaSubst_comm {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols) (hzx : z ≠ x) :
    formulaSubstConst (formulaSubstN A t x) z c =
    formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp [formulaSubstN, formulaSubstConst]; congr 1; ext i
    exact termSubstConst_termSubst_comm _ _ _ _ _ hzx
  | eq_ _ t1 t2 =>
    simp [formulaSubstN, formulaSubstConst,
      termSubstConst_termSubst_comm t1 t x z c hzx,
      termSubstConst_termSubst_comm t2 t x z c hzx]
  | conj A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | neg A ih => simp [formulaSubstN, formulaSubstConst, ih]
  | all w A ih => simp [formulaSubstN, formulaSubstConst]; split <;> simp [formulaSubstConst, ih]
  | ex w A ih => simp [formulaSubstN, formulaSubstConst]; split <;> simp [formulaSubstConst, ih]

-- termFV is mapped under constant substitution: only gains z.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution, LCS.CutElim.Interpolation.VariableSubstitution
theorem termFV_termSubstConst {L : Language}
    (s : Term L) (z w : Nat) (c : L.constSymbols) (hwz : w ≠ z)
    (h : w ∉ termFV s) :
    w ∉ termFV (termSubstConst s z c) := by
-- BEGIN PROOF
  induction s with
  | var v => exact h
  | const c' =>
    simp only [termSubstConst]; split
    · simp [termFV]; exact hwz
    · exact fun hm => h hm
  | func f ts ih =>
    simp only [termSubstConst, termFV] at h ⊢
    intro ⟨i, hi⟩; exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- isFreeForN is preserved under constant substitution.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem isFreeFor_constSubst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols)
    (hfree : isFreeForN t x A) (hNoZ : ¬ formulaBVN A z) :
    isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) := by
-- BEGIN PROOF
  induction A with
  | predN P ts => trivial
  | eq_ _ t1 t2 => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | neg A ih => exact ih hfree hNoZ
  | all w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right; exact ⟨termFV_termSubstConst t z w c (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right; exact ⟨termFV_termSubstConst t z w c (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNoZ (Or.inl h))⟩

-- formulaFVN under constant substitution
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution, LCS.CutElim.Interpolation.VariableSubstitution
theorem formulaFV_formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) (v : Nat) (hvz : v ≠ z)
    (h : v ∉ formulaFVN A) :
    v ∉ formulaFVN (formulaSubstConst A z c) := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨i, hi⟩; exact h ⟨i, termFV_termSubstConst (ts i) z v c hvz (fun hm => h ⟨i, hm⟩) |>.elim hi⟩
  | eq_ _ t1 t2 =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact (termFV_termSubstConst t1 z v c hvz (fun hm => h (Or.inl hm))).elim h1
    · exact (termFV_termSubstConst t2 z v c hvz (fun hm => h (Or.inr hm))).elim h2
  | conj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | disj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | impl A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | neg A ih =>
    simp only [formulaSubstConst, formulaFVN]; exact ih h
  | all w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩; exact ih (fun hm' => h ⟨hm', hne⟩) hm
  | ex w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩; exact ih (fun hm' => h ⟨hm', hne⟩) hm

-- formulaBVN under constant substitution is identity


-- BV(A[t/x]) = BV(A)
theorem formulaBV_formulaSubst {L : Language} (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaBVN (formulaSubstN A t x) = formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => rfl
  | eq_ _ t1 t2 => rfl
  | conj A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | disj A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | impl A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | neg A ih => simp only [formulaSubstN, formulaBVN, ih]
  | all w A ih =>
    simp only [formulaSubstN, formulaBVN]
    split <;> simp only [formulaBVN, ih]
  | ex w A ih =>
    simp only [formulaSubstN, formulaBVN]
    split <;> simp only [formulaBVN, ih]

-- Helper: (.var x) is always free for x in any formula.
-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.InterpolantRepair, LCS.Herbrand.HerbrandTheorem.Part2
theorem isFreeForN_var_self {L : Language} (A : FormulaN L) (x : Nat) :
    isFreeForN (.var x) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ => trivial
  | conj A B ihA ihB => exact ⟨ihA, ihB⟩
  | disj A B ihA ihB => exact ⟨ihA, ihB⟩
  | impl A B ihA ihB => exact ⟨ihA, ihB⟩
  | neg A ih => exact ih
  | all y A ih =>
    show x = y ∨ _
    by_cases h : x = y
    · exact .inl h
    · exact .inr ⟨fun heq => h (by
        simp only [termFV] at heq; exact heq.symm), ih⟩
  | ex y A ih =>
    show x = y ∨ _
    by_cases h : x = y
    · exact .inl h
    · exact .inr ⟨fun heq => h (by
        simp only [termFV] at heq; exact heq.symm), ih⟩

-- Helper: if v ∉ termFV t and v ≠ z, then v ∉ termFV (termSubst t (.var z) y)
theorem termFV_termSubst_ne {L : Language}
    (t : Term L) (y z v : Nat) (hNotFree : v ∉ termFV t) (hNeZ : v ≠ z) :
    v ∉ termFV (termSubst t (.var z) y) := by
-- BEGIN PROOF
  induction t with
  | var w =>
    simp only [termSubst]; split
    · rename_i heq; exact hNeZ
    · exact hNotFree
  | const c => exact hNotFree
  | func f ts ih =>
    simp only [termSubst, termFV] at hNotFree ⊢
    intro ⟨i, hi⟩; exact ih i (fun hm => hNotFree ⟨i, hm⟩) hi

-- Helper: if v ∉ FV(F) and v ≠ z, then v ∉ FV(F[z/y])
theorem formulaFV_formulaSubst_ne {L : Language}
    (F : FormulaN L) (y z v : Nat) (hNotFree : v ∉ formulaFVN F) (hNeZ : v ≠ z) :
    v ∉ formulaFVN (formulaSubstN F (.var z) y) := by
-- BEGIN PROOF
  induction F with
  | predN P ts =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢
    intro ⟨i, hi⟩; exact hNotFree ⟨i, (termFV_termSubst_ne _ y z v (fun hm => hNotFree ⟨i, hm⟩) hNeZ).elim hi⟩
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢
    intro hm; rcases hm with h1 | h2
    · exact (termFV_termSubst_ne t1 y z v (fun hm => hNotFree (Or.inl hm)) hNeZ).elim h1
    · exact (termFV_termSubst_ne t2 y z v (fun hm => hNotFree (Or.inr hm)) hNeZ).elim h2
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | neg A ih => simp only [formulaSubstN, formulaFVN]; exact ih hNotFree
  | all w A ih =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; split
    · intro ⟨hm, hne⟩; exact ih (fun hm' => hNotFree ⟨hm', hne⟩) hm
    · exact hNotFree
  | ex w A ih =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; split
    · intro ⟨hm, hne⟩; exact ih (fun hm' => hNotFree ⟨hm', hne⟩) hm
    · exact hNotFree

/-- A variable is not bound in an LK deduction tree when it is not bound
in any leaf sequent or rule annotation. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.notBoundIn {L : Language}
    {hL : L.withoutEquality} :
    {s : Sequent L} → FOLKDeductionTree hL s → Nat → Prop
  | s, .leaf _, y => sequentNotBoundIn s y
  | _, .onePremise rule t, y => rule.notBoundIn y ∧ t.notBoundIn y
  | _, .twoPremise rule t₁ t₂, y =>
      rule.notBoundIn y ∧ t₁.notBoundIn y ∧ t₂.notBoundIn y

/-- A variable does not occur in an LK deduction tree when it occurs in
neither its leaf sequents nor its rule annotations, including eigenvariables
and instantiating terms. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.varNotOccurs {L : Language}
    {hL : L.withoutEquality} :
    {s : Sequent L} → FOLKDeductionTree hL s → Nat → Prop
  | s, .leaf _, z => sequentVarNotOccurs s z
  | _, .onePremise rule t, z => rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t₁ t₂, z =>
      rule.varNotOccurs z ∧ t₁.varNotOccurs z ∧ t₂.varNotOccurs z

/-- Passing from a deduction tree to its proof tree preserves bound-variable exclusion. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.notBoundIn_toProofTree
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (hp : T.isProof) (v : Nat) :
    (T.toProofTree hp).notBoundIn v ↔ T.notBoundIn v := by
  induction T with
  | leaf q => rfl
  | onePremise rule t ih =>
    exact and_congr Iff.rfl (ih hp)
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    exact and_congr Iff.rfl (and_congr (ih₁ hp.1) (ih₂ hp.2))

/-- Passing from a deduction tree to its proof tree preserves variable freshness. -/
theorem _root_.LCS.CutElim.LK.FOLKDeductionTree.varNotOccurs_toProofTree
    {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (T : FOLKDeductionTree hL s) (hp : T.isProof) (v : Nat) :
    (T.toProofTree hp).varNotOccurs v ↔ T.varNotOccurs v := by
  induction T with
  | leaf q => rfl
  | onePremise rule t ih =>
    exact and_congr Iff.rfl (ih hp)
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    exact and_congr Iff.rfl (and_congr (ih₁ hp.1) (ih₂ hp.2))

variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

end LCS.CutElim.Interpolation
end
