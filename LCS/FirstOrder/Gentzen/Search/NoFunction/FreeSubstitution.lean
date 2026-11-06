import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.FreeSubstitution.ProofsStamp

/-! # Free substitutions during the search (Section 5.4.7)

The variables of TERM₀ do not occur bound in the input and the variables of AVAIL₀
are new, so the substitutions performed by the quantifier rules are free. The
invariant expressing this, its preservation, and the resulting freeness lemmas.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- SearchState invariant (textbook §5.4.7 variable bookkeeping)
-- ===================================================================

/-- Definition 5.4.9 (companion, invariant): A Nat `bound` is above all
    variable indices in `seq` if every formula of `seq` has all free
    and bound variable indices strictly less than `bound`. Used to
    state the `SearchState.Inv` invariant below. -/
@[blueprint "chap5__definition_5_4_9"]
def NoVarAbove {L : Language} (seq : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ seq.antecedent ++ seq.succedent,
    (∀ j ∈ formulaFVN F, j < bound) ∧ (∀ j ∈ formulaBVN F, j < bound)

namespace SearchState

/-- Definition 5.4.9 (companion): The input's bound variables stay below
    `bound`. Available entries are variables fresh for those binders.
    Activated variables are either input free variables or fresh for its
    binders, and no variable in TERM₀ or TERM₁ occurs in the unconsumed
    availability stream. These conditions permit any injective enumeration,
    including enumerations whose variable indices do not increase. -/
@[blueprint "chap5__definition_5_4_9"]
structure Inv {L : Language} {supply : TermStream L} (seq : Sequent L) (bound : Nat)
    (st : SearchState L supply) : Prop where
  bound_above_seq : NoVarAbove seq bound
  available_vars : ∀ n, ∃ i, supply.entries n = some (.var i)
  avail_fresh : ∀ n, st.availNext ≤ n → ∀ i, supply.entries n = some (.var i) →
    ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms_allowed : ∀ rec ∈ st.TERM0,
    ∀ i, rec = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms1_allowed : ∀ rec ∈ st.TERM1,
    ∀ i, rec = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms_below_avail : ∀ rec ∈ st.TERM0,
    ∀ i, rec = Term.var i → BeforeCursor supply st.availNext i
  terms1_below_avail : ∀ rec ∈ st.TERM1,
    ∀ i, rec = Term.var i → BeforeCursor supply st.availNext i

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (companion, invariant): `tailAVAIL0` preserves the
    state invariant. Increments `availNext`; `bound`, TERM₀, and TERM₁
    unchanged. -/
theorem tailAVAIL0_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L} {bound : Nat}
    {st : SearchState L supply} (h : Inv seq bound st) : Inv seq bound st.tailAVAIL0 := by
  refine ⟨h.bound_above_seq, h.available_vars, ?_, h.terms_allowed, h.terms1_allowed, ?_, ?_⟩
  · intro n hn i hi
    exact h.avail_fresh n (Nat.le_trans (Nat.le_succ _) hn) i hi
  · intro t ht i hi
    exact (h.terms_below_avail t ht i hi).mono (Nat.le_succ _)
  · intro t ht i hi
    exact (h.terms1_below_avail t ht i hi).mono (Nat.le_succ _)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (companion, invariant): `appendTERM1` preserves
    the state invariant. Only `TERM1` changes; TERM₀, availNext, bound
    are untouched. The caller must witness that the appended `y` (if
    a variable) is either free-in-seq or ≥ bound — typically discharged
    via `avail_above_bound` when `y = Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))`. -/
theorem appendTERM1_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L}
    {bound : Nat} {st : SearchState L supply} {y : Term L}
    (h : Inv seq bound st)
    (hy : ∀ i, y = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F))
    (hy_strict : ∀ i, y = Term.var i → BeforeCursor supply st.availNext i) :
    Inv seq bound (st.appendTERM1 y) := by
-- BEGIN PROOF
  refine ⟨h.bound_above_seq, h.available_vars, h.avail_fresh, h.terms_allowed, ?_, h.terms_below_avail, ?_⟩
  · -- terms1_allowed preservation
    intro rec hRec i hi
    unfold appendTERM1 at hRec
    simp only at hRec
    rw [List.mem_append] at hRec
    rcases hRec with h1 | h2
    · exact h.terms1_allowed rec h1 i hi
    · rw [List.mem_singleton] at h2
      rw [h2] at hi
      apply hy i
      exact hi
  · -- terms1_below_avail preservation
    intro rec hRec i hi
    unfold appendTERM1 at hRec
    simp only at hRec
    rw [List.mem_append] at hRec
    rcases hRec with h1 | h2
    · exact h.terms1_below_avail rec h1 i hi
    · rw [List.mem_singleton] at h2
      rw [h2] at hi
      exact hy_strict i hi

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, invariant): `commitRound` preserves
    the state invariant. Since `Inv`'s `terms1_allowed` field tracks
    the TERM₁ allowed-variable property, committing TERM₀ := TERM₁
    straightforwardly moves that property to `terms_allowed`. -/
theorem commitRound_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L}
    {bound : Nat} {st : SearchState L supply} (h : Inv seq bound st)
    {s : Sequent L} (t : SearchTree s) :
    Inv seq bound (st.commitRound t).2 :=
  ⟨h.bound_above_seq, h.available_vars, h.avail_fresh, h.terms1_allowed,
    h.terms1_allowed, h.terms1_below_avail, h.terms1_below_avail⟩

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): Every admissible initialization
    satisfies the global search invariant. -/
theorem init_preserves_Inv {L : Language} {seq : Sequent L} (initial : Init seq) :
    Inv seq (sequentVarBound seq) (init initial) := by
  rcases initial.admissible with ⟨hTerms, hVars, hDisj, _⟩
  have hAllowed : ∀ t ∈ initial.term0, ∀ i, t = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F) := by
    intro t ht i hi
    rcases initialTerms_var_index seq t ((hTerms t).mp ht) i hi with hFV | hEq
    · exact Or.inl hFV
    · right; subst i
      intro F hF hBV
      exact (leastAbsentVar_spec seq).1 (sequentVarIndices_mem hF (Or.inr hBV))
  have hBefore : ∀ t ∈ initial.term0, ∀ i, t = Term.var i →
      BeforeCursor initial.avail0 0 i := by
    intro t ht i hi n _ heq
    exact hDisj n t (hi ▸ heq) ht
  refine ⟨?_, ?_, ?_, hAllowed, hAllowed, hBefore, hBefore⟩
  · intro F hF
    exact ⟨fun i hi => sequentVarIndices_lt_bound seq (sequentVarIndices_mem hF (Or.inl hi)),
      fun i hi => sequentVarIndices_lt_bound seq (sequentVarIndices_mem hF (Or.inr hi))⟩
  · intro n; obtain ⟨i, hi, _⟩ := hVars n; exact ⟨i, hi⟩
  · intro n _ i hi F hF hBV
    obtain ⟨j, hj, hjFresh⟩ := hVars n
    have hji : j = i := Term.var.inj (Option.some.inj (hj.symm.trans hi))
    subst j
    exact hjFresh (sequentVarIndices_mem hF (Or.inr hBV))

end SearchState

-- ===================================================================
-- Side-condition discharge lemmas (isFreeForN, freshness)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): `isFreeForN (Term.var i) x B`
    holds whenever `i ∉ formulaBVN B`, i.e. `i` is not a bound variable
    anywhere in B. Structural induction on B unfolds both `isFreeForN`
    and `formulaBVN` in parallel: at binders, either `x` matches the
    binder (trivial case of isFreeForN) or we must show `i ≠ y` and
    recurse. Since `i ∉ BV(∀y A) = BV(A) ∪ {y}` gives both `i ∉ BV(A)`
    (IH) and `i ≠ y` (the `{y}` clause), the proof goes through. -/
theorem isFreeForN_var_of_notBV {L : Language} (i x : Nat) (B : FormulaN L)
    (h : i ∉ formulaBVN B) : isFreeForN (Term.var i) x B := by
-- BEGIN PROOF
  induction B with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg A ihA =>
    have h' : i ∉ formulaBVN A := h
    exact ihA h'
  | conj A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | disj A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | impl A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | all y A ihA =>
    -- formulaBVN (all y A) = formulaBVN A ∪ {y}
    -- h : i ∉ formulaBVN A ∪ {y}
    -- Goal: x = y ∨ (¬ (y ∈ termFV (Term.var i)) ∧ isFreeForN (Term.var i) x A)
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ihA (fun hBVA => h (Or.inl hBVA))⟩
      -- termFV (Term.var i) = {i}, so ¬ (y ∈ {i}) ↔ y ≠ i, which is i ≠ y
      show y ∉ termFV (Term.var i)
      intro hy
      -- termFV (Term.var i) = Set.singleton i; hy : y ∈ Set.singleton i
      have hyi : y = i := hy
      have hiyIn : i ∈ formulaBVN (FormulaN.all y A) := by
        show i ∈ formulaBVN A ∪ Set.singleton y
        exact Or.inr (by show i ∈ Set.singleton y; rw [hyi]; rfl)
      exact h hiyIn
  | ex y A ihA =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ihA (fun hBVA => h (Or.inl hBVA))⟩
      show y ∉ termFV (Term.var i)
      intro hy
      have hyi : y = i := hy
      have hiyIn : i ∈ formulaBVN (FormulaN.ex y A) := by
        show i ∈ formulaBVN A ∪ Set.singleton y
        exact Or.inr (by show i ∈ Set.singleton y; rw [hyi]; rfl)
      exact h hiyIn

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): `isFreeForN (Term.const c) x B`
    holds unconditionally, because `termFV (Term.const c) = ∅` means
    no variable of B can be captured by substituting `c`. -/
theorem isFreeForN_const {L : Language} (c : L.constSymbols) (x : Nat)
    (B : FormulaN L) : isFreeForN (Term.const c) x B := by
-- BEGIN PROOF
  induction B with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ih⟩
      show y ∉ termFV (Term.const (L := L) c)
      intro hy
      exact hy
  | ex y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ih⟩
      show y ∉ termFV (Term.const (L := L) c)
      intro hy
      exact hy

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): An index `i ∈ FV(seq)`
    (i.e. appears free in some formula of `seq`), under the §5.4.7
    standing assumption `crossNoFreeBound seq` ("the set of all
    variables occurring free in some formula in the sequent is
    disjoint from the set of all variables occurring bound in some
    formula in the sequent"), does NOT occur bound in any formula of
    `seq`.

    Bridge between "FV-class TERM₀ entries" and "isFreeForN discharge":
    when a TERM₀ entry `Term.var i` has `i ∈ FV(seq)`,
    `crossNoFreeBound` gives `i ∉ BV(G)` for every `G ∈ seq`, so via
    the subformula-bound invariant `BV(B) ⊆ BV(G)` for any subformula
    `B` of `G`, `isFreeForN_var_of_notBV` yields
    `isFreeForN (Term.var i) x B`. -/
theorem notBV_of_FV_of_crossNFB {L : Language} {seq : Sequent L}
    (hCNFB : crossNoFreeBound seq) {i : Nat}
    (hFV : ∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F)
    (G : FormulaN L) (hG : G ∈ seq.antecedent ++ seq.succedent) :
    i ∉ formulaBVN G :=
-- BEGIN PROOF
  hCNFB i hFV G hG

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): Combined "allowed index"
    discharge — if `i` is `VarAllowed` (free in seq OR ≥ bound), then
    `i` is not bound in any formula of `seq` under the §5.4.7 standing
    assumption `crossNoFreeBound seq` and the invariant
    `NoVarAbove seq bound`. -/
theorem notBV_of_allowed {L : Language} {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (hNVA : NoVarAbove seq bound) {i : Nat}
    (hAllowed :
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F))
    (G : FormulaN L) (hG : G ∈ seq.antecedent ++ seq.succedent) :
    i ∉ formulaBVN G := by
-- BEGIN PROOF
  cases hAllowed with
  | inl hFV => exact notBV_of_FV_of_crossNFB hCNFB hFV G hG
  | inr hFresh => exact hFresh G hG

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): If `i ∉ formulaBVN (∀x A)`,
    then `i ∉ formulaBVN A`. This is the "descend into binder body"
    direction of the subformula-bound invariant: binding `x` can only
    ADD `x` to BV, so the inside's BV is a subset of the outside's BV.
    Used by `growLeftAll` (and mirror cases) to lift discharge from
    `∀x A ∈ seq` to `A` (the body, where substitution actually
    happens). -/
theorem notBV_body_of_all {L : Language} {i x : Nat} {A : FormulaN L}
    (h : i ∉ formulaBVN (FormulaN.all x A)) : i ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  exact h (Or.inl hBV)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): Mirror of `notBV_body_of_all`
    for the existential binder. -/
theorem notBV_body_of_ex {L : Language} {i x : Nat} {A : FormulaN L}
    (h : i ∉ formulaBVN (FormulaN.ex x A)) : i ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  exact h (Or.inl hBV)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Advancing AVAIL₀ and appending its former head to TERM₁ preserves
    the state invariant. Stream injectivity excludes that variable from
    every later position. -/
theorem SearchState.Inv.tailAppend {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st) :
    SearchState.Inv seq bound
      ((st.tailAVAIL0).appendTERM1 (Term.var (supply.varAt st.availNext (h.available_vars st.availNext)))) := by
  apply SearchState.appendTERM1_preserves_Inv (SearchState.tailAVAIL0_preserves_Inv h)
  · intro i hi
    have hEq := Term.var.inj hi
    right
    exact hEq ▸ h.avail_fresh st.availNext (Nat.le_refl _) _
      (supply.varAt_spec st.availNext (h.available_vars st.availNext))
  · intro i hi
    have hEq := Term.var.inj hi
    exact hEq ▸ supply.varAt_beforeSucc st.availNext (h.available_vars st.availNext)

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
