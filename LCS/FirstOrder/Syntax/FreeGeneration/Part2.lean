import LCS.Item
import LCS.Util
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Syntax.FreeGeneration.Part1
import Attach
import LCS.FirstOrder.Syntax.FreeGeneration.Part2.ProofsStamp

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax





/-- Lemma 5.2.5: For any proper prefix w of a formula A (in its
string representation), K(w) ≤ 0. -/
@[blueprint "chap5__lemma_5_2_5" (main := true)]
theorem formula_prefix_k_le_zero {L : Language} (A : Formula L)
    (w rest : List (FormulaSymbol L))
    (hw : Formula.toSymbolList A = w ++ rest)
    (hne : rest ≠ []) :
    formulaListK L w ≤ 0 

-- ===================================================================
-- Lemma 5.2.6: No proper prefix of a formula is a formula
-- ===================================================================

/-- Lemma 5.2.6: No proper prefix of a formula is a formula. If w is both a
proper prefix of A and the string representation of formula B, then K(w) = 1 (by formula_k_eq_one applied to B) but also K(w) ≤ 0 (by formula_prefix_k_le_zero). Contradiction. -/
@[blueprint "chap5__lemma_5_2_6" (main := true)]
theorem formula_prefix_free {L : Language} (A : Formula L)
    (w rest : List (FormulaSymbol L))
    (hw : Formula.toSymbolList A = w ++ rest)
    (hne : rest ≠ []) :
    ¬∃ (B : Formula L), Formula.toSymbolList B = w 

-- ===================================================================
-- Theorem 5.2.2: Free generation of FORM_L
-- ===================================================================







-- retained: used by LCS.FirstOrder.Syntax.Parenthesized
/-- If a ++ r1 = b ++ r2 and a.length = b.length then a = b and r1 = r2. -/
theorem append_cancel_of_length_eq {α : Type} {a b rest1 rest2 : List α}
    (h : a ++ rest1 = b ++ rest2) (hlen : a.length = b.length) :
    a = b ∧ rest1 = rest2 := by
-- BEGIN PROOF
  have hab : a = b := by
    have h1 := congrArg (List.take a.length) h
    rw [List.take_append_of_le_length (by omega), List.take_length,
        List.take_append_of_le_length (by omega), show a.length = b.length from hlen,
        List.take_length] at h1; exact h1
  subst hab; exact ⟨rfl, List.append_cancel_left h⟩

-- retained: used by LCS.FirstOrder.Syntax.Parenthesized
/-- Prefix-freeness of terms lifted to an append-cancel principle:
if toSymbolList t1 ++ r1 = toSymbolList t2 ++ r2 then the two
toSymbolLists are equal and the remainders are equal. -/
theorem termSymList_append_cancel {L : Language}
    (t1 t2 : Term L) (rest1 rest2 : List (TermSymbol L))
    (h : Term.toSymbolList t1 ++ rest1 = Term.toSymbolList t2 ++ rest2) :
    Term.toSymbolList t1 = Term.toSymbolList t2 ∧ rest1 = rest2 := by
-- BEGIN PROOF
  by_cases hlen : (Term.toSymbolList t1).length < (Term.toSymbolList t2).length
  · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h (by omega)
    have hmid_ne : mid ≠ [] := by
      intro heq; subst heq; simp at hmid_eq
      have := congrArg List.length hmid_eq; omega
    exact absurd ⟨t1, rfl⟩ (term_prefix_free t2 _ mid hmid_eq hmid_ne)
  · by_cases hlen2 : (Term.toSymbolList t2).length < (Term.toSymbolList t1).length
    · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h.symm (by omega)
      have hmid_ne : mid ≠ [] := by
        intro heq; subst heq; simp at hmid_eq
        have := congrArg List.length hmid_eq; omega
      exact absurd ⟨t2, rfl⟩ (term_prefix_free t1 _ mid hmid_eq hmid_ne)
    · exact append_cancel_of_length_eq h (by omega)

-- retained: used by LCS.FirstOrder.Syntax.Algebra, LCS.FirstOrder.Syntax.Parenthesized
/-- Theorem 5.2.1 (companion): The symbol-list representation of terms is injective. -/
theorem term_toSymbolList_injective {L : Language} (t1 t2 : Term L)
    (h : Term.toSymbolList t1 = Term.toSymbolList t2) : t1 = t2 := by
-- BEGIN PROOF
  induction t1 generalizing t2 with
  | var n =>
    cases t2 with
    | var m => simp [Term.toSymbolList] at h; subst h; rfl
    | const c => simp [Term.toSymbolList] at h
    | func f ts => simp [Term.toSymbolList, TermFormationFn.c_f] at h
  | const c =>
    cases t2 with
    | var m => simp [Term.toSymbolList] at h
    | const d => simp [Term.toSymbolList] at h; subst h; rfl
    | func f ts => simp [Term.toSymbolList, TermFormationFn.c_f] at h
  | func f ts ih =>
    cases t2 with
    | var m => simp [Term.toSymbolList, TermFormationFn.c_f] at h
    | const c => simp [Term.toSymbolList, TermFormationFn.c_f] at h
    | func g us =>
      simp only [Term.toSymbolList_func, List.singleton_append, List.cons_eq_cons] at h
      obtain ⟨hfg, hrest⟩ := h; cases hfg; congr 1
      have : ∀ (n : Nat) (ts' us' : Fin n → Term L),
          (∀ i, ∀ t2, Term.toSymbolList (ts' i) = Term.toSymbolList t2 → ts' i = t2) →
          (List.ofFn (fun i => Term.toSymbolList (ts' i))).flatten =
          (List.ofFn (fun i => Term.toSymbolList (us' i))).flatten →
          ts' = us' := by
        intro n; induction n with
        | zero => intro ts' us' _ _; funext i; exact i.elim0
        | succ m ihm =>
          intro ts' us' ih' hfl
          rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons] at hfl
          have hcan := termSymList_append_cancel (ts' 0) (us' 0) _ _ hfl
          funext i; match i with
          | ⟨0, _⟩ => exact ih' 0 _ hcan.1
          | ⟨k + 1, hk⟩ =>
            have := ihm (fun j => ts' j.succ) (fun j => us' j.succ)
              (fun j t2' ht2' => ih' j.succ t2' ht2') hcan.2
            exact congrFun this ⟨k, by omega⟩
      exact this _ ts us ih hrest

/-- Theorem 5.2.1: On tuples of term strings, each formation function C_f
is injective, and distinct function symbols give disjoint ranges. No value
of C_f is a one-letter variable or constant string. Term strings are the
range of `Term.toSymbolList`. -/
@[blueprint "chap5__theorem_5_2_1" (main := true)]
theorem term_free_generation (L : Language) :
    (∀ (f : L.funSymbols) (ss us : Fin (L.funArity f) → List (TermSymbol L)),
      (∀ i, ∃ t : Term L, Term.toSymbolList t = ss i) →
      (∀ i, ∃ t : Term L, Term.toSymbolList t = us i) →
      TermFormationFn.c_f f ss = TermFormationFn.c_f f us → ss = us) ∧
    (∀ (f g : L.funSymbols), f ≠ g →
      ∀ (ss : Fin (L.funArity f) → List (TermSymbol L))
        (us : Fin (L.funArity g) → List (TermSymbol L)),
      (∀ i, ∃ t : Term L, Term.toSymbolList t = ss i) →
      (∀ i, ∃ t : Term L, Term.toSymbolList t = us i) →
      TermFormationFn.c_f f ss ≠ TermFormationFn.c_f g us) ∧
    (∀ (f : L.funSymbols) (ss : Fin (L.funArity f) → List (TermSymbol L)),
      (∀ n : Nat, TermFormationFn.c_f f ss ≠ [TermSymbol.varSym n]) ∧
      (∀ c : L.constSymbols, TermFormationFn.c_f f ss ≠ [TermSymbol.constSym c])) 

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Prefix-freeness of formulae lifted to an append-cancel principle. -/
theorem fmlaSymList_append_cancel {L : Language}
    (A B : Formula L) (rest1 rest2 : List (FormulaSymbol L))
    (h : Formula.toSymbolList A ++ rest1 = Formula.toSymbolList B ++ rest2) :
    Formula.toSymbolList A = Formula.toSymbolList B ∧ rest1 = rest2 := by
-- BEGIN PROOF
  by_cases hlen : (Formula.toSymbolList A).length < (Formula.toSymbolList B).length
  · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h (by omega)
    have hmid_ne : mid ≠ [] := by
      intro heq; subst heq; simp at hmid_eq
      have := congrArg List.length hmid_eq; omega
    exact absurd ⟨A, rfl⟩ (formula_prefix_free B _ mid hmid_eq hmid_ne)
  · by_cases hlen2 : (Formula.toSymbolList B).length < (Formula.toSymbolList A).length
    · obtain ⟨mid, hmid_eq, _⟩ := list_split_left h.symm (by omega)
      have hmid_ne : mid ≠ [] := by
        intro heq; subst heq; simp at hmid_eq
        have := congrArg List.length hmid_eq; omega
      exact absurd ⟨B, rfl⟩ (formula_prefix_free A _ mid hmid_eq hmid_ne)
    · exact append_cancel_of_length_eq h (by omega)

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Flatten of ofFn of mapped lists equals map applied to the flattened
original lists. -/
theorem flatten_ofFn_map {α β : Type} {n : Nat} (f : α → β) (g : Fin n → List α) :
    (List.ofFn (fun i => (g i).map f)).flatten = ((List.ofFn g).flatten).map f := by
-- BEGIN PROOF
  induction n with
  | zero => simp [List.ofFn]
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons, List.map_append]
    congr 1; exact ih (fun i => g i.succ)

-- retained: used by LCS.FirstOrder.Syntax.Algebra
/-- Formulae with the same symbol string are equal. Predicate atoms of
rank zero and positive rank are distinguished by their predicate symbols'
arities; compound formulae are distinguished by their symbols and subformulae. -/
theorem formula_constructor_range_distinguishable {L : Language}
    (A B : Formula L)
    (h : Formula.toSymbolList A = Formula.toSymbolList B) :
    A = B :=
-- BEGIN PROOF
by
  induction A generalizing B with
  | falsum =>
    cases B with
    | falsum => rfl
    | pred0 _ _ => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | pred0 P hP =>
    cases B with
    | pred0 Q hQ =>
      have hPQ : P = Q := by simpa using h
      subst Q; rfl
    | predN Q hQ ts =>
      have hPQ : P = Q := by
        simpa using congrArg List.head? h
      subst Q; omega
    | falsum => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | predN P hP ts =>
    cases B with
    | pred0 Q hQ =>
      have hPQ : P = Q := by
        simpa using congrArg List.head? h
      subst Q; omega
    | falsum => simp at h
    | predN Q hQ us =>
      simp only [Formula.toSymbolList_predN, List.singleton_append, List.cons_eq_cons] at h
      obtain ⟨hPQ, hrest⟩ := h; cases hPQ; congr 1
      rw [flatten_ofFn_map, flatten_ofFn_map] at hrest
      have hinj : Function.Injective (FormulaSymbol.termSym (L:=L)) :=
        fun _ _ h => FormulaSymbol.termSym.inj h
      have hterm := (List.map_inj_right hinj).mp hrest
      have : ∀ (n : Nat) (ts' us' : Fin n → Term L),
          (List.ofFn (fun i => Term.toSymbolList (ts' i))).flatten =
          (List.ofFn (fun i => Term.toSymbolList (us' i))).flatten →
          ts' = us' := by
        intro n; induction n with
        | zero => intro ts' us' _; funext i; exact i.elim0
        | succ m ihm =>
          intro ts' us' hfl
          rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons] at hfl
          have hcan := termSymList_append_cancel (ts' 0) (us' 0) _ _ hfl
          funext i; match i with
          | ⟨0, _⟩ => exact term_toSymbolList_injective _ _ hcan.1
          | ⟨k + 1, hk⟩ =>
            exact congrFun (ihm (fun j => ts' j.succ) (fun j => us' j.succ) hcan.2) ⟨k, by omega⟩
      exact this _ ts us hterm
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | eq_ _ t1 t2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ u1 u2 =>
      simp only [Formula.toSymbolList_eq] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      rw [← List.map_append, ← List.map_append] at htl
      have hinj : Function.Injective (FormulaSymbol.termSym (L:=L)) :=
        fun _ _ h => FormulaSymbol.termSym.inj h
      have hterm := (List.map_inj_right hinj).mp htl
      have hcan := termSymList_append_cancel t1 u1 _ _ hterm
      have h1 := term_toSymbolList_injective t1 u1 hcan.1
      have h2 := term_toSymbolList_injective t2 u2 hcan.2
      subst h1; subst h2; rfl
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | conj A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_conj, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | disj A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_disj, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | impl A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_impl, Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | equiv_ A1 A2 ihA1 ihA2 =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_conj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connAnd] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | disj B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_disj, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connOr] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | impl B1 B2 =>
      simp only [Formula.toSymbolList_equiv, Formula.toSymbolList_impl, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connImpl] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have := List.head_eq_of_cons_eq hcan.2; simp at this
    | equiv_ B1 B2 =>
      simp only [Formula.toSymbolList_equiv, List.cons_append] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have hcan1 := fmlaSymList_append_cancel A1 B1
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList A2 ++ [FormulaSymbol.rParen])
        ([FormulaSymbol.connEquiv] ++ Formula.toSymbolList B2 ++ [FormulaSymbol.rParen])
        (by simp [List.append_assoc] at htl ⊢; exact htl)
      have h1 := ihA1 B1 hcan1.1
      have hrest2 := List.tail_eq_of_cons_eq hcan1.2; simp at hrest2
      have h2 := ihA2 B2 hrest2
      subst h1; subst h2; rfl
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | neg A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg C =>
      simp only [Formula.toSymbolList_neg] at h
      have htl := List.tail_eq_of_cons_eq h; simp at htl
      have := ihA C htl
      subst this; rfl
    | all _ _ => simp at h
    | ex _ _ => simp at h
  | all i A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all j C =>
      simp only [Formula.toSymbolList_all] at h
      have h2 := List.tail_eq_of_cons_eq h; simp at h2
      obtain ⟨hij, hAC⟩ := h2
      have hA := ihA C hAC
      subst hij; subst hA; rfl
    | ex _ _ => simp at h
  | ex i A ihA =>
    cases B with
    | pred0 _ _ => simp at h
    | falsum => simp at h
    | predN _ _ _ => simp at h
    | eq_ _ _ _ => simp at h
    | conj _ _ => simp at h
    | disj _ _ => simp at h
    | impl _ _ => simp at h
    | equiv_ _ _ => simp at h
    | neg _ => simp at h
    | all _ _ => simp at h
    | ex j C =>
      simp only [Formula.toSymbolList_ex] at h
      have h2 := List.tail_eq_of_cons_eq h; simp at h2
      obtain ⟨hij, hAC⟩ := h2
      have hA := ihA C hAC
      subst hij; subst hA; rfl



end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
namespace FormulaFormationFn

/-- Theorem 5.2.2 (companion): The connective and quantifier formation
operations, with the variable index included in each quantifier operation. -/
@[blueprint "chap5__definition_5_2_3"]
inductive Op where
  | conj | disj | impl | equiv | neg
  | all (i : Nat)
  | ex (i : Nat)

/-- Theorem 5.2.2 (companion): Number of formula-string arguments of an operation. -/
@[blueprint "chap5__definition_5_2_3"]
abbrev Op.arity : Op → Nat
  | .conj | .disj | .impl | .equiv => 2
  | .neg | .all _ | .ex _ => 1

/-- Theorem 5.2.2 (companion): Apply a connective or indexed quantifier
formation function to arbitrary formula-symbol strings. -/
@[blueprint "chap5__definition_5_2_3"]
def Op.apply {L : Language} (op : Op)
    : (Fin op.arity → List (FormulaSymbol L)) → List (FormulaSymbol L) :=
  match op with
  | .conj => fun args => c_conj (args 0) (args 1)
  | .disj => fun args => c_disj (args 0) (args 1)
  | .impl => fun args => c_impl (args 0) (args 1)
  | .equiv => fun args => c_equiv (args 0) (args 1)
  | .neg => fun args => c_neg (args 0)
  | .all i => fun args => A_i i (args 0)
  | .ex i => fun args => E_i i (args 0)

end FormulaFormationFn
end LCS.FirstOrder.Syntax.FreeGeneration
end

section
namespace LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

/-- Theorem 5.2.2: On tuples of formula strings, the connective and
quantifier formation functions are injective, have pairwise disjoint ranges,
and never produce an atomic-formula string. Quantifier operations include
their variable indices. Formula strings are the range of `Formula.toSymbolList`. -/
@[blueprint "chap5__theorem_5_2_2" (main := true)]
theorem formula_free_generation (L : Language) :
    (∀ (op : FormulaFormationFn.Op)
      (ss us : Fin op.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = us i) →
      op.apply ss = op.apply us → ss = us) ∧
    (∀ (op other : FormulaFormationFn.Op), op ≠ other →
      ∀ (ss : Fin op.arity → List (FormulaSymbol L))
        (us : Fin other.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = us i) →
      op.apply ss ≠ other.apply us) ∧
    (∀ (op : FormulaFormationFn.Op) (ss : Fin op.arity → List (FormulaSymbol L)),
      (∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) →
      ∀ A : Formula L, A.isAtomic → op.apply ss ≠ Formula.toSymbolList A) 

end LCS.FirstOrder.Syntax.FreeGeneration
end

