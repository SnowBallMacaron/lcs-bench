import LCS.FirstOrder.Syntax.FreeGeneration
import Attach
import LCS.FirstOrder.Syntax.Parenthesized.ProofsStamp

/-! # Parenthesized term and atomic-formula notation

The notation variant in Remark (1) after Theorem 5.2.2 uses commas in
function and predicate applications and infix equality. Formation functions
act on arbitrary strings; free generation concerns the well-formed strings.
-/

namespace LCS.FirstOrder.Syntax.Parenthesized

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration

/-- Theorem 5.2.2 (companion): The formula alphabet extended by a comma. -/
@[blueprint "chap5__theorem_5_2_2"]
inductive Symbol (L : Language) where
  | original : FormulaSymbol L → Symbol L
  | comma : Symbol L

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Separate a list of strings by commas,
without a leading or trailing comma. -/
def separate {L : Language} : List (List (Symbol L)) → List (Symbol L)
  | [] => []
  | [s] => s
  | s :: t :: ss => s ++ [.comma] ++ separate (t :: ss)

/-- Theorem 5.2.2 (companion): C_f forms f(s₁,…,sₙ) from arbitrary strings. -/
@[blueprint "chap5__theorem_5_2_2"]
def functionString {L : Language} (f : L.funSymbols)
    (ss : Fin (L.funArity f) → List (Symbol L)) : List (Symbol L) :=
  [.original (.termSym (.funSym f)), .original .lParen] ++
    separate (List.ofFn ss) ++ [.original .rParen]

/-- Theorem 5.2.2 (companion): C_P forms P(s₁,…,sₙ) for predicates of
positive rank from arbitrary strings. -/
@[blueprint "chap5__theorem_5_2_2"]
def predicateString {L : Language} (P : L.predSymbols) (_hP : 0 < L.predArity P)
    (ss : Fin (L.predArity P) → List (Symbol L)) : List (Symbol L) :=
  [.original (.predSym P), .original .lParen] ++
    separate (List.ofFn ss) ++ [.original .rParen]

/-- Theorem 5.2.2 (companion): Equality formation uses infix s ≐ t. -/
@[blueprint "chap5__theorem_5_2_2"]
def equalityString {L : Language} (s t : List (Symbol L)) : List (Symbol L) :=
  s ++ [.original .eqSym] ++ t

/-- Theorem 5.2.2 (companion): Print a term in parenthesized notation. -/
@[blueprint "chap5__theorem_5_2_2"]
def termPrint {L : Language} : Term L → List (Symbol L)
  | .var x => [.original (.termSym (.varSym x))]
  | .const c => [.original (.termSym (.constSym c))]
  | .func f ts => functionString f (fun i => termPrint (ts i))

/-- Theorem 5.2.2 (companion): Connective and indexed quantifier operations
on arbitrary strings retain their original punctuation and order. -/
@[blueprint "chap5__theorem_5_2_2"]
def applyFormulaOp {L : Language} (op : FormulaFormationFn.Op)
    (ss : Fin op.arity → List (Symbol L)) : List (Symbol L) :=
  match op with
  | .conj => [.original .lParen] ++ ss 0 ++ [.original .connAnd] ++ ss 1 ++ [.original .rParen]
  | .disj => [.original .lParen] ++ ss 0 ++ [.original .connOr] ++ ss 1 ++ [.original .rParen]
  | .impl => [.original .lParen] ++ ss 0 ++ [.original .connImpl] ++ ss 1 ++ [.original .rParen]
  | .equiv => [.original .lParen] ++ ss 0 ++ [.original .connEquiv] ++ ss 1 ++ [.original .rParen]
  | .neg => [.original .connNeg] ++ ss 0
  | .all i => [.original .quantAll, .original (.varSym_ i)] ++ ss 0
  | .ex i => [.original .quantEx, .original (.varSym_ i)] ++ ss 0

/-- Theorem 5.2.2 (companion): Print rank-zero predicates and falsum as single
symbols, positive-rank predicate applications with parentheses, and equality
infix, retaining the full connective language. -/
@[blueprint "chap5__theorem_5_2_2"]
def formulaPrint {L : Language} : Formula L → List (Symbol L)
  | .falsum => [.original .falsumSym]
  | .pred0 P _ => [.original (.predSym P)]
  | .predN P h ts => predicateString P h (fun i => termPrint (ts i))
  | .eq_ _ t u => equalityString (termPrint t) (termPrint u)
  | .conj A B => applyFormulaOp .conj (vec2 (formulaPrint A) (formulaPrint B))
  | .disj A B => applyFormulaOp .disj (vec2 (formulaPrint A) (formulaPrint B))
  | .impl A B => applyFormulaOp .impl (vec2 (formulaPrint A) (formulaPrint B))
  | .equiv_ A B => applyFormulaOp .equiv (vec2 (formulaPrint A) (formulaPrint B))
  | .neg A => applyFormulaOp .neg (fun _ => formulaPrint A)
  | .all i A => applyFormulaOp (.all i) (fun _ => formulaPrint A)
  | .ex i A => applyFormulaOp (.ex i) (fun _ => formulaPrint A)

/-- Theorem 5.2.2 (companion): The variant term strings are exactly the
outputs of the parenthesized term printer. -/
@[blueprint "chap5__theorem_5_2_2"]
def isTermString {L : Language} (s : List (Symbol L)) : Prop :=
  ∃ t : Term L, termPrint t = s

/-- Theorem 5.2.2 (companion): The variant formula strings are exactly the
outputs of the parenthesized formula printer, with bare rank-zero predicates
and falsum in the atomic base. -/
@[blueprint "chap5__theorem_5_2_2"]
def isFormulaString {L : Language} (s : List (Symbol L)) : Prop :=
  ∃ A : Formula L, formulaPrint A = s

-- ATTACH-BLOCKER: private declaration
/-- Erase punctuation and all non-term letters from a variant string. -/
private def eraseTermPunctuation {L : Language} (s : List (Symbol L)) : List (TermSymbol L) :=
  s.filterMap fun a => match a with
    | .original (.termSym t) => some t
    | _ => none

-- ATTACH-BLOCKER: private declaration
private theorem eraseTermPunctuation_separate {L : Language} (ss : List (List (Symbol L))) :
    eraseTermPunctuation (separate ss) = (ss.map eraseTermPunctuation).flatten := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases ss with
    | nil => simp [separate, eraseTermPunctuation]
    | cons t ts => simpa [separate, eraseTermPunctuation] using
          (congrArg (fun u => eraseTermPunctuation s ++ u) ih)

-- ATTACH-BLOCKER: private declaration
private theorem eraseTermPunctuation_termPrint {L : Language} (t : Term L) :
    eraseTermPunctuation (termPrint t) = Term.toSymbolList t := by
  induction t with
  | var x => rfl
  | const c => rfl
  | func f ts ih =>
    simp only [termPrint, functionString, eraseTermPunctuation, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil, List.append_nil]
    change TermSymbol.funSym f :: eraseTermPunctuation (separate _) = _
    rw [eraseTermPunctuation_separate]
    simp [Term.toSymbolList, TermFormationFn.c_f, List.map_ofFn, Function.comp_def, ih]

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 5.2.2 (companion): Parenthesized term strings determine their terms. -/
theorem termPrint_injective {L : Language} (t u : Term L)
    (h : termPrint t = termPrint u) : t = u := by
  apply term_toSymbolList_injective
  simpa only [eraseTermPunctuation_termPrint] using congrArg eraseTermPunctuation h

-- ATTACH-BLOCKER: private declaration
private theorem eraseTermPunctuation_append {L : Language} (r s : List (Symbol L)) :
    eraseTermPunctuation (r ++ s) = eraseTermPunctuation r ++ eraseTermPunctuation s := by
  simp [eraseTermPunctuation]

-- ATTACH-BLOCKER: private declaration
private theorem termPrint_append_cancel {L : Language} (t u : Term L)
    (r s : List (Symbol L)) (h : termPrint t ++ r = termPrint u ++ s) :
    t = u ∧ r = s := by
  have he := congrArg eraseTermPunctuation h
  have herase (v : Term L) (xs : List (Symbol L)) :
      eraseTermPunctuation (termPrint v ++ xs) = Term.toSymbolList v ++ eraseTermPunctuation xs := by
    rw [eraseTermPunctuation_append, eraseTermPunctuation_termPrint]
  rw [herase, herase] at he
  have ht := term_toSymbolList_injective t u
    (termSymList_append_cancel t u _ _ he).1
  subst u
  exact ⟨rfl, List.append_cancel_left h⟩

-- ATTACH-BLOCKER: private declaration
private theorem termPrint_head {L : Language} (t : Term L) :
    ∃ a : TermSymbol L, ∃ r, termPrint t = Symbol.original (.termSym a) :: r := by
  cases t <;> simp [termPrint, functionString]

-- ATTACH-BLOCKER: private declaration
private theorem termArgs_append_cancel {L : Language} (n : Nat)
    (ts us : Fin n → Term L) (r s : List (TermSymbol L))
    (h : (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten ++ r =
      (List.ofFn (fun i => Term.toSymbolList (us i))).flatten ++ s) : ts = us := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc] at h
    have hc := termSymList_append_cancel (ts 0) (us 0) _ _ h
    have hz := term_toSymbolList_injective _ _ hc.1
    have ht := ih (fun i => ts i.succ) (fun i => us i.succ) hc.2
    funext i
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact hz
    | succ i => exact congrFun ht ⟨i, by omega⟩

-- ATTACH-BLOCKER: private declaration
private theorem separate_args_injective {L : Language} {n : Nat}
    (ts us : Fin n → Term L) (r s : List (Symbol L))
    (h : separate (List.ofFn (fun i => termPrint (ts i))) ++ r =
      separate (List.ofFn (fun i => termPrint (us i))) ++ s) : ts = us := by
  have he := congrArg eraseTermPunctuation h
  have herase (vs : Fin n → Term L) (xs : List (Symbol L)) :
      eraseTermPunctuation (separate (List.ofFn (fun i => termPrint (vs i))) ++ xs) =
      (List.ofFn (fun i => Term.toSymbolList (vs i))).flatten ++ eraseTermPunctuation xs := by
    rw [eraseTermPunctuation_append, eraseTermPunctuation_separate]
    simp [List.map_ofFn, Function.comp_def, eraseTermPunctuation_termPrint]
  rw [herase, herase] at he
  exact termArgs_append_cancel n ts us _ _ he

-- ATTACH-BLOCKER: private declaration
private theorem formulaPrint_append_cancel {L : Language} (A B : Formula L)
    (r s : List (Symbol L)) (h : formulaPrint A ++ r = formulaPrint B ++ s) :
    A = B ∧ r = s := by
  induction A generalizing B r s with
  | falsum  =>
    cases B with
    | falsum  =>
      exact ⟨rfl, List.append_cancel_left h⟩
    | pred0 Q hq =>
      simp [formulaPrint] at h
    | predN Q hq vs =>
      simp [formulaPrint, predicateString, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | neg B =>
      simp [formulaPrint, applyFormulaOp] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp] at h
  | pred0 P hp =>
    cases B with
    | falsum  =>
      simp [formulaPrint] at h
    | pred0 Q hq =>
      have hh := congrArg List.head? h
      have hpq : P = Q := by simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using hh
      cases hpq
      exact ⟨rfl, List.append_cancel_left h⟩
    | predN Q hq vs =>
      have hh := congrArg List.head? h
      have hpq : P = Q := by simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using hh
      cases hpq
      omega
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | neg B =>
      simp [formulaPrint, applyFormulaOp] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp] at h
  | predN P hp ts =>
    cases B with
    | falsum  =>
      simp [formulaPrint, predicateString, List.append_assoc] at h
    | pred0 Q hq =>
      have hh := congrArg List.head? h
      have hpq : P = Q := by simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using hh
      cases hpq
      omega
    | predN Q hq vs =>
      simp only [formulaPrint, predicateString, List.append_assoc, List.cons_append, List.cons.injEq, Symbol.original.injEq,
        FormulaSymbol.predSym.injEq, true_and] at h
      obtain ⟨hpq, hh⟩ := h
      cases hpq
      have hargs := separate_args_injective ts vs _ _ hh
      subst vs
      exact ⟨rfl, by simpa using hh⟩
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, predicateString, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | neg B =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
  | eq_ he t u =>
    cases B with
    | falsum  =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, equalityString, List.append_assoc, ht] at hh
    | pred0 Q hq =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, equalityString, List.append_assoc, ht] at hh
    | predN Q hq vs =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, predicateString, equalityString, List.append_assoc, ht] at hh
    | eq_ he2 v w =>
      have hc := termPrint_append_cancel t v
        ([.original .eqSym] ++ termPrint u ++ r)
        ([.original .eqSym] ++ termPrint w ++ s)
        (by simpa [formulaPrint, equalityString, List.append_assoc] using h)
      rcases hc with ⟨ht, hr⟩
      have hu := termPrint_append_cancel u w r s (by simpa using hr)
      rcases hu with ⟨hu, hrs⟩
      subst v; subst w; exact ⟨rfl, hrs⟩
    | conj B E =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | disj B E =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | impl B E =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | equiv_ B E =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | neg B =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
    | all y B =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
    | ex y B =>
      obtain ⟨a, rest, ht⟩ := termPrint_head t
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
  | conj A D ihA ihD =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | conj B E =>
      have hh : formulaPrint A ++ [.original .connAnd] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connAnd] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      have hh2 : formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint E ++ [.original .rParen] ++ s := by simpa using hr
      obtain ⟨hde, hrs⟩ := ihD E _ _ (by simpa only [List.append_assoc] using hh2)
      subst B; subst E
      exact ⟨rfl, by simpa using hrs⟩
    | disj B E =>
      have hh : formulaPrint A ++ [.original .connAnd] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connOr] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | impl B E =>
      have hh : formulaPrint A ++ [.original .connAnd] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connImpl] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | equiv_ B E =>
      have hh : formulaPrint A ++ [.original .connAnd] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connEquiv] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | neg B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
  | disj A D ihA ihD =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | conj B E =>
      have hh : formulaPrint A ++ [.original .connOr] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connAnd] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | disj B E =>
      have hh : formulaPrint A ++ [.original .connOr] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connOr] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      have hh2 : formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint E ++ [.original .rParen] ++ s := by simpa using hr
      obtain ⟨hde, hrs⟩ := ihD E _ _ (by simpa only [List.append_assoc] using hh2)
      subst B; subst E
      exact ⟨rfl, by simpa using hrs⟩
    | impl B E =>
      have hh : formulaPrint A ++ [.original .connOr] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connImpl] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | equiv_ B E =>
      have hh : formulaPrint A ++ [.original .connOr] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connEquiv] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | neg B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
  | impl A D ihA ihD =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | conj B E =>
      have hh : formulaPrint A ++ [.original .connImpl] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connAnd] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | disj B E =>
      have hh : formulaPrint A ++ [.original .connImpl] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connOr] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | impl B E =>
      have hh : formulaPrint A ++ [.original .connImpl] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connImpl] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      have hh2 : formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint E ++ [.original .rParen] ++ s := by simpa using hr
      obtain ⟨hde, hrs⟩ := ihD E _ _ (by simpa only [List.append_assoc] using hh2)
      subst B; subst E
      exact ⟨rfl, by simpa using hrs⟩
    | equiv_ B E =>
      have hh : formulaPrint A ++ [.original .connImpl] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connEquiv] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | neg B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
  | equiv_ A D ihA ihD =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, vec2, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, vec2, List.append_assoc, ht] at hh
    | conj B E =>
      have hh : formulaPrint A ++ [.original .connEquiv] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connAnd] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | disj B E =>
      have hh : formulaPrint A ++ [.original .connEquiv] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connOr] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | impl B E =>
      have hh : formulaPrint A ++ [.original .connEquiv] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connImpl] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      simp at hr
    | equiv_ B E =>
      have hh : formulaPrint A ++ [.original .connEquiv] ++ formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint B ++ [.original .connEquiv] ++ formulaPrint E ++ [.original .rParen] ++ s := by
        simpa [formulaPrint, applyFormulaOp, predicateString, equalityString, vec2, List.append_assoc] using h
      obtain ⟨hab, hr⟩ := ihA B _ _ (by simpa only [List.append_assoc] using hh)
      have hh2 : formulaPrint D ++ [.original .rParen] ++ r =
          formulaPrint E ++ [.original .rParen] ++ s := by simpa using hr
      obtain ⟨hde, hrs⟩ := ihD E _ _ (by simpa only [List.append_assoc] using hh2)
      subst B; subst E
      exact ⟨rfl, by simpa using hrs⟩
    | neg B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
  | neg A ihA =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | neg B =>
      simp only [formulaPrint, applyFormulaOp, List.cons_append, List.cons.injEq, List.nil_append, true_and] at h
      obtain ⟨hab, hrs⟩ := ihA B r s h
      subst B; exact ⟨rfl, hrs⟩
    | all y B =>
      simp [formulaPrint, applyFormulaOp] at h
    | ex y B =>
      simp [formulaPrint, applyFormulaOp] at h
  | all x A ihA =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | neg B =>
      simp [formulaPrint, applyFormulaOp] at h
    | all y B =>
      simp only [formulaPrint, applyFormulaOp, List.cons_append, List.cons.injEq, List.nil_append, true_and,
        Symbol.original.injEq, FormulaSymbol.varSym_.injEq] at h
      obtain ⟨hxy, hh⟩ := h
      cases hxy
      obtain ⟨hab, hrs⟩ := ihA B r s hh
      subst B; exact ⟨rfl, hrs⟩
    | ex y B =>
      simp [formulaPrint, applyFormulaOp] at h
  | ex x A ihA =>
    cases B with
    | falsum  =>
      simp [formulaPrint, applyFormulaOp] at h
    | pred0 Q hq =>
      simp [formulaPrint, applyFormulaOp] at h
    | predN Q hq vs =>
      simp [formulaPrint, applyFormulaOp, predicateString, List.append_assoc] at h
    | eq_ he2 v w =>
      obtain ⟨a, rest, ht⟩ := termPrint_head v
      have hh := congrArg List.head? h
      simp [formulaPrint, applyFormulaOp, equalityString, List.append_assoc, ht] at hh
    | conj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | disj B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | impl B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | equiv_ B E =>
      simp [formulaPrint, applyFormulaOp, vec2, List.append_assoc] at h
    | neg B =>
      simp [formulaPrint, applyFormulaOp] at h
    | all y B =>
      simp [formulaPrint, applyFormulaOp] at h
    | ex y B =>
      simp only [formulaPrint, applyFormulaOp, List.cons_append, List.cons.injEq, List.nil_append, true_and,
        Symbol.original.injEq, FormulaSymbol.varSym_.injEq] at h
      obtain ⟨hxy, hh⟩ := h
      cases hxy
      obtain ⟨hab, hrs⟩ := ihA B r s hh
      subst B; exact ⟨rfl, hrs⟩

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 5.2.2 (companion): Variant formula strings determine their formulae. -/
theorem formulaPrint_injective {L : Language} (A B : Formula L)
    (h : formulaPrint A = formulaPrint B) : A = B := by
  exact (formulaPrint_append_cancel A B [] [] (by simpa using h)).1

/-- Theorem 5.2.2 (companion): On tuples of term strings, each formation function C_f
is injective, and distinct function symbols give disjoint ranges. No value
of C_f is a one-letter variable or constant string. Term strings are the
range of `termPrint`. -/
@[blueprint "chap5__theorem_5_2_2"]
theorem term_free_generation (L : Language) :
    (∀ (f : L.funSymbols) (ss us : Fin (L.funArity f) → List (Symbol L)),
      (∀ i, isTermString (ss i)) →
      (∀ i, isTermString (us i)) →
      functionString f ss = functionString f us → ss = us) ∧
    (∀ (f g : L.funSymbols), f ≠ g →
      ∀ (ss : Fin (L.funArity f) → List (Symbol L))
        (us : Fin (L.funArity g) → List (Symbol L)),
      (∀ i, isTermString (ss i)) →
      (∀ i, isTermString (us i)) →
      functionString f ss ≠ functionString g us) ∧
    (∀ (f : L.funSymbols) (ss : Fin (L.funArity f) → List (Symbol L)),
      (∀ n : Nat, functionString f ss ≠ [Symbol.original (.termSym (.varSym n))]) ∧
      (∀ c : L.constSymbols, functionString f ss ≠ [Symbol.original (.termSym (.constSym c))])) 

/-- Theorem 5.2.2 (companion): On tuples of formula strings, the connective and
quantifier formation functions are injective, have pairwise disjoint ranges,
and never produce an atomic-formula string. Quantifier operations include
their variable indices. Formula strings are the range of `formulaPrint`;
the atomic base includes bare rank-zero predicates and falsum. -/
@[blueprint "chap5__theorem_5_2_2"]
theorem formula_free_generation (L : Language) :
    (∀ (op : FormulaFormationFn.Op)
      (ss us : Fin op.arity → List (Symbol L)),
      (∀ i, isFormulaString (ss i)) →
      (∀ i, isFormulaString (us i)) →
      applyFormulaOp op ss = applyFormulaOp op us → ss = us) ∧
    (∀ (op other : FormulaFormationFn.Op), op ≠ other →
      ∀ (ss : Fin op.arity → List (Symbol L))
        (us : Fin other.arity → List (Symbol L)),
      (∀ i, isFormulaString (ss i)) →
      (∀ i, isFormulaString (us i)) →
      applyFormulaOp op ss ≠ applyFormulaOp other us) ∧
    (∀ (op : FormulaFormationFn.Op) (ss : Fin op.arity → List (Symbol L)),
      (∀ i, isFormulaString (ss i)) →
      ∀ A : Formula L, A.isAtomic → applyFormulaOp op ss ≠ formulaPrint A) 

end LCS.FirstOrder.Syntax.Parenthesized
