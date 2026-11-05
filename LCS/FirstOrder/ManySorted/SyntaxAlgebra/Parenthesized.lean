import LCS.FirstOrder.ManySorted.SyntaxAlgebra
import Attach
import LCS.FirstOrder.ManySorted.SyntaxAlgebra.Parenthesized.ProofsStamp

/-! # Parenthesized many-sorted strings

Comma-separated applications and infix sorted equality, as in Remark (1)
after Theorem 10.2.1. Generation restricts arbitrary token lists to their
proper sorts; no quotient of literal strings is taken.
-/

namespace LCS.FirstOrder.ManySorted.SyntaxAlgebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Theorem 10.2.1 (companion): The source alphabet extended with a comma. -/
@[blueprint "chap10__theorem_10_2_1"]
inductive MSParenthesizedToken (L : MSLanguage) where
  | original : MSSourceToken L → MSParenthesizedToken L
  | comma : MSParenthesizedToken L

/-- Theorem 10.2.1 (companion): An ambient token list at a designated sort. Well-formedness is imposed
by the generated family, separately from this arbitrary-string carrier. -/
@[blueprint "chap10__theorem_10_2_1"]
abbrev MSParenthesizedString (L : MSLanguage) (_s : MSSyntaxSort L) :=
  List (MSParenthesizedToken L)

/-- Theorem 10.2.1 (companion): Separate arguments by commas, with no leading or trailing comma. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedSeparate {L : MSLanguage} :
    List (List (MSParenthesizedToken L)) → List (MSParenthesizedToken L)
  | [] => []
  | [w] => w
  | w :: v :: rest => w ++ [.comma] ++ msParenthesizedSeparate (v :: rest)

/-- Theorem 10.2.1 (companion): The variable generator keeps its sort and index. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedVariable (L : MSLanguage) (s : L.SortType) (i : Nat) :
    MSParenthesizedString L (some s) := [.original (msVarToken (s, i))]

/-- Theorem 10.2.1 (companion): The constant generator retains its sort. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedConstant {L : MSLanguage} (s : L.SortType) (c : L.constSymbols s) :
    MSParenthesizedString L (some s) := [.original (msConstToken ⟨s, c⟩)]

/-- Theorem 10.2.1 (companion): The function formation scheme f(t₁,…,tₙ), with the ordered
input sorts and result sort of f. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedFunction {L : MSLanguage} (f : L.funSymbols)
    (args : (i : Fin (L.funRank f).1.length) →
      MSParenthesizedString L (some ((L.funRank f).1.get i))) :
    MSParenthesizedString L (some (L.funRank f).2) :=
  [.original (msFunToken f), .original .lparen] ++
    msParenthesizedSeparate (List.ofFn args) ++ [.original .rparen]

/-- Theorem 10.2.1 (companion): The predicate formation scheme P(t₁,…,tₙ), on its ordered
data sorts. A nullary predicate remains a bare propositional letter. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedPredicate {L : MSLanguage} (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) →
      MSParenthesizedString L (some ((L.predArity P).get i))) :
    MSParenthesizedString L none :=
  if (L.predArity P).isEmpty then [.original (msPredToken P)]
  else [.original (msPredToken P), .original .lparen] ++
    msParenthesizedSeparate (List.ofFn args) ++ [.original .rparen]

/-- Theorem 10.2.1 (companion): The equality formation scheme (t₁ ≐ₛ t₂), requiring the
same data sort and the language equality flag. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedEquality {L : MSLanguage} (h : L.hasEquality = true)
    (s : L.SortType) (t u : MSParenthesizedString L (some s)) :
    MSParenthesizedString L none :=
  [.original .lparen] ++ t ++ [.original (.eq_ h s)] ++ u ++ [.original .rparen]

/-- Theorem 10.2.1 (companion): Every expanded constructor acts on arbitrary strings; connective
and sorted quantifier punctuation is the original source punctuation. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedOperation {L : MSLanguage} (op : MSConstructorSymbol L)
    (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
      MSParenthesizedString L (((msConstructorAlphabet L).argSorts op).get i)) :
    MSParenthesizedString L ((msConstructorAlphabet L).resultSort op) := by
  cases op <;> dsimp only [MSRankedAlphabet.argSorts, MSRankedAlphabet.resultSort,
    msConstructorAlphabet, msConstructorRank] at args ⊢
  case const s c => exact msParenthesizedConstant s c
  case func f => exact msParenthesizedFunction f (fun i => args ⟨i.val, by simpa using i.isLt⟩)
  case pred P => exact msParenthesizedPredicate P (fun i => args ⟨i.val, by simpa using i.isLt⟩)
  case eq_ h s => exact msParenthesizedEquality h s (args 0) (args 1)
  case falsum => exact [.original .falsum]
  case conj => exact [.original .lparen] ++ args 0 ++ [.original .conj] ++ args 1 ++ [.original .rparen]
  case disj => exact [.original .lparen] ++ args 0 ++ [.original .disj] ++ args 1 ++ [.original .rparen]
  case impl => exact [.original .lparen] ++ args 0 ++ [.original .impl] ++ args 1 ++ [.original .rparen]
  case equiv_ => exact [.original .lparen] ++ args 0 ++ [.original .equiv_] ++ args 1 ++ [.original .rparen]
  case neg => exact .original .neg :: args 0
  case all s i => exact .original (.all s) :: .original (msVarToken (s, i)) :: args 0
  case ex s i => exact .original (.ex s) :: .original (msVarToken (s, i)) :: args 0

/-- Theorem 10.2.1 (companion): Sorted parenthesized strings generated by V under the expanded
constructors. The indices enforce sort constraints on all generated arguments. -/
@[blueprint "chap10__theorem_10_2_1"]
inductive MSParenthesizedGenerated (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop where
  | var (s : L.SortType) (i : Nat) :
      MSParenthesizedGenerated L (some s) (msParenthesizedVariable L s i)
  | operation (op : MSConstructorSymbol L)
      (args : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
        MSParenthesizedString L (((msConstructorAlphabet L).argSorts op).get i))
      (generated : ∀ i, MSParenthesizedGenerated L (((msConstructorAlphabet L).argSorts op).get i) (args i)) :
      MSParenthesizedGenerated L ((msConstructorAlphabet L).resultSort op) (msParenthesizedOperation op args)

/-- Theorem 10.2.1 (companion): The ranked parenthesized algebra on arbitrary
strings. Its well-formed subalgebra is generated separately. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedAmbientAlgebra (L : MSLanguage) :
    LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L) where
  carrier := MSParenthesizedString L
  carrierNonempty := fun _ => ⟨[]⟩
  operation := msParenthesizedOperation

/-- Theorem 10.2.1 (companion): The actual algebra of generated parenthesized
strings, with operations restricted to correctly sorted generated arguments. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedAlgebra (L : MSLanguage) :
    LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L) where
  carrier := fun s => {w : MSParenthesizedString L s // MSParenthesizedGenerated L s w}
  carrierNonempty := by
    intro s
    cases s with
    | some s => exact ⟨⟨msParenthesizedVariable L s 0, .var s 0⟩⟩
    | none => exact ⟨⟨[.original .falsum],
        .operation .falsum (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)⟩⟩
  operation := fun op args =>
    ⟨msParenthesizedOperation op (fun i => (args i).val),
      .operation op (fun i => (args i).val) (fun i => (args i).property)⟩

/-- Theorem 10.2.1 (companion): Freeness of an actual sorted family C of
ambient strings over generators G and a chosen set of operation labels O.
Generation means containment, closure and leastness. The three freeness clauses
are injectivity on C-tuples, separation for distinct full labels, and exclusion
of generator values. Separation compares underlying token strings even when
result sorts differ. No injectivity is asserted on arbitrary malformed strings. -/
@[blueprint "chap10__theorem_10_2_1"]
structure MSParenthesizedFreeness (L : MSLanguage)
    (C G : (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop)
    (O : MSConstructorSymbol L → Prop) : Prop where
  contains : ∀ s w, G s w → C s w
  closed : ∀ op, O op → ∀ args, (∀ i, C (((msConstructorAlphabet L).argSorts op).get i) (args i)) →
    C ((msConstructorAlphabet L).resultSort op) (msParenthesizedOperation (L := L) op args)
  least : ∀ D : (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop,
    (∀ s w, G s w → D s w) →
    (∀ op, O op → ∀ args, (∀ i, D (((msConstructorAlphabet L).argSorts op).get i) (args i)) →
      D ((msConstructorAlphabet L).resultSort op) (msParenthesizedOperation (L := L) op args)) →
    ∀ s w, C s w → D s w
  free :
    (∀ op, O op → ∀ args more,
      (∀ i, C (((msConstructorAlphabet L).argSorts op).get i) (args i)) → (∀ i, C (((msConstructorAlphabet L).argSorts op).get i) (more i)) →
      msParenthesizedOperation (L := L) op args =
        msParenthesizedOperation (L := L) op more → args = more) ∧
    (∀ op other, O op → O other → op ≠ other → ∀ args more,
      (∀ i, C (((msConstructorAlphabet L).argSorts op).get i) (args i)) → (∀ i, C (((msConstructorAlphabet L).argSorts other).get i) (more i)) →
      (msParenthesizedOperation (L := L) op args) ≠
        (msParenthesizedOperation (L := L) other more)) ∧
    (∀ op, O op → ∀ args, (∀ i, C (((msConstructorAlphabet L).argSorts op).get i) (args i)) →
      ¬ G ((msConstructorAlphabet L).resultSort op) (msParenthesizedOperation (L := L) op args))

/-- Theorem 10.2.1 (companion): V as a family of actual singleton strings;
its Boolean component is empty. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedVariableGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop
  | some s, w => ∃ i, msParenthesizedVariable L s i = w
  | none, _ => False

/-- Theorem 10.2.1 (companion): The term-string family, with empty
Boolean component, inherited from the generated string algebra. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedTermCarrier (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop
  | some s, w => MSParenthesizedGenerated L (some s) w
  | none, _ => False

/-- Theorem 10.2.1 (companion): Separate term generators are exactly
singleton variables and constants of the requested data sort. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedTermGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop
  | some s, w => (∃ i, msParenthesizedVariable L s i = w) ∨
      (∃ c, msParenthesizedConstant s c = w)
  | none, _ => False

/-- Theorem 10.2.1 (companion): Atomic strings are bottom, predicates
on generated term strings (including empty arity), or available same-sort
equalities on generated term strings. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedAtomic {L : MSLanguage} (w : MSParenthesizedString L none) : Prop :=
  w = ([.original .falsum] : MSParenthesizedString L none) ∨
  (∃ (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) →
      MSParenthesizedString L (some ((L.predArity P).get i))),
    (∀ i, MSParenthesizedGenerated L (some ((L.predArity P).get i)) (args i)) ∧ msParenthesizedPredicate P args = w) ∨
  (∃ (h : L.hasEquality = true) (s : L.SortType)
    (t u : MSParenthesizedString L (some s)),
    MSParenthesizedGenerated L (some s) t ∧ MSParenthesizedGenerated L (some s) u ∧
      msParenthesizedEquality h s t u = w)

/-- Theorem 10.2.1 (companion): The formula-string family is the
Boolean generated carrier, with empty data components. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedFormulaCarrier (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop
  | none, w => MSParenthesizedGenerated L none w
  | some _, _ => False

/-- Theorem 10.2.1 (companion): Separate formula generators are the
atomic strings, all at bool. -/
@[blueprint "chap10__theorem_10_2_1"]
def msParenthesizedFormulaGenerators (L : MSLanguage) :
    (s : MSSyntaxSort L) → MSParenthesizedString L s → Prop
  | none, w => msParenthesizedAtomic w
  | some _, _ => False


/-- Theorem 10.2.1 (companion): Parenthesized strings are freely generated by the sorted variables. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesized_free_generation (L : MSLanguage) :
    MSParenthesizedFreeness L (MSParenthesizedGenerated L)
      (msParenthesizedVariableGenerators L) (fun _ => True)

/-- Theorem 10.2.1 (companion): Parenthesized terms are freely generated by variables and constants. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesizedTerm_free_generation (L : MSLanguage) :
    MSParenthesizedFreeness L (msParenthesizedTermCarrier L)
      (msParenthesizedTermGenerators L) msTermStringOperations

/-- Theorem 10.2.1 (companion): Parenthesized formulae are freely generated by atomic formulae. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesizedFormula_free_generation (L : MSLanguage) :
    MSParenthesizedFreeness L (msParenthesizedFormulaCarrier L)
      (msParenthesizedFormulaGenerators L) msFormulaStringOperations

/-- Theorem 10.2.1 (companion): Function application preserves the specified generated data sort. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesizedFunction_formation {L : MSLanguage} (f : L.funSymbols)
    (args : (i : Fin (L.funRank f).1.length) → MSParenthesizedString L (some ((L.funRank f).1.get i)))
    (h : ∀ i, MSParenthesizedGenerated L (some ((L.funRank f).1.get i)) (args i)) :
    MSParenthesizedGenerated L (some (L.funRank f).2) (msParenthesizedFunction f args)

/-- Theorem 10.2.1 (companion): Predicate application to terms of its input sorts is a formula. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesizedPredicate_formation {L : MSLanguage} (P : L.predSymbols)
    (args : (i : Fin (L.predArity P).length) → MSParenthesizedString L (some ((L.predArity P).get i)))
    (h : ∀ i, MSParenthesizedGenerated L (some ((L.predArity P).get i)) (args i)) :
    msParenthesizedAtomic (msParenthesizedPredicate P args)

/-- Theorem 10.2.1 (companion): Equality of two terms of the same sort is an atomic formula. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msParenthesizedEquality_formation {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (t u : MSParenthesizedString L (some s))
    (ht : MSParenthesizedGenerated L (some s) t) (hu : MSParenthesizedGenerated L (some s) u) :
    msParenthesizedAtomic (msParenthesizedEquality hL s t u)

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
