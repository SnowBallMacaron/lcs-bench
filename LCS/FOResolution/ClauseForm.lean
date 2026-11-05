import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.SHGTheorem
import Attach
import LCS.FOResolution.ClauseForm.ProofsStamp

/-! # FOResolution.ClauseForm (Section 8.2)
    Source: Logic for Computer Science, Gallier 2015

    Formulae in clause form: first-order literals, clauses, ground clauses,
    and conversion to clause form.
-/

namespace LCS.FOResolution.ClauseForm

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- General carrier: First-order literals
-- ===================================================================

/-- The general atomic formula carried by a
    first-order literal. The two constructors are exactly the atomic
    forms of `FormulaN`: predicate applications and equality formulae.
    The equality constructor retains the language's equality witness. -/
@[blueprint "chap8__definition_8_2_1"]
inductive FOAtomCore (L : Language) : Type where
  | predN : (P : L.predSymbols) →
      (Fin (L.predArity P) → Term L) → FOAtomCore L
  | eq_ : L.hasEquality = true → Term L → Term L → FOAtomCore L

namespace FOAtomCore

/-- Embed an atomic carrier into the ambient normalized formula type. -/
@[blueprint "chap8__definition_8_2_1"]
def toFormula {L : Language} : FOAtomCore L → FormulaN L
  | .predN P args => .predN P args
  | .eq_ hL lhs rhs => .eq_ hL lhs rhs

-- ATTACH-BLOCKER: unsupported untagged instance
instance {L : Language} : Coe (FOAtomCore L) (FormulaN L) :=
  ⟨toFormula⟩

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.HornClauses, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- The embedding of atomic carriers into formulae is injective. -/
theorem toFormula_injective {L : Language} :
    Function.Injective (@toFormula L) := by
  intro A B h
  cases A <;> cases B <;> simp_all [toFormula]

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Parse an ambient formula as an atomic carrier. Non-atomic formulae
    are rejected visibly with `none`. -/
def ofFormula? {L : Language} : FormulaN L → Option (FOAtomCore L)
  | .predN P args => some (.predN P args)
  | .eq_ hL lhs rhs => some (.eq_ hL lhs rhs)
  | .neg _ | .conj _ _ | .disj _ _ | .impl _ _ | .all _ _ | .ex _ _ =>
      none





-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Proof-indexed parsing of a formula known to be atomic. -/
def ofFormula {L : Language} (A : FormulaN L)
    (hAtomic : FormulaN.isAtomic A = true) : FOAtomCore L := by
  cases A with
  | predN P args => exact .predN P args
  | eq_ hL lhs rhs => exact .eq_ hL lhs rhs
  | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
      simp [FormulaN.isAtomic] at hAtomic



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The atomic carrier makes atomicity derivable by construction. -/
theorem toFormula_isAtomic {L : Language} (A : FOAtomCore L) :
    FormulaN.isAtomic A.toFormula = true := by
  cases A <;> rfl

/-- Apply a structural transformation to every term of an atom. -/
@[blueprint "chap8__definition_8_5_2"]
def mapTerms {L : Language} (f : Term L → Term L) : FOAtomCore L → FOAtomCore L
  | .predN P args => .predN P (fun i => f (args i))
  | .eq_ hL lhs rhs => .eq_ hL (f lhs) (f rhs)

end FOAtomCore

/-- General carrier: A first-order literal is either an atomic formula B
    (the pos case) or the negation of an atomic formula (the neg case). -/
@[blueprint "chap8__definition_8_2_1"]
inductive FOLiteralCore (L : Language) : Type where
  /-- A literal that is an atomic formula B -/
  | pos : FOAtomCore L → FOLiteralCore L
  /-- A literal that is the negation of an atomic formula B -/
  | neg : FOAtomCore L → FOLiteralCore L

-- ===================================================================
-- General carrier: FOClauseCore
-- ===================================================================

/-- General carrier: A first-order clause is a disjunction of literals,
    represented as a list of FOLiterals (universal quantifiers implicit). -/
@[blueprint "chap8__definition_8_2_1"]
abbrev FOClauseCore (L : Language) : Type := List (FOLiteralCore L)

-- ===================================================================
-- General carrier: FOClauseFormCore
-- ===================================================================

/-- General carrier: A sentence in clause form is a conjunction of
    clauses, represented as a list of FOClauses. -/
@[blueprint "chap8__definition_8_2_1"]
abbrev FOClauseFormCore (L : Language) : Type := List (FOClauseCore L)

-- ===================================================================
-- General carrier: FOLiteralCore.conjugate
-- ===================================================================

namespace FOLiteralCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- General carrier: The conjugate of a first-order literal flips its
    sign: pos B has conjugate neg B, and neg B has conjugate pos B. -/
def conjugate {L : Language} : FOLiteralCore L → FOLiteralCore L
  | .pos B => .neg B
  | .neg B => .pos B

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- General carrier: Extract the underlying formula from a first-order literal. -/
def formula {L : Language} : FOLiteralCore L → FormulaN L
  | .pos B => B.toFormula
  | .neg B => B.toFormula

end FOLiteralCore

namespace FOClauseCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- General carrier: Every literal in a first-order clause
    wraps an atomic formula (a predicate application or an equality). -/
def allAtomic {L : Language} (c : FOClauseCore L) : Prop :=
  ∀ lit ∈ c, FormulaN.isAtomic lit.formula = true



end FOClauseCore

-- ===================================================================
-- Helper: collect variables from terms and formulae
-- ===================================================================

/-- General carrier: Collect all variable indices occurring in a term. -/
@[blueprint "chap8__definition_8_2_1"]
def termVars {L : Language} : Term L → Set Nat
  | .var n => fun m => m = n
  | .const _ => fun _ => False
  | .func _ args => fun m => ∃ i, termVars (args i) m

namespace FOAtomCore

/-- Collect all variable indices occurring in an atomic carrier. -/
@[blueprint "chap8__definition_8_2_1"]
def vars {L : Language} : FOAtomCore L → Set Nat
  | .predN _ args => fun m => ∃ i, termVars (args i) m
  | .eq_ _ lhs rhs => fun m => termVars lhs m ∨ termVars rhs m

end FOAtomCore

/-- General carrier: Collect all variable indices occurring in a formula. -/
@[blueprint "chap8__definition_8_2_1"]
def formulaVars {L : Language} : FormulaN L → Set Nat
  | .predN _ args => fun m => ∃ i, termVars (args i) m
  | .eq_ _ t1 t2 => fun m => termVars t1 m ∨ termVars t2 m
  | .conj A B => fun m => formulaVars A m ∨ formulaVars B m
  | .disj A B => fun m => formulaVars A m ∨ formulaVars B m
  | .impl A B => fun m => formulaVars A m ∨ formulaVars B m
  | .neg A => formulaVars A
  | .all _ A => formulaVars A
  | .ex _ A => formulaVars A

namespace FOAtomCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Variable collection agrees with the ambient-formula embedding. -/
theorem vars_eq_formulaVars {L : Language} (atom : FOAtomCore L) :
    atom.vars = formulaVars atom.toFormula := by
  cases atom <;> rfl

end FOAtomCore

-- ===================================================================
-- General carrier: FOLiteralCore variable collection
-- ===================================================================

namespace FOLiteralCore

/-- General carrier: Collect all variable indices occurring in a first-order literal. -/
@[blueprint "chap8__definition_8_2_1"]
def vars {L : Language} (lit : FOLiteralCore L) : Set Nat :=
  match lit with
  | .pos atom | .neg atom => atom.vars

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Literal variables are exactly the variables of its embedded atom. -/
theorem vars_eq_formulaVars {L : Language} (lit : FOLiteralCore L) :
    lit.vars = formulaVars lit.formula := by
  cases lit <;> apply FOAtomCore.vars_eq_formulaVars

end FOLiteralCore

namespace FOClauseCore

/-- General carrier: Collect all variable indices occurring in a clause. -/
@[blueprint "chap8__definition_8_2_1"]
def vars {L : Language} (c : FOClauseCore L) : Set Nat :=
  fun m => ∃ lit, lit ∈ c ∧ lit.vars m

end FOClauseCore

-- ===================================================================
-- General carrier: FOClauseCore.isGround
-- ===================================================================

namespace FOClauseCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- General carrier: A ground clause has no quantifiers and contains
    no variables (every literal references only ground terms). -/
def isGround {L : Language} (c : FOClauseCore L) : Prop :=
  c.vars = Set.empty

end FOClauseCore

-- ===================================================================
-- General carrier: FOClauseFormCore.hasDisjointBoundVars
-- ===================================================================

namespace FOClauseFormCore

/-- General carrier: For any two distinct clauses in the clause form,
    their sets of variables are disjoint (disjoint bound variables). -/
@[blueprint "chap8__definition_8_2_1"]
def hasDisjointBoundVars {L : Language}
    (cf : FOClauseFormCore L) : Prop :=
  ∀ (i j : Fin cf.length), i ≠ j →
    Set.inter (FOClauseCore.vars (cf.get i)) (FOClauseCore.vars (cf.get j)) = Set.empty

end FOClauseFormCore

-- ===================================================================
/-- Definition 8.2.1: Atomic data in a language without equality. -/
@[blueprint "chap8__definition_8_2_1"]
abbrev FOAtom (L : Language) (_hL : L.withoutEquality) : Type := FOAtomCore L

/-- Definition 8.2.1: A literal is an atom or its immediate negation,
    in the standing equality-free language. -/
@[blueprint "chap8__definition_8_2_1" (main := true)]
abbrev FOLiteral (L : Language) (_hL : L.withoutEquality) : Type := FOLiteralCore L

/-- Definition 8.2.1: A clause matrix is a list of equality-free literals;
    universal quantifiers are implicit in this matrix representation. -/
@[blueprint "chap8__definition_8_2_1"]
abbrev FOClause (L : Language) (hL : L.withoutEquality) : Type := List (FOLiteral L hL)

/-- Definition 8.2.1: The clause matrices of an equality-free clause form. -/
@[blueprint "chap8__definition_8_2_1"]
abbrev FOClauseForm (L : Language) (hL : L.withoutEquality) : Type := List (FOClause L hL)

namespace FOLiteral

/-- Definition 8.2.1: Conjugation reverses the literal's sign. -/
@[blueprint "chap8__definition_8_2_1"]
def conjugate {L : Language} (hL : L.withoutEquality) :
    FOLiteral L hL → FOLiteral L hL := FOLiteralCore.conjugate

/-- Definition 8.2.1 (companion): The literal's underlying atomic formula. -/
@[blueprint "chap8__definition_8_2_1"]
def formula {L : Language} (hL : L.withoutEquality) :
    FOLiteral L hL → FormulaN L := FOLiteralCore.formula

/-- Definition 8.2.1 (companion): Variables of an equality-free literal. -/
@[blueprint "chap8__definition_8_2_1"]
def vars {L : Language} (hL : L.withoutEquality) :
    FOLiteral L hL → Set Nat := FOLiteralCore.vars

end FOLiteral

namespace FOClause

/-- Definition 8.2.1 (companion): Every clause literal has an atomic matrix. -/
@[blueprint "chap8__definition_8_2_1"]
def allAtomic {L : Language} (hL : L.withoutEquality) (c : FOClause L hL) : Prop :=
  FOClauseCore.allAtomic c

/-- Definition 8.2.1 (companion): Variables of a clause matrix. -/
@[blueprint "chap8__definition_8_2_1"]
def vars {L : Language} (hL : L.withoutEquality) (c : FOClause L hL) : Set Nat :=
  FOClauseCore.vars c

/-- Definition 8.2.1: A ground clause matrix contains no variables. -/
@[blueprint "chap8__definition_8_2_1"]
def isGround {L : Language} (hL : L.withoutEquality) (c : FOClause L hL) : Prop :=
  FOClauseCore.isGround c

end FOClause

/-- Definition 8.2.1: Distinct clause occurrences have disjoint sets of
    actual bound names, including vacuous binders. The input consists of
    formula clauses with explicit prefixes, separately from clause matrices. -/
@[blueprint "chap8__definition_8_2_1"]
def FOClauseForm.hasDisjointBoundVars {L : Language} (_hL : L.withoutEquality)
    (clauses : List (FormulaN L)) : Prop :=
  ∀ (i j : Fin clauses.length), i ≠ j →
    Set.inter (formulaBVN (clauses.get i)) (formulaBVN (clauses.get j)) = Set.empty

-- ===================================================================
-- Example 8.2.1: Clause form conversion example
-- ===================================================================

/-- Example 8.2.1 (companion): Predicate symbols for the example language: one binary
    predicate P. -/
@[blueprint "chap8__example_8_2_1"]
inductive ExClausePred : Type where
  | P : ExClausePred

/-- Example 8.2.1 (companion): Function symbols for the example language: one unary
    Skolem function f. -/
@[blueprint "chap8__example_8_2_1"]
inductive ExClauseFunc : Type where
  | f : ExClauseFunc

/-- Example 8.2.1 (companion): Constant symbols for the example language: one Skolem
    constant a. -/
@[blueprint "chap8__example_8_2_1"]
inductive ExClauseConst : Type where
  | a : ExClauseConst

/-- Example 8.2.1 (companion): A first-order language with one binary predicate P,
    one constant a (Skolem constant), and one unary function f (Skolem
    function). -/
@[blueprint "chap8__example_8_2_1"]
def exClauseFormLang : Language where
  funSymbols := ExClauseFunc
  funArity := fun | .f => 1
  constSymbols := ExClauseConst
  predSymbols := ExClausePred
  predArity := fun | .P => 2
  hasEquality := false

/-- Example 8.2.1 (companion): The Skolem constant a, introduced to eliminate the
    outermost existential quantifier exists y. -/
@[blueprint "chap8__example_8_2_1"]
def exSkolemConst_a : Term exClauseFormLang :=
  Term.const ExClauseConst.a

/-- Example 8.2.1 (companion): The Skolem function f(z), introduced to eliminate the
    inner existential quantifier exists x under forall z. Takes the bound
    variable index as argument and returns the term f(z). -/
@[blueprint "chap8__example_8_2_1"]
def exSkolemFunc_f (z : Nat) : Term exClauseFormLang :=
  Term.func ExClauseFunc.f (fun _ => Term.var z)

/-- Example 8.2.1 (companion): build a binary predicate application P(t1, t2) in the example
    language. -/
@[blueprint "chap8__example_8_2_1"]
def exPred_P (t1 t2 : Term exClauseFormLang) : FOAtom exClauseFormLang rfl :=
  .predN ExClausePred.P (vec2 t1 t2)

/-- Example 8.2.1 (companion): The input signature contains only the
    binary predicate P. The later constant a and unary function f are fresh
    because the input has no constant or function symbols. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseInputLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExClausePred
  predArity := fun | .P => 2
  hasEquality := false

/-- Example 8.2.1 (companion): P in the original predicate-only signature. -/
@[blueprint "chap8__example_8_2_1"]
def exInputPred_P (t1 t2 : Term exClauseInputLang) : FormulaN exClauseInputLang :=
  .predN .P (vec2 t1 t2)

/-- Example 8.2.1: The original sentence
    A = ¬∃y ∀z (P(z,y) ≡ ¬∃x (P(z,x) ∧ P(x,z))).
    Following the standing abbreviation for ≡, its two implications are
    explicit. Their copies of the local existential have separate binding
    identities x=4 and u=5; y=0 and z=1. This is the alpha-renamed form of
    the printed abbreviation, with the right copy fresh as in SQ05. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseOriginal : FormulaN exClauseInputLang :=
  .neg (.ex 0 (.all 1
    (.conj
      (.impl (exInputPred_P (.var 1) (.var 0))
        (.neg (.ex 4 (.conj (exInputPred_P (.var 1) (.var 4))
          (exInputPred_P (.var 4) (.var 1))))))
      (.impl (.neg (.ex 5 (.conj (exInputPred_P (.var 1) (.var 5))
          (exInputPred_P (.var 5) (.var 1)))))
        (exInputPred_P (.var 1) (.var 0))))))

/-- Example 8.2.1: Negate A and eliminate the biconditional and implications.
    The left existential x=4 and the right existential u=5 have disjoint
    scopes; the latter is the renamed copy of the second printed x. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseEliminated : FormulaN exClauseInputLang :=
  .ex 0 (.all 1
    (.conj
      (.disj (.neg (exInputPred_P (.var 1) (.var 0)))
        (.neg (.ex 4 (.conj (exInputPred_P (.var 1) (.var 4))
          (exInputPred_P (.var 4) (.var 1))))))
      (.disj (.ex 5 (.conj (exInputPred_P (.var 1) (.var 5))
          (exInputPred_P (.var 5) (.var 1))))
        (exInputPred_P (.var 1) (.var 0)))))

/-- Example 8.2.1: The NNF stage. The left binder becomes ∀x, whereas
    the right binder remains ∃u. The universal scope of u is only z,
    since the left ∀x does not enclose the right conjunct. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseNNF : FormulaN exClauseInputLang :=
  .ex 0 (.all 1
    (.conj
      (.disj (.neg (exInputPred_P (.var 1) (.var 0)))
        (.all 4 (.disj (.neg (exInputPred_P (.var 1) (.var 4)))
          (.neg (exInputPred_P (.var 4) (.var 1))))))
      (.disj (.ex 5 (.conj (exInputPred_P (.var 1) (.var 5))
          (exInputPred_P (.var 5) (.var 1))))
        (exInputPred_P (.var 1) (.var 0)))))

/-- Example 8.2.1: The Skolem stage replaces y by fresh a and u by f(z).
    The left universal x remains; f has exactly the one argument z. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseSkolem : FormulaN exClauseFormLang :=
  .all 1
    (.conj
      (.disj (.neg (exPred_P (.var 1) exSkolemConst_a).toFormula)
        (.all 4 (.disj (.neg (exPred_P (.var 1) (.var 4)).toFormula)
          (.neg (exPred_P (.var 4) (.var 1)).toFormula))))
      (.disj (.conj (exPred_P (.var 1) (exSkolemFunc_f 1)).toFormula
          (exPred_P (exSkolemFunc_f 1) (.var 1)).toFormula)
        (exPred_P (.var 1) exSkolemConst_a).toFormula))

/-- Example 8.2.1: The prenex stage has prefix ∀z ∀x; x is absent
    from the right conjunct, so its binder can be moved outward. -/
@[blueprint "chap8__example_8_2_1"]
def exClausePrenex : FormulaN exClauseFormLang :=
  .all 1 (.all 4
    (.conj
      (.disj (.neg (exPred_P (.var 1) exSkolemConst_a).toFormula)
        (.disj (.neg (exPred_P (.var 1) (.var 4)).toFormula)
          (.neg (exPred_P (.var 4) (.var 1)).toFormula)))
      (.disj (.conj (exPred_P (.var 1) (exSkolemFunc_f 1)).toFormula
          (exPred_P (exSkolemFunc_f 1) (.var 1)).toFormula)
        (exPred_P (.var 1) exSkolemConst_a).toFormula)))

/-- Example 8.2.1: The CNF stage under the adopted SQ06 reading:
    distribute ∨ over ∧, giving C1 ∧ (C2 ∧ C3) beneath ∀z ∀x.
    The third conjunct is P(f(z),z) ∨ P(z,a). Clause-local renaming
    and omission of the vacuous x binders yield the separate matrices below. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseCNF : FormulaN exClauseFormLang :=
  .all 1 (.all 4
    (.conj
      (.disj (.neg (exPred_P (.var 1) exSkolemConst_a).toFormula)
        (.disj (.neg (exPred_P (.var 1) (.var 4)).toFormula)
          (.neg (exPred_P (.var 4) (.var 1)).toFormula)))
      (.conj
        (.disj (exPred_P (.var 1) (exSkolemFunc_f 1)).toFormula
          (exPred_P (.var 1) exSkolemConst_a).toFormula)
        (.disj (exPred_P (exSkolemFunc_f 1) (.var 1)).toFormula
          (exPred_P (.var 1) exSkolemConst_a).toFormula))))

/-- Example 8.2.1: Clause C1 = neg P(z_1, a) lor neg P(z_1, x) lor
    neg P(x, z_1). Variables: z_1 = 1, x = 4. -/
@[blueprint "chap8__example_8_2_1"]
def exClause_C1 : FOClause exClauseFormLang rfl :=
  [ .neg (exPred_P (Term.var 1) exSkolemConst_a),
    .neg (exPred_P (Term.var 1) (Term.var 4)),
    .neg (exPred_P (Term.var 4) (Term.var 1)) ]

/-- Example 8.2.1: Clause C2 = P(z_2, f(z_2)) lor P(z_2, a).
    Variable: z_2 = 2. -/
@[blueprint "chap8__example_8_2_1"]
def exClause_C2 : FOClause exClauseFormLang rfl :=
  [ .pos (exPred_P (Term.var 2) (exSkolemFunc_f 2)),
    .pos (exPred_P (Term.var 2) exSkolemConst_a) ]

/-- Example 8.2.1: Clause C3 = P(f(z_3), z_3) lor P(z_3, a).
    Variable: z_3 = 3. -/
@[blueprint "chap8__example_8_2_1"]
def exClause_C3 : FOClause exClauseFormLang rfl :=
  [ .pos (exPred_P (exSkolemFunc_f 3) (Term.var 3)),
    .pos (exPred_P (Term.var 3) exSkolemConst_a) ]

/-- Example 8.2.1: The complete clause form conversion of the textbook's
    sentence A, yielding the three clauses C1, C2, C3. -/
@[blueprint "chap8__example_8_2_1" (main := true)]
def exClauseFormConversion : FOClauseForm exClauseFormLang rfl :=
  [exClause_C1, exClause_C2, exClause_C3]

-- ===================================================================
-- Lemma 8.2.1: Required definitions and theorem
-- ===================================================================

open LCS.FirstOrder.Semantics
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Semantics.Subformulae

namespace Formula

/-- Lemma 8.2.1 (companion): A first-order formula is unsatisfiable iff
    it is not satisfiable in any structure. -/
@[blueprint "chap8__lemma_8_2_1"]
def isUnsatisfiable {L : Language} (A : FormulaN L) : Prop :=
  ¬ ∃ (M : Structure L) (s : Assignment M), formulaEvalN M A s

end Formula

namespace Formula

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A clause literal is an atomic predicate/equality formula or its
    immediate negation. -/
def isClauseLiteral {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg (.predN _ _) => True
  | .neg (.eq_ _ _ _) => True
  | _ => False

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A clause matrix is a nonempty disjunction tree whose leaves are
    clause literals. -/
def isDisjunctionOfLiterals {L : Language} : FormulaN L → Prop
  | .disj A B =>
      Formula.isDisjunctionOfLiterals A ∧
      Formula.isDisjunctionOfLiterals B
  | A => Formula.isClauseLiteral A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A CNF matrix is a nonempty conjunction tree whose leaves are
    disjunctions of literals. -/
def isCNFMatrix {L : Language} : FormulaN L → Prop
  | .conj A B => Formula.isCNFMatrix A ∧ Formula.isCNFMatrix B
  | A => Formula.isDisjunctionOfLiterals A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 8.2.1 (companion): Split a formula's top-level conjunctions
    into the list of conjuncts. A non-conjunction is a singleton list. -/
def splitConj {L : Language} : FormulaN L → List (FormulaN L)
  | .conj A B => splitConj A ++ splitConj B
  | A => [A]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Universal-prefix/disjunction grammar over an arbitrary language.
    This shape predicate does not assert closure or distinct bound names. -/
def isUniversalClauseShape {L : Language} : FormulaN L → Prop
  | .all _ A => isUniversalClauseShape A
  | A => isDisjunctionOfLiterals A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Conjunctions of universal-prefix/disjunction shapes. Prepared prefix
    distribution preserves this grammar, even when names are shared. -/
def isClauseFormShape {L : Language} : FormulaN L → Prop
  | .conj A B => isClauseFormShape A ∧ isClauseFormShape B
  | A => isUniversalClauseShape A

/-- Definition 8.2.1: A clause is a closed universal-prefix disjunction
    of literals in an equality-free language. Prefix names are distinct;
    zero-length prefixes and vacuous quantifiers are allowed. -/
@[blueprint "chap8__definition_8_2_1"]
def isUniversalClause {L : Language} (_hL : L.withoutEquality) (A : FormulaN L) : Prop :=
  FormulaN.isClosed A ∧ (formulaBoundVarIndices A).Nodup ∧ isUniversalClauseShape A

/-- Lemma 8.2.1 (companion): A clause-form sentence is a nonempty
    syntactic conjunction of closed universal clauses whose actual bound
    names are pairwise disjoint, including names of vacuous binders. -/
@[blueprint "chap8__lemma_8_2_1"]
def isClauseForm {L : Language} (hL : L.withoutEquality) (A : FormulaN L) : Prop :=
  FormulaN.isClosed A ∧
    (∀ C ∈ splitConj A, isUniversalClause hL C) ∧
    FOClauseForm.hasDisjointBoundVars hL (splitConj A)

end Formula

namespace Formula

/-- Lemma 8.2.1 (companion): A formula is valid iff it is universally
    valid (true in every structure under every assignment). -/
@[blueprint "chap8__lemma_8_2_1"]
def isValid {L : Language} (A : FormulaN L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s

end Formula

namespace Formula

/-- Lemma 8.2.1 (companion): Predicate that a formula is in prenex form:
    all quantifiers appear at the front, preceding the quantifier-free
    matrix. -/
@[blueprint "chap8__lemma_8_2_1"]
def isPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => Formula.isPrenex A
  | .ex _ A => Formula.isPrenex A
  | A => ¬ (∃ i B, A = FormulaN.all i B ∨ A = FormulaN.ex i B) ∧
         formulaQuantifierFree A
where
  /-- A formula is quantifier-free if it contains no quantifiers. -/
  formulaQuantifierFree {L : Language} : FormulaN L → Prop
    | .predN _ _ => True
    | .eq_ _ _ _ => True
    | .neg A => formulaQuantifierFree A
    | .conj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .disj A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .impl A B => formulaQuantifierFree A ∧ formulaQuantifierFree B
    | .all _ _ => False
    | .ex _ _ => False

/-- Lemma 8.2.1 (companion): Predicate that the matrix (innermost
    quantifier-free part) of a prenex formula is in conjunctive normal
    form (i.e. a conjunction of clauses where each clause is a
    disjunction of literals). -/
@[blueprint "chap8__lemma_8_2_1"]
def matrixIsCNF {L : Language} : FormulaN L → Prop
  | .all _ A => Formula.matrixIsCNF A
  | .ex _ A => Formula.matrixIsCNF A
  | A => Formula.isCNFMatrix A

/-- Lemma 8.2.1 (companion): A formula has a purely universal prenex
    prefix: every leading quantifier is a universal. Used to restrict
    Lemma 8.2.1 to the Skolem-free case (no existentials in the prefix),
    which is provable without invoking Ch7 Skolemization. -/
@[blueprint "chap8__lemma_8_2_1"]
def isUniversalPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => Formula.isUniversalPrenex A
  | .ex _ _ => False
  | _ => True

end Formula

-- ===================================================================
-- Lemma 8.2.1 (companion def): concrete clause-form conversion
-- ===================================================================

namespace Formula

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Reassemble a non-empty list of formulae as
    a right-associated conjunction. The empty-list case uses
    `FormulaN.falsum fallback`. In `preparedClauseDistribution`, the list
    comes from `splitConj` and is nonempty. This is general syntax machinery
    for prepared prefix distribution. -/
def conjunctAll {L : Language}
    (fallback : FormulaN L) : List (FormulaN L) → FormulaN L
  | [] => FormulaN.falsum fallback
  | [C] => C
  | C :: rest => FormulaN.conj C (conjunctAll fallback rest)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 8.2.1 (companion): Prepend a list of universal quantifiers to
    a formula: `prependAlls [i_1, ..., i_n] A = ∀ i_1 ... ∀ i_n . A`. -/
def prependAlls {L : Language} :
    List Nat → FormulaN L → FormulaN L
  | [], A => A
  | i :: rest, A => FormulaN.all i (Formula.prependAlls rest A)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 8.2.1 (companion): Strip a leading universal prefix from a
    (universal-prenex) formula, returning the list of bound variables
    (outer-to-inner) and the matrix. On non-universal-prenex input the
    function stops at the first non-`∀` node. -/
def stripAllPrenex {L : Language} :
    FormulaN L → List Nat × FormulaN L
  | .all i A => let (vs, M) := Formula.stripAllPrenex A; (i :: vs, M)
  | A => ([], A)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Distribute an existing universal prefix
    over the conjuncts of a CNF matrix. This prepared syntactic operation
    preserves universal validity; repeated copies of the prefix still
    require renaming apart to satisfy the clause-form sentence contract. -/
def ofFormulaN {L : Language} (A : FormulaN L) : FormulaN L :=
  let (vs, M) := Formula.stripAllPrenex A
  let conjuncts := Formula.splitConj M
  Formula.conjunctAll A (conjuncts.map (Formula.prependAlls vs))

end Formula

-- ===================================================================
-- Semantics of prepared prefix distribution
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): Iterated universal over a list `vs` of
    variables — for every assignment update sequence applied in order.
    Defined as a separate predicate so its recursion does not rely on
    `vs` being duplicate-free. -/
def formulaEvalN_prependAllsAux {L : Language} (M : Structure L) :
    List Nat → FormulaN L → Assignment M → Prop
  | [], A, s => formulaEvalN M A s
  | w :: rest, A, s =>
      ∀ a : M.carrier,
        formulaEvalN_prependAllsAux M rest A (assignUpdate s w a)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): Recursive semantic characterisation of
    `prependAlls`. Each outer `∀ w` corresponds to a universal
    quantification over `M.carrier`. -/
theorem formulaEvalN_prependAlls_forall {L : Language}
    (M : Structure L) :
    ∀ (vs : List Nat) (A : FormulaN L) (s : Assignment M),
      formulaEvalN M (Formula.prependAlls vs A) s ↔
      formulaEvalN_prependAllsAux M vs A s := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil =>
    intro A s
    simp only [Formula.prependAlls, formulaEvalN_prependAllsAux]
  | cons w rest ih =>
    intro A s
    simp only [Formula.prependAlls, formulaEvalN,
               formulaEvalN_prependAllsAux]
    constructor
    · intro hAll a
      exact (ih A (assignUpdate s w a)).mp (hAll a)
    · intro hAll a
      exact (ih A (assignUpdate s w a)).mpr (hAll a)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): `splitConj` preserves semantics — a formula is
    true under `s` iff every conjunct in its top-level conjunction split
    is true under `s`. -/
theorem formulaEvalN_splitConj {L : Language}
    (M : Structure L) :
    ∀ (A : FormulaN L) (s : Assignment M),
      formulaEvalN M A s ↔
      (∀ C ∈ Formula.splitConj A, formulaEvalN M C s) := by
-- BEGIN PROOF
  intro A
  induction A with
  | conj A B ihA ihB =>
    intro s
    simp only [Formula.splitConj, formulaEvalN, List.mem_append]
    constructor
    · rintro ⟨hA, hB⟩ C hC
      cases hC with
      | inl hCA => exact (ihA s).mp hA C hCA
      | inr hCB => exact (ihB s).mp hB C hCB
    · intro hAll
      refine ⟨?_, ?_⟩
      · apply (ihA s).mpr; intro C hC; exact hAll C (Or.inl hC)
      · apply (ihB s).mpr; intro C hC; exact hAll C (Or.inr hC)
  | predN P ts =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | eq_ hL t1 t2 =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | neg A _ =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | disj A B _ _ =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | impl A B _ _ =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | all i A _ =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl
  | ex i A _ =>
    intro s; simp only [Formula.splitConj, List.mem_singleton]
    constructor
    · intro h C hC; subst hC; exact h
    · intro hAll; exact hAll _ rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper, nonempty case): `conjunctAll` is true under `s`
    iff every formula in the (non-empty) list is true under `s`. The
    non-empty restriction is captured by providing a head `C` and a
    tail `rest` explicitly. -/
theorem formulaEvalN_conjunctAll_cons {L : Language}
    (M : Structure L) (fallback : FormulaN L) :
    ∀ (C : FormulaN L) (rest : List (FormulaN L)) (s : Assignment M),
      formulaEvalN M (Formula.conjunctAll fallback (C :: rest)) s ↔
      (formulaEvalN M C s ∧
        ∀ D ∈ rest, formulaEvalN M D s) := by
-- BEGIN PROOF
  intro C rest
  induction rest generalizing C with
  | nil =>
    intro s
    simp only [Formula.conjunctAll, List.not_mem_nil, false_implies,
               implies_true, and_true]
  | cons D rest' ih =>
    intro s
    simp only [Formula.conjunctAll, formulaEvalN]
    constructor
    · rintro ⟨hC, hDrest⟩
      have hih := (ih D s).mp hDrest
      refine ⟨hC, ?_⟩
      intro E hE
      simp only [List.mem_cons] at hE
      cases hE with
      | inl hED => subst hED; exact hih.1
      | inr hE' => exact hih.2 E hE'
    · rintro ⟨hC, hAll⟩
      refine ⟨hC, ?_⟩
      apply (ih D s).mpr
      refine ⟨hAll D (by simp), ?_⟩
      intro E hE; exact hAll E (List.mem_cons_of_mem _ hE)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Stripping and restoring the leading universal prefix reconstructs
    every formula exactly. No prenex or clause-form premise is required. -/
theorem stripAllPrenex_prependAlls {L : Language} :
    ∀ (A : FormulaN L),
      A = Formula.prependAlls (Formula.stripAllPrenex A).1
              (Formula.stripAllPrenex A).2 := by
-- BEGIN PROOF
  intro A
  induction A with
  | all i A ihA =>
    simp only [Formula.stripAllPrenex, Formula.prependAlls]
    exact congrArg (FormulaN.all i) ihA
  | _ => simp [Formula.stripAllPrenex, Formula.prependAlls]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Splitting a faithful CNF matrix at top-level conjunctions yields only
    disjunctions of literals. -/
theorem splitConj_isDisjunctionOfLiterals {L : Language} :
    ∀ (A : FormulaN L), Formula.isCNFMatrix A →
      ∀ C ∈ Formula.splitConj A, Formula.isDisjunctionOfLiterals C := by
  intro A
  induction A with
  | conj A B ihA ihB =>
      intro hCNF C hC
      obtain ⟨hA, hB⟩ := hCNF
      simp only [Formula.splitConj, List.mem_append] at hC
      exact hC.elim (ihA hA C) (ihB hB C)
  | predN _ _ | eq_ _ _ _ | neg _ _ | disj _ _ _ _
  | impl _ _ _ _ | all _ _ _ | ex _ _ _ =>
      intro hCNF C hC
      simp only [Formula.splitConj, List.mem_singleton] at hC
      subst C
      exact hCNF

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): Every conjunct of the matrix of a
    universal-prenex CNF formula is a disjunction of literals. -/
theorem matrixIsCNF_of_univPrenex {L : Language} :
    ∀ (A : FormulaN L), Formula.isUniversalPrenex A →
      Formula.matrixIsCNF A →
      ∀ C ∈ Formula.splitConj (Formula.stripAllPrenex A).2,
        Formula.isDisjunctionOfLiterals C := by
-- BEGIN PROOF
  intro A
  induction A with
  | all i A ihA =>
    intro hPre hCNF C hC
    simp only [Formula.stripAllPrenex] at hC
    exact ihA hPre hCNF C hC
  | predN _ _ | eq_ _ _ _ | neg _ _ | conj _ _ _ _
  | disj _ _ _ _ | impl _ _ _ _ =>
    intro _hPre hCNF C hC
    exact splitConj_isDisjunctionOfLiterals _ hCNF C hC
  | ex _i _A _ih =>
    intro hPre _hCNF C _hC
    exact absurd hPre (by
      simp only [Formula.isUniversalPrenex]; intro h; exact h)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A disjunction of literals has universal-clause shape with an empty
    quantifier prefix. -/
theorem isUniversalClauseShape_of_isDisjunctionOfLiterals {L : Language}
    (C : FormulaN L) (hC : Formula.isDisjunctionOfLiterals C) :
    Formula.isUniversalClauseShape C := by
  cases C <;>
    simp_all [Formula.isUniversalClauseShape,
      Formula.isDisjunctionOfLiterals, Formula.isClauseLiteral]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): Prepending universal quantifiers to a
    disjunction of literals produces universal-clause shape. -/
theorem prependAlls_isUniversalClauseShape {L : Language} (C : FormulaN L)
    (hC : Formula.isDisjunctionOfLiterals C) :
    ∀ (vs : List Nat),
      Formula.isUniversalClauseShape (Formula.prependAlls vs C) := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil =>
      simp only [Formula.prependAlls]
      exact isUniversalClauseShape_of_isDisjunctionOfLiterals C hC
  | cons v rest ih =>
    simp only [Formula.prependAlls, Formula.isUniversalClauseShape]
    exact ih

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every universal-clause shape is a one-clause clause-form shape. -/
theorem isClauseFormShape_of_isUniversalClauseShape {L : Language}
    (C : FormulaN L) (hC : Formula.isUniversalClauseShape C) :
    Formula.isClauseFormShape C := by
  cases C <;>
    simp_all [Formula.isClauseFormShape, Formula.isUniversalClauseShape,
      Formula.isDisjunctionOfLiterals, Formula.isClauseLiteral]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- `conjunctAll` preserves clause-form shape for a nonempty list of
    universal-clause shapes. The empty-list fallback is outside this
    theorem's domain; closure and binder separation are separate conditions. -/
theorem conjunctAll_isClauseFormShape {L : Language}
    (fallback : FormulaN L) :
    ∀ (L' : List (FormulaN L)), L' ≠ [] →
      (∀ C ∈ L', Formula.isUniversalClauseShape C) →
      Formula.isClauseFormShape (Formula.conjunctAll fallback L') := by
-- BEGIN PROOF
  intro L' hne hAll
  induction L' with
  | nil => exact absurd rfl hne
  | cons C rest ih =>
    cases rest with
    | nil =>
      simp only [Formula.conjunctAll]
      exact isClauseFormShape_of_isUniversalClauseShape C
        (hAll C List.mem_cons_self)
    | cons D rest' =>
      simp only [Formula.conjunctAll, Formula.isClauseFormShape]
      refine ⟨isClauseFormShape_of_isUniversalClauseShape C
        (hAll C List.mem_cons_self), ?_⟩
      apply ih (List.cons_ne_nil _ _)
      intro E hE; exact hAll E (List.mem_cons_of_mem _ hE)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): `splitConj A` is always non-empty. -/
theorem splitConj_nonempty {L : Language} (A : FormulaN L) :
    Formula.splitConj A ≠ [] := by
-- BEGIN PROOF
  induction A with
  | conj A B ihA _ =>
    simp only [Formula.splitConj]
    intro h
    exact ihA (List.append_eq_nil_iff.mp h).1
  | _ => simp [Formula.splitConj]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 8.2.1 (helper): `splitConj A` as a cons. Since `splitConj` is
    non-empty, there is a head and a tail. -/
theorem splitConj_cons {L : Language} (A : FormulaN L) :
    ∃ (C : FormulaN L) (rest : List (FormulaN L)),
      Formula.splitConj A = C :: rest := by
-- BEGIN PROOF
  have hne := splitConj_nonempty A
  cases h : Formula.splitConj A with
  | nil => exact absurd h hne
  | cons C rest => exact ⟨C, rest, rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Distributing the same universal prefix over a matrix's top-level
    conjuncts preserves evaluation under the given assignment. The prefix
    need not bind every free variable of the matrix, and its names may
    repeat; the recursive assignment updates retain their order. -/
theorem formulaEvalN_ofFormulaN_core {L : Language}
    (M : Structure L) (vs : List Nat) (matrix : FormulaN L)
    (s : Assignment M) :
    formulaEvalN_prependAllsAux M vs matrix s ↔
    ∀ C ∈ Formula.splitConj matrix,
      formulaEvalN_prependAllsAux M vs C s := by
-- BEGIN PROOF
  induction vs generalizing s with
  | nil =>
    simp only [formulaEvalN_prependAllsAux]
    exact formulaEvalN_splitConj M matrix s
  | cons w rest ih =>
    simp only [formulaEvalN_prependAllsAux]
    constructor
    · intro hAll C hC a
      exact (ih (assignUpdate s w a)).mp (hAll a) C hC
    · intro hAll a
      apply (ih (assignUpdate s w a)).mpr
      intro C hC
      exact hAll C hC a

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Semantic characterization of prepared prefix distribution:
    `ofFormulaN A` is true under `s` iff each top-level matrix conjunct,
    preceded by the original universal prefix, is true under `s`.
    This holds for every formula A, with no CNF precondition. -/
theorem formulaEvalN_ofFormulaN_distribute {L : Language}
    (M : Structure L) (A : FormulaN L) (s : Assignment M) :
    formulaEvalN M (Formula.ofFormulaN A) s ↔
    ∀ C ∈ Formula.splitConj (Formula.stripAllPrenex A).2,
      formulaEvalN M
        (Formula.prependAlls (Formula.stripAllPrenex A).1 C) s := by
-- BEGIN PROOF
  simp only [Formula.ofFormulaN]
  -- Split the conjunction list (non-empty) as C :: rest.
  obtain ⟨C0, rest0, hsplit⟩ := splitConj_cons (Formula.stripAllPrenex A).2
  rw [hsplit]
  simp only [List.map_cons]
  rw [formulaEvalN_conjunctAll_cons]
  constructor
  · rintro ⟨hC0, hAll⟩ C hC
    simp only [List.mem_cons] at hC
    cases hC with
    | inl h => subst h; exact hC0
    | inr h =>
      have hmem : Formula.prependAlls (Formula.stripAllPrenex A).1 C
          ∈ List.map (Formula.prependAlls (Formula.stripAllPrenex A).1)
                     rest0 := List.mem_map.mpr ⟨C, h, rfl⟩
      exact hAll _ hmem
  · intro hAll
    refine ⟨hAll C0 (by simp), ?_⟩
    intro D hD
    obtain ⟨C, hC, hCeq⟩ := List.mem_map.mp hD
    subst hCeq
    exact hAll C (by simp [hC])

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Prepared universal-prefix distribution for a CNF matrix preserves
    universal validity and the conjunction-of-universal-clause-shapes
    grammar. The operation copies prefixes; it does not rename binders
    apart or close free variables. The full sentence clause-form contract
    is expressed by `Formula.isClauseForm`. -/
theorem preparedClauseDistribution {L : Language} (A : FormulaN L)
    (hPrenex : Formula.isUniversalPrenex A)
    (hCNF : Formula.matrixIsCNF A) :
    Formula.isClauseFormShape (Formula.ofFormulaN A) ∧
      (universallyValidN A ↔ universallyValidN (Formula.ofFormulaN A)) :=
-- BEGIN PROOF
by
  refine ⟨?_, ?_⟩
  · -- Prefix distribution preserves the grammar of universal-clause shapes.
    unfold Formula.ofFormulaN
    apply conjunctAll_isClauseFormShape
    · -- List is non-empty because splitConj is non-empty
      intro h
      have hne := splitConj_nonempty (L := L) (Formula.stripAllPrenex A).2
      exact hne (List.map_eq_nil_iff.mp h)
    · -- Every matrix conjunct has disjunction-of-literals shape.
      intro C hC
      obtain ⟨D, hD, hDeq⟩ := List.mem_map.mp hC
      subst hDeq
      apply prependAlls_isUniversalClauseShape
      exact matrixIsCNF_of_univPrenex A hPrenex hCNF D hD
  · -- universallyValidN A ↔ universallyValidN (ofFormulaN A)
    constructor
    · -- A valid ⇒ ofFormulaN A valid
      intro hA M s
      rw [formulaEvalN_ofFormulaN_distribute]
      intro C hC
      rw [formulaEvalN_prependAlls_forall]
      have := hA M s
      -- Rewrite A as prependAlls of its matrix
      rw [stripAllPrenex_prependAlls A] at this
      rw [formulaEvalN_prependAlls_forall] at this
      exact (formulaEvalN_ofFormulaN_core M (Formula.stripAllPrenex A).1
        (Formula.stripAllPrenex A).2 s).mp this C hC
    · -- ofFormulaN A valid ⇒ A valid
      intro hB' M s
      rw [stripAllPrenex_prependAlls A]
      rw [formulaEvalN_prependAlls_forall]
      apply (formulaEvalN_ofFormulaN_core M (Formula.stripAllPrenex A).1
        (Formula.stripAllPrenex A).2 s).mpr
      intro C hC
      have := hB' M s
      rw [formulaEvalN_ofFormulaN_distribute] at this
      have hCeval := this C hC
      rw [formulaEvalN_prependAlls_forall] at hCeval
      exact hCeval

/-- Lemma 8.2.1 (companion): A clause conversion starts from the rectified
    NNF of the negation of A. `S` supplies the canonical fresh Skolem signature
    and actual Skolem form of that sentence. The output is a closed clause
    form with distinct, pairwise disjoint prefix names, equivalent in every
    structure of the extended language to that Skolem form. Rectification
    is internal to this relation; it is not a precondition on A. -/
@[blueprint "chap8__lemma_8_2_1"]
def Formula.isClauseFormOf {L : Language} (hL : L.withoutEquality)
    (A : FormulaN L) (S : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (B' : FormulaN S.language) : Prop :=
  S.source = LCS.FirstOrder.Semantics.Subformulae.rectify (FormulaN.neg A).toNNF ∧
    Formula.isClauseForm (L := S.language) hL B' ∧
    ∀ (M : Structure S.language) (s : Assignment M),
      formulaEvalN M B' s ↔ formulaEvalN M (LCS.Herbrand.SHGTheorem.skolemForm S) s

/-- Lemma 8.2.1: Every sentence of an equality-free language has a
    clause-form sentence for its negation in the corresponding fresh Skolem
    extension. The original sentence is valid exactly when that output is
    unsatisfiable. No prenex, CNF or rectification premise is imposed on A.
    This is the existence and semantic boundary; the general effective
    conversion is deferred under OD-A17. -/
@[attach_debt, blueprint "chap8__lemma_8_2_1" (main := true)]
theorem clauseFormConstruction {L : Language} (hL : L.withoutEquality)
    (A : FormulaN L) (hSentence : FormulaN.isClosed A) :
    ∃ (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) (B' : FormulaN S.language),
      Formula.isClauseFormOf hL A S B' ∧
        (Formula.isValid A ↔ Formula.isUnsatisfiable B') 

-- ===================================================================
-- Example 8.2.1: the six displayed conversion relationships
-- ===================================================================

/-- Example 8.2.1: A model of the actual final clause list satisfies every
    clause under every assignment. Positive atoms are evaluated directly;
    negative literals negate their atom's evaluation. This universally
    closes the matrix representation, including its clause-local names. -/
@[blueprint "chap8__example_8_2_1"]
def exClauseFormSatisfied (M : Structure exClauseFormLang) : Prop :=
  ∀ c ∈ exClauseFormConversion, ∀ s : Assignment M,
    ∃ lit ∈ c, match lit with
      | .pos atom => formulaEvalN M atom.toFormula s
      | .neg atom => ¬ formulaEvalN M atom.toFormula s

/-- Example 8.2.1, step 1: Negation of the same original A is equivalent
    to the displayed biconditional/implication-elimination stage. -/
@[blueprint "chap8__example_8_2_1"]
theorem exClauseOriginal_toEliminated (M : Structure exClauseInputLang)
    (s : Assignment M) :
    formulaEvalN M (.neg exClauseOriginal) s ↔ formulaEvalN M exClauseEliminated s 

/-- Example 8.2.1, step 2: The eliminated formula and its displayed NNF
    are equivalent in every input-language structure and assignment. -/
@[blueprint "chap8__example_8_2_1"]
theorem exClauseEliminated_toNNF (M : Structure exClauseInputLang)
    (s : Assignment M) :
    formulaEvalN M exClauseEliminated s ↔ formulaEvalN M exClauseNNF s 

/-- Example 8.2.1, step 3: Skolemization preserves satisfiability across
    the predicate-only input signature and its extension by fresh a and
    unary f. This is equisatisfiability, not equivalence under an arbitrary
    interpretation of the new symbols. The right witness depends only on z. -/
@[attach_debt, blueprint "chap8__example_8_2_1"]
theorem exClauseNNF_toSkolem :
    satisfiableN exClauseNNF ↔ satisfiableN exClauseSkolem 

/-- Example 8.2.1, step 4: Moving the left universal x outwards yields
    the displayed prenex formula; x does not occur in the right conjunct. -/
@[attach_debt, blueprint "chap8__example_8_2_1"]
theorem exClauseSkolem_toPrenex (M : Structure exClauseFormLang)
    (s : Assignment M) :
    formulaEvalN M exClauseSkolem s ↔ formulaEvalN M exClausePrenex s 

/-- Example 8.2.1, step 5: Distributing ∨ over ∧ gives the adopted SQ06
    CNF, including the complete third disjunction P(f(z),z) ∨ P(z,a). -/
@[blueprint "chap8__example_8_2_1"]
theorem exClausePrenex_toCNF (M : Structure exClauseFormLang)
    (s : Assignment M) :
    formulaEvalN M exClausePrenex s ↔ formulaEvalN M exClauseCNF s 

/-- Example 8.2.1, step 6: Distribute the universal prefix, discard
    vacuous x binders in C2/C3, and rename z to the clause-local names
    1, 2, 3. The resulting matrices are the actual stored C1–C3 list. -/
@[attach_debt, blueprint "chap8__example_8_2_1"]
theorem exClauseCNF_toClauses (M : Structure exClauseFormLang)
    (s : Assignment M) :
    formulaEvalN M exClauseCNF s ↔ exClauseFormSatisfied M 

/-- Example 8.2.1: Composing all six transitions connects the actual
    final clauses to the negation of the same original A. -/
@[blueprint "chap8__example_8_2_1"]
theorem exClauseFormConversion_negOriginal :
    satisfiableN (.neg exClauseOriginal) ↔
      ∃ M : Structure exClauseFormLang, exClauseFormSatisfied M 

/-- Example 8.2.1: The original A is valid exactly when the actual
    final clauses have no model, by the conversion through ¬A. -/
@[blueprint "chap8__example_8_2_1"]
theorem exClauseFormConversion_valid_iff_unsatisfiable :
    Formula.isValid exClauseOriginal ↔
      ¬ ∃ M : Structure exClauseFormLang, exClauseFormSatisfied M 

end LCS.FOResolution.ClauseForm
