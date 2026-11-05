import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Herbrand.HerbrandTheorem.Main.Part1
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import Attach
import LCS.FOResolution.GroundResolution.GroundClauses.ProofsStamp

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm

/-- Example 8.3.1 (companion): Finite binary resolution-tree syntax over
    a first-order language without equality. Leaves store clauses and
    internal nodes store two premise trees and a pivot literal.
    `labelSpec` certifies groundness and the resolution inferences;
    `isRefutation` additionally requires input-clause leaves and an empty
    root label. Internal clause labels are specified by `labelSpec`. -/
@[blueprint "chap8__example_8_3_1"]
inductive FOResolutionTree (L : Language) (hNoEq : L.withoutEquality) : Type where
  /-- A leaf node labeled with a ground clause from the input set -/
  | axiom_ : FOClause L hNoEq → FOResolutionTree L hNoEq
  /-- A resolution step combining two subtrees via pivot literal L -/
  | resolve : FOResolutionTree L hNoEq → FOResolutionTree L hNoEq →
      (pivot : FOLiteral L hNoEq) → FOResolutionTree L hNoEq

end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
namespace FOResolutionTree

/-- Example 8.3.1 (companion): Certified ground-resolution labeling in
    a language without equality. A leaf has its stored ground clause.
    A resolution step has certified premise labels containing the pivot
    and its conjugate, respectively. Its ground conclusion is extensionally
    the union of those labels with the pivot and its conjugate removed.
    The specification uses literal membership, so list ordering and
    repetitions do not change the represented resolvent. -/
@[blueprint "chap8__example_8_3_1"]
def labelSpec {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → FOClause L hNoEq → Prop
  | .axiom_ C, C' =>
    C' = C ∧ FOClause.isGround hNoEq C
  | .resolve T1 T2 pivot, C' =>
    ∃ C1 C2 : FOClause L hNoEq,
      labelSpec (hNoEq := hNoEq) T1 C1 ∧ labelSpec (hNoEq := hNoEq) T2 C2 ∧
      pivot ∈ C1 ∧
      FOLiteral.conjugate hNoEq pivot ∈ C2 ∧
      FOClause.isGround hNoEq C' ∧
      (∀ lit, lit ∈ C' ↔
        (lit ∈ C1 ∧ lit ≠ pivot) ∨
        (lit ∈ C2 ∧ lit ≠ FOLiteral.conjugate hNoEq pivot))

/-- Lemma 8.3.1 (companion): All leaf clauses in a first-order
    resolution tree are members of the clause set S. -/
@[blueprint "chap8__lemma_8_3_1"]
def leavesFrom {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → (FOClause L hNoEq → Prop) → Prop
  | .axiom_ C, S => S C
  | .resolve T1 T2 _, S => T1.leavesFrom (hNoEq := hNoEq) S ∧ T2.leavesFrom (hNoEq := hNoEq) S

/-- Lemma 8.3.1 (companion): A ground-resolution refutation over a
    language without equality certifies that every clause in S is ground,
    every leaf belongs to S, and the root has the certified empty label.
    The input predicate S need not be finite here; the completeness theorem
    uses a finite list of ground clauses. -/
@[blueprint "chap8__lemma_8_3_1"]
def isRefutation {L : Language} (hNoEq : L.withoutEquality)
    (T : FOResolutionTree L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  (∀ C, S C → FOClause.isGround hNoEq C) ∧
  T.leavesFrom hNoEq S ∧
  labelSpec (hNoEq := hNoEq) T []

end FOResolutionTree
end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
namespace FOLiteral

/-- Lemma 8.3.1 (companion): A first-order literal is satisfied in a
    structure M under assignment s. A positive literal pos B is true
    when B holds; a negative literal neg B is true when B does not
    hold. -/
@[blueprint "chap8__lemma_8_3_1"]
def isSatisfied {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) :
    FOLiteral L hNoEq → Prop
  | .pos B => formulaEvalN M B.toFormula s
  | .neg B => ¬ formulaEvalN M B.toFormula s

end FOLiteral
end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
namespace FOClause

/-- Lemma 8.3.1 (companion): A ground clause (disjunction of literals)
    is satisfied in a structure M under assignment s iff at least one
    of its literals is true. -/
@[blueprint "chap8__lemma_8_3_1"]
def isSatisfied {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (c : FOClause L hNoEq) : Prop :=
  ∃ lit ∈ c, FOLiteral.isSatisfied (hNoEq := hNoEq) M s lit

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Groundness is preserved when every literal of one clause occurs in a
    ground clause. -/
theorem isGround_of_subset {L : Language} (hNoEq : L.withoutEquality)
    {source target : FOClause L hNoEq}
    (hGround : source.isGround hNoEq)
    (hSubset : ∀ lit, lit ∈ target → lit ∈ source) :
    target.isGround hNoEq := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    have : source.vars hNoEq x := ⟨lit, hSubset lit hLit, hVar⟩
    dsimp only [FOClause.vars] at this
    rw [hGround] at this
    exact this
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Appending ground clauses preserves groundness. -/
theorem isGround_append {L : Language} (hNoEq : L.withoutEquality)
    {left right : FOClause L hNoEq}
    (hLeft : left.isGround hNoEq)
    (hRight : right.isGround hNoEq) :
    (left ++ right).isGround hNoEq := by
  apply isGround_of_subset (hNoEq := hNoEq) (source := left ++ right)
      (target := left ++ right)
  · ext x
    constructor
    · intro ⟨lit, hLit, hVar⟩
      rw [List.mem_append] at hLit
      rcases hLit with hLit | hLit
      · have : left.vars hNoEq x := ⟨lit, hLit, hVar⟩
        dsimp only [FOClause.vars] at this
        rw [hLeft] at this
        exact this
      · have : right.vars hNoEq x := ⟨lit, hLit, hVar⟩
        dsimp only [FOClause.vars] at this
        rw [hRight] at this
        exact this
    · intro h
      exact h.elim
  · exact fun _ h => h

end FOClause
end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
namespace FOResolutionTree

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- A certified ground-resolution label is ground at every node. -/
theorem labelSpec_isGround {L : Language} (hNoEq : L.withoutEquality)
    {T : FOResolutionTree L hNoEq} {C : FOClause L hNoEq}
    (hSpec : T.labelSpec (hNoEq := hNoEq) C) :
    C.isGround hNoEq := by
  cases T with
  | axiom_ source =>
    exact hSpec.1 ▸ hSpec.2
  | resolve _ _ _ =>
    exact hSpec.choose_spec.choose_spec.2.2.2.2.1

end FOResolutionTree
end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
namespace GroundClauseSet

/-- Lemma 8.3.1 (companion): A set of ground clauses is unsatisfiable
    iff no interpretation satisfies all clauses simultaneously. Adapts
    the unsatisfiability concept from propositional resolution to the
    first-order ground setting. A ground clause (a disjunction of
    ground literals) is viewed as a formula; the set is unsatisfiable
    when the conjunction of all clause-formulae is unsatisfiable. -/
@[blueprint "chap8__lemma_8_3_1"]
def isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOClause L hNoEq)) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    ∃ c ∈ S, ¬ FOClause.isSatisfied (hNoEq := hNoEq) M s c

end GroundClauseSet
end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN

/-- Lemma 8.3.1 (companion): A ground substitution maps variable
    indices to ground terms (terms with no variables). -/
@[blueprint "chap8__lemma_8_3_1"]
structure GroundSubstitution (L : Language) where
  /-- The term substituted for each variable. -/
  toSubst : Nat → Term L
  /-- Every substituted term is closed. -/
  termsGround : ∀ n, termVars (toSubst n) = Set.empty

-- ATTACH-BLOCKER: unsupported untagged instance
instance {L : Language} :
    CoeFun (GroundSubstitution L) (fun _ => Nat → Term L) where
  coe sigma := sigma.toSubst

/-- Lemma 8.3.1 (companion): Apply a ground substitution to a term,
    replacing every variable with its image under the substitution. -/
@[blueprint "chap8__lemma_8_3_1"]
def applySubstTerm {L : Language}
    (sigma : GroundSubstitution L) : Term L → Term L
  | .var n => sigma n
  | .const c => .const c
  | .func f args => .func f (fun i => applySubstTerm sigma (args i))

/-- Lemma 8.3.1 (companion): Apply a ground substitution throughout a
    quantifier-free formula.  The recursive quantifier cases make this a
    total raw-syntax operation, but are not a capture-avoiding substitution;
    ground instantiation below operates on atomic literals instead. -/
@[blueprint "chap8__lemma_8_3_1"]
def applySubstFormula {L : Language}
    (sigma : GroundSubstitution L) : FormulaN L → FormulaN L
  | .predN P args => .predN P (fun i => applySubstTerm sigma (args i))
  | .eq_ hL t1 t2 => .eq_ hL (applySubstTerm sigma t1)
      (applySubstTerm sigma t2)
  | .conj A B => .conj (applySubstFormula sigma A)
      (applySubstFormula sigma B)
  | .disj A B => .disj (applySubstFormula sigma A)
      (applySubstFormula sigma B)
  | .impl A B => .impl (applySubstFormula sigma A)
      (applySubstFormula sigma B)
  | .neg A => .neg (applySubstFormula sigma A)
  | .all x A => .all x (applySubstFormula sigma A)
  | .ex x A => .ex x (applySubstFormula sigma A)

/-- Lemma 8.3.1 (companion): Apply a ground substitution to a
    first-order literal, substituting in the underlying formula. -/
@[blueprint "chap8__lemma_8_3_1"]
def applySubstLiteral {L : Language} (hNoEq : L.withoutEquality)
    (sigma : GroundSubstitution L) : FOLiteral L hNoEq → FOLiteral L hNoEq
  | .pos B => .pos (B.mapTerms (applySubstTerm sigma))
  | .neg B => .neg (B.mapTerms (applySubstTerm sigma))

/-- Lemma 8.3.1 (companion): Instantiate a first-order clause to a
    ground clause by applying a ground substitution to each literal.
    This is the clause-to-ground-clause step of the three-step ground
    resolution procedure. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundInstantiate {L : Language} (hNoEq : L.withoutEquality)
    (sigma : GroundSubstitution L)
    (c : FOClause L hNoEq) : FOClause L hNoEq :=
  c.map (applySubstLiteral (hNoEq := hNoEq) sigma)

-- ===================================================================
-- Lemma 8.3.1 (companion): ThreeStepProcedure
-- ===================================================================
/-- The fresh Skolem signature for this input, completed by one distinguished
    constant. The ground-universe predicate admits that constant only when
    the occurring input-plus-Skolem signature has no ground term. -/
@[blueprint "chap8__lemma_8_3_1"]
def GroundRunLanguage {L : Language} (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    Language := extendedLanguage S.language Unit

/-- Embed normalized formula syntax into the constant-completed signature. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundRunLiftFormula {L : Language} : FormulaN L → FormulaN (extendedLanguage L Unit)
  | .predN P ts => .predN P (fun i => LCS.FirstOrder.Semantics.Substitution.liftTerm (ts i))
  | .eq_ h t u => .eq_ h (LCS.FirstOrder.Semantics.Substitution.liftTerm t)
      (LCS.FirstOrder.Semantics.Substitution.liftTerm u)
  | .conj A B => .conj (groundRunLiftFormula A) (groundRunLiftFormula B)
  | .disj A B => .disj (groundRunLiftFormula A) (groundRunLiftFormula B)
  | .impl A B => .impl (groundRunLiftFormula A) (groundRunLiftFormula B)
  | .neg A => .neg (groundRunLiftFormula A)
  | .all x A => .all x (groundRunLiftFormula A)
  | .ex x A => .ex x (groundRunLiftFormula A)

/-- Ground terms using only symbols of the original input and its fresh
    occurrence-indexed Skolem symbols, before constant completion. -/
@[blueprint "chap8__lemma_8_3_1"]
def GroundRunBaseTerm {L : Language} (B : FormulaN L)
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) (t : Term S.language) : Prop :=
  termVars t = Set.empty ∧
    (∀ c, LCS.Herbrand.HerbrandTheorem.Main.termConstSymbols t c →
      match c with
      | .inl c => LCS.Herbrand.HerbrandTheorem.Main.fmlaConstSymbols B c
      | .inr _ => True) ∧
    (∀ f, LCS.Herbrand.HerbrandTheorem.Main.termFuncSymbols t f →
      match f with
      | .inl f => LCS.Herbrand.HerbrandTheorem.Main.fmlaFuncSymbols B f
      | .inr _ => True)

/-- The enumeration universe excludes unused ambient symbols. The fresh
    grounding constant is available exactly when the base universe is empty,
    including the case of no constants but an occurring nullary function. -/
@[blueprint "chap8__lemma_8_3_1"]
def GroundRunTerm {L : Language} (B : FormulaN L)
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) (t : Term (GroundRunLanguage S)) : Prop :=
  termVars t = Set.empty ∧
    (∀ c, LCS.Herbrand.HerbrandTheorem.Main.termConstSymbols t c →
      match c with
      | .inl (.inl c) => LCS.Herbrand.HerbrandTheorem.Main.fmlaConstSymbols B c
      | .inl (.inr _) => True
      | .inr _ => ¬ ∃ u, GroundRunBaseTerm B S u) ∧
    (∀ f, LCS.Herbrand.HerbrandTheorem.Main.termFuncSymbols t f →
      match f with
      | .inl f => LCS.Herbrand.HerbrandTheorem.Main.fmlaFuncSymbols B f
      | .inr _ => True)

/-- The rectified NNF of the same input sentence supplied to Skolemization. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundRunNormalizedInput {L : Language} (B : FormulaN L) : FormulaN L :=
  LCS.FirstOrder.Semantics.Subformulae.rectify B.toNNF

/-- Normalization of the same input B, not its negation, in its canonical
    fresh Skolem signature. The clause sentence has the full closed/disjoint
    prefix contract; its matrices have the same universally closed semantics.
    This specifies supplied conversion data, not an effective converter. -/
@[blueprint "chap8__lemma_8_3_1"]
structure GroundRunNormalization (L : Language) (hNoEq : L.withoutEquality)
    (B : FormulaN L) where
  inputIsSentence : FormulaN.isClosed B
  skolem : LCS.Herbrand.SHGTheorem.SkolemSpec L
  sameInput : skolem.source = groundRunNormalizedInput B
  clauseSentence : FormulaN (GroundRunLanguage skolem)
  clauseSentenceValid : Formula.isClauseForm (L := GroundRunLanguage skolem) hNoEq clauseSentence
  clauseForm : FOClauseForm (GroundRunLanguage skolem) hNoEq
  clauseConstants : ∀ c ∈ clauseForm, ∀ lit ∈ c, ∀ d,
    LCS.Herbrand.HerbrandTheorem.Main.fmlaConstSymbols (FOLiteral.formula (L := GroundRunLanguage skolem) hNoEq lit) d →
      match d with
      | .inl (.inl d) => LCS.Herbrand.HerbrandTheorem.Main.fmlaConstSymbols B d
      | .inl (.inr _) => True
      | .inr _ => False
  clauseFunctions : ∀ c ∈ clauseForm, ∀ lit ∈ c, ∀ f,
    LCS.Herbrand.HerbrandTheorem.Main.fmlaFuncSymbols (FOLiteral.formula (L := GroundRunLanguage skolem) hNoEq lit) f →
      match f with
      | .inl f => LCS.Herbrand.HerbrandTheorem.Main.fmlaFuncSymbols B f
      | .inr _ => True
  clauseSemantics : ∀ M : Structure (GroundRunLanguage skolem), ∀ s : Assignment M,
    formulaEvalN M clauseSentence s ↔
      ∀ c ∈ clauseForm, ∀ a : Assignment M, FOClause.isSatisfied (L := GroundRunLanguage skolem) hNoEq M a c
  skolemSemantics : ∀ M : Structure (GroundRunLanguage skolem), ∀ s : Assignment M,
    formulaEvalN M clauseSentence s ↔
      formulaEvalN M (groundRunLiftFormula (LCS.Herbrand.SHGTheorem.skolemForm skolem)) s
  equisatisfiable :
    (∃ (M : Structure L) (s : Assignment M), formulaEvalN M B s) ↔
      ∃ M : Structure (GroundRunLanguage skolem), ∀ c ∈ clauseForm,
        ∀ s : Assignment M, FOClause.isSatisfied (L := GroundRunLanguage skolem) hNoEq M s c

/-- Clause images are sets of literals: order and repeated literals do not
    affect origin or coverage. All substitution images use the input universe. -/
@[blueprint "chap8__lemma_8_3_1"]
def GroundRunInstance {L : Language} {hNoEq : L.withoutEquality} {B : FormulaN L}
    (N : GroundRunNormalization L hNoEq B)
    (C : FOClause (GroundRunLanguage N.skolem) hNoEq) : Prop :=
  FOClause.isGround (L := GroundRunLanguage N.skolem) hNoEq C ∧ ∃ source ∈ N.clauseForm,
    ∃ sigma : GroundSubstitution (GroundRunLanguage N.skolem),
      (∀ x, GroundRunTerm B N.skolem (sigma.toSubst x)) ∧
      ∀ lit, lit ∈ C ↔ lit ∈ groundInstantiate (L := GroundRunLanguage N.skolem) hNoEq sigma source

/-- The cumulative finite prefix after n enumeration steps. `none` denotes
    exhaustion, so empty and finite enumerations need no invented clause. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundRunPrefix {L : Language} {hNoEq : L.withoutEquality}
    (enumeration : Nat → Option (FOClause L hNoEq)) (n : Nat) : List (FOClause L hNoEq) :=
  (List.range n).filterMap enumeration

/-- An admissible ground-resolution run on B. Every reached prefix is tested;
    a negative test continues exactly when another instance is available.
    Successful and exhausted runs have no further reached stages. The supplied
    stream is fair, eventually exhausts any finite extensional instance set,
    and may be infinite otherwise. No successful prefix is assumed.
    Executable normalization, enumeration and testing are deferred (OD-A17). -/
@[blueprint "chap8__lemma_8_3_1"]
structure ThreeStepProcedure (L : Language) (hNoEq : L.withoutEquality)
    (B : FormulaN L) where
  normalization : GroundRunNormalization L hNoEq B
  enumeration : Nat → Option (FOClause (GroundRunLanguage normalization.skolem) hNoEq)
  origin : ∀ n C, enumeration n = some C → GroundRunInstance normalization C
  exhausted : ∀ n, enumeration n = none → enumeration (n + 1) = none
  coverage : ∀ C, GroundRunInstance normalization C →
    ∃ n D, enumeration n = some D ∧ ∀ lit, lit ∈ C ↔ lit ∈ D
  exhaustionComplete : ∀ n, enumeration n = none →
    ∀ C, GroundRunInstance normalization C →
      ∃ D ∈ groundRunPrefix enumeration n, ∀ lit, lit ∈ C ↔ lit ∈ D
  finiteExhaustion :
    (∃ all : List (FOClause (GroundRunLanguage normalization.skolem) hNoEq),
      ∀ C, GroundRunInstance normalization C →
        ∃ D ∈ all, ∀ lit, lit ∈ C ↔ lit ∈ D) → ∃ n, enumeration n = none
  test : Nat → Bool
  reached : Nat → Prop
  initial : reached 0
  next : ∀ n, reached (n + 1) ↔
    reached n ∧ test n = false ∧ enumeration n ≠ none
  testCorrect : ∀ n, reached n →
    (test n = true ↔ GroundClauseSet.isUnsatisfiable (L := GroundRunLanguage normalization.skolem) hNoEq
      (groundRunPrefix enumeration n))

/-- Success is a separate certificate at a reached positive test, carrying
    the actual resolution tree and its empty-root/leaf correctness proof. -/
@[blueprint "chap8__lemma_8_3_1"]
structure GroundRunSuccess {L : Language} {hNoEq : L.withoutEquality} {B : FormulaN L}
    (run : ThreeStepProcedure L hNoEq B) where
  stage : Nat
  reached : run.reached stage
  positive : run.test stage = true
  refutation : FOResolutionTree (GroundRunLanguage run.normalization.skolem) hNoEq
  valid : refutation.isRefutation (L := GroundRunLanguage run.normalization.skolem) hNoEq
    (fun C => C ∈ groundRunPrefix run.enumeration stage)

-- ===================================================================
-- Example 8.3.1: Ground clauses G1-G4
-- ===================================================================

/-- Example 8.3.1 (companion): The ground term f(a), obtained by applying the
    Skolem function f to the Skolem constant a. -/
@[blueprint "chap8__example_8_3_1"]
def exGroundTerm_fa : Term exClauseFormLang :=
  Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)

/-- Example 8.3.1: G1 = {not P(a,a)}, the ground clause obtained
    from C1 by substituting a for x and z1. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G1 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G2 = {P(a,f(a)), P(a,a)}, the ground clause
    obtained from C2 by substituting a for z2. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G2 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exSkolemConst_a exGroundTerm_fa),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G3 = {P(f(a),a), P(a,a)}, the ground clause
    obtained from C3 by substituting a for z3. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G3 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.3.1: G4 = {not P(f(a),a), not P(a,f(a))}, the ground
    clause obtained from C1 by substituting f(a) for z1 and a for x. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundClause_G4 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.neg (exPred_P exSkolemConst_a exGroundTerm_fa) ]

-- ===================================================================
-- Example 8.3.1: Resolution steps
-- ===================================================================

/-- Example 8.3.1: Resolution step 1 -- G2 resolves with G1 on
    P(a,a), yielding the unit clause {P(a,f(a))}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step1 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exGroundClause_G2)
    (.axiom_ exGroundClause_G1)
    (FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a))

/-- Example 8.3.1: Resolution step 2 -- G1 resolves with G3 on
    P(a,a), yielding the unit clause {P(f(a),a)}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step2 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exGroundClause_G3)
    (.axiom_ exGroundClause_G1)
    (FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a))

/-- Example 8.3.1: Resolution step 3 -- {P(f(a),a)} resolves with
    G4 on P(f(a),a), yielding {not P(a,f(a))}. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step3 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exGroundResolution_step2
    (.axiom_ exGroundClause_G4)
    (FOLiteralCore.pos
      (exPred_P (exGroundTerm_fa) exSkolemConst_a))

/-- Example 8.3.1: Resolution step 4 -- {P(a,f(a))} resolves with
    {not P(a,f(a))} on P(a,f(a)), yielding the empty clause. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_step4 :
    FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exGroundResolution_step1
    exGroundResolution_step3
    (FOLiteralCore.pos
      (exPred_P exSkolemConst_a (exGroundTerm_fa)))

-- ===================================================================
-- Example 8.3.1: Complete refutation
-- ===================================================================

/-- Example 8.3.1: The complete resolution tree deriving the empty
    clause from G1-G4 through four resolution steps. -/
@[blueprint "chap8__example_8_3_1" (main := true)]
def exGroundResolution_refutation :
    FOResolutionTree exClauseFormLang rfl :=
  exGroundResolution_step4

end LCS.FOResolution.GroundResolution
end

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical

/-- Lemma 8.3.1 (companion): Translate a first-order literal to a
    propositional literal, given an encoding function that maps atomic
    formulae to natural numbers. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundLiteralToProp {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat) : FOLiteral L hNoEq → Literal
  | .pos B => Literal.pos (encode B)
  | .neg B => Literal.neg (encode B)

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- The atom carried by a ground-resolution literal. -/
def groundLiteralAtom {L : Language} (hNoEq : L.withoutEquality) : FOLiteral L hNoEq → FOAtom L hNoEq
  | .pos atom | .neg atom => atom

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- All atoms occurring in a finite ground clause list, without duplicates. -/
noncomputable def groundClauseSetAtoms {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOClause L hNoEq)) : List (FOAtom L hNoEq) :=
  (S.flatMap fun c => c.map (groundLiteralAtom (hNoEq := hNoEq))).eraseDups

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Every source literal contributes its atom to `groundClauseSetAtoms`. -/
theorem groundClauseSetAtoms_mem {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOClause L hNoEq)) {c : FOClause L hNoEq} (hc : c ∈ S)
    {lit : FOLiteral L hNoEq} (hLit : lit ∈ c) :
    groundLiteralAtom (hNoEq := hNoEq) lit ∈ groundClauseSetAtoms (hNoEq := hNoEq) S := by
  classical
  unfold groundClauseSetAtoms
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨lit, hLit, rfl⟩⟩

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Encode an atom by its first position in a finite source-atom list. -/
noncomputable def finiteAtomEncode {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (atom : FOAtom L hNoEq) : Nat :=
  atoms.idxOf atom

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Decode an atom index into a nonempty finite source-atom list.  The
    modulo makes this total without fabricating a default atom outside the
    source image. -/
def finiteAtomDecodeIndex {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hAtoms : atoms ≠ []) (n : Nat) :
    Fin atoms.length :=
  ⟨n % atoms.length,
    Nat.mod_lt _ (by
      cases atoms with
      | nil => exact (hAtoms rfl).elim
      | cons _ _ => simp)⟩

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Decode through the canonical cyclic index into the source list. -/
def finiteAtomDecode {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hAtoms : atoms ≠ []) (n : Nat) : FOAtom L hNoEq :=
  atoms.get (finiteAtomDecodeIndex (hNoEq := hNoEq) atoms hAtoms n)

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Direct access at the first index of a member recovers that member. -/
theorem finiteAtom_get_idxOf {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (atom : FOAtom L hNoEq) (hAtom : atom ∈ atoms) :
    atoms[atoms.idxOf atom]'(List.idxOf_lt_length_iff.mpr hAtom) = atom := by
  induction atoms with
  | nil => cases hAtom
  | cons head tail ih =>
    simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
    by_cases hEq : head = atom
    · simp [hEq]
    · simp only [hEq, if_false]
      simp only [List.mem_cons] at hAtom
      rcases hAtom with hAtom | hAtom
      · exact absurd hAtom.symm hEq
      · simpa using ih hAtom

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- Looking up the first index of a list member returns that member. -/
theorem finiteAtomDecode_encode {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hAtoms : atoms ≠ []) (atom : FOAtom L hNoEq)
    (hAtom : atom ∈ atoms) :
    finiteAtomDecode (hNoEq := hNoEq) atoms hAtoms (finiteAtomEncode (hNoEq := hNoEq) atoms atom) = atom := by
  classical
  unfold finiteAtomDecode finiteAtomEncode
  have hIdx : atoms.idxOf atom < atoms.length :=
    List.idxOf_lt_length_iff.mpr hAtom
  have hFin :
      finiteAtomDecodeIndex (hNoEq := hNoEq) atoms hAtoms (atoms.idxOf atom) =
      ⟨atoms.idxOf atom, hIdx⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hIdx
  rw [hFin]
  exact finiteAtom_get_idxOf (hNoEq := hNoEq) atoms atom hAtom

/-- Lemma 8.3.1 (companion): Translate a ground first-order clause to
    a propositional clause. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundClauseToProp {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (c : FOClause L hNoEq) : Clause :=
  Finset.ofList (c.map (groundLiteralToProp (hNoEq := hNoEq) encode))

/-- Lemma 8.3.1 (companion): Translate a list of ground first-order
    clauses to a propositional clause sequent. -/
@[blueprint "chap8__lemma_8_3_1"]
def groundClauseSetToProp {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (S : List (FOClause L hNoEq)) : ClauseSequent :=
  Finset.ofList (S.map (groundClauseToProp (hNoEq := hNoEq) encode))

-- ===================================================================
-- Conjugate preservation
-- ===================================================================

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- The translation preserves conjugation: the propositional conjugate
    of the translation of a literal equals the translation of the
    first-order conjugate. -/
theorem groundLiteralToProp_conjugate {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat) (lit : FOLiteral L hNoEq) :
    Literal.conjugate (groundLiteralToProp (hNoEq := hNoEq) encode lit) =
    groundLiteralToProp (hNoEq := hNoEq) encode (FOLiteral.conjugate hNoEq lit) := by
-- BEGIN PROOF
  cases lit with
  | pos B => rfl
  | neg B => rfl

-- ===================================================================
-- Satisfaction preservation: FO to propositional direction
-- ===================================================================









-- ===================================================================
-- Satisfaction preservation: clause level (FO to prop)
-- ===================================================================





-- ===================================================================
-- FO unsatisfiability implies propositional unsatisfiability
-- ===================================================================

-- ===================================================================
-- Herbrand structure construction
-- ===================================================================

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- The auxiliary term structure for an equality-free language L.
    Its carrier is all terms, including variables, so it is nonempty even
    when the language has no ground terms. Functions and constants are
    interpreted syntactically; predicates use the supplied atomic truth
    assignment. Ground terms evaluate to themselves, as certified below,
    which is the property used by the ground-to-propositional bridge. -/
def herbrandStructure {L : Language} (hNoEq : L.withoutEquality)
    (truthVal : FOAtom L hNoEq → Prop) : Structure L where
  carrier := Term L
  carrierNonempty := by
    -- The carrier contains all terms; this witness imposes no
    -- nonemptiness requirement on the language's ground terms.
    exact ⟨Term.var 0⟩
  interpFunc := fun f args => Term.func f args
  interpConst := fun c => Term.const c
  interpPred := fun P args => truthVal (FOAtomCore.predN P args)

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation
/-- In the Herbrand structure, ground terms evaluate to themselves.
    More precisely, for a term t, termEval (herbrandStructure tv) s t
    equals t when t is ground (contains no variables). -/
theorem herbrand_termEval_ground {L : Language} (hNoEq : L.withoutEquality)
    (truthVal : FOAtom L hNoEq → Prop)
    (s : Assignment (herbrandStructure (hNoEq := hNoEq) truthVal))
    (t : Term L) (hGround : termVars t = Set.empty) :
    termEval (herbrandStructure (hNoEq := hNoEq) truthVal) s t = t := by
-- BEGIN PROOF
  induction t with
  | var n =>
    -- A variable is not ground
    exfalso
    have hmem : termVars (L := L) (.var n) n := rfl
    rw [hGround] at hmem; exact hmem
  | const c => rfl
  | func f args ih =>
    simp only [termEval, herbrandStructure]
    congr 1; ext i
    apply ih i
    -- Need: termVars (args i) = Set.empty
    funext m; apply propext
    constructor
    · intro hm
      have : termVars (Term.func f args) m := ⟨i, hm⟩
      rw [hGround] at this; exact this
    · intro h; exact h.elim





end LCS.FOResolution.GroundResolution
end
