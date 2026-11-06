import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import Attach
import LCS.Herbrand.HerbrandTheorem.Substitutions.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Substitutions
    Chapter 7, Section 5.3: Substitutions.

    Definition 7.5.3 (substitution functions, their homomorphic extension
    to terms, support, substitution instances of formulae), the Remark on
    sequential versus simultaneous substitution and ground substitutions,
    and substitution pairs.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

-- ===================================================================
-- Definition 7.5.3: Substitution
-- ===================================================================

/-- Definition 7.5.3: A substitution function (for short, a substitution) is any function sigma : V -> TERM_L assigning terms to the variables in V. Using Nat for variables, this is simply a function Nat -> Term L. -/
@[blueprint "chap7__definition_7_5_3" (main := true)]
abbrev Substitution (L : Language) : Type := Nat → Term L

namespace Substitution

/-- Definition 7.5.3 (companion def): The homomorphic extension sigma-hat applied to terms, defined recursively: sigma-hat(x) = sigma(x) for variables, sigma-hat(c) = c for constants, sigma-hat(f t_1...t_n) = f sigma-hat(t_1)...sigma-hat(t_n) for function applications. -/
@[blueprint "chap7__definition_7_5_3" (main := true)]
def applyTerm {L : Language} (sigma : Substitution L) :
    Term L → Term L
  | .var x => sigma x
  | .const c => .const c
  | .func f ts => .func f (fun i => applyTerm sigma (ts i))

/-- Definition 7.5.3: the constant-preserving homomorphic extension of an
arbitrary variable-to-term map is unique. A term map agreeing with sigma on
variables, fixing every constant and preserving each ranked function application
is exactly applyTerm sigma. The variable map has no finite-support restriction. -/
@[blueprint "chap7__definition_7_5_3" (main := true)]
theorem applyTerm_unique {L : Language} (sigma : Substitution L)
    (extend : Term L → Term L)
    (hVar : ∀ x, extend (.var x) = sigma x)
    (hConst : ∀ c, extend (.const c) = .const c)
    (hFunc : ∀ (f : L.funSymbols) (ts : Fin (L.funArity f) → Term L),
      extend (.func f ts) = .func f (fun i => extend (ts i))) :
    extend = applyTerm sigma

-- ===================================================================
-- Definition 7.5.3 (companion def): Substitution.support
-- ===================================================================

/-- Definition 7.5.3 (companion def): The support of a substitution sigma is the subset X of V consisting of variables x such that sigma(x) != Term.var x. -/
@[blueprint "chap7__definition_7_5_3"]
def support {L : Language} (sigma : Substitution L) : Set Nat :=
  fun x => sigma x ≠ Term.var x

-- ===================================================================
-- Definition 7.5.3 (companion def): Substitution.hasFiniteSupport
-- ===================================================================

/-- Definition 7.5.3 (companion def): Predicate that the support is finite: there exists a list containing exactly the variables changed by sigma. -/
@[blueprint "chap7__definition_7_5_3"]
def hasFiniteSupport {L : Language} (sigma : Substitution L) :
    Prop :=
  Set.Finite (support sigma)

-- ===================================================================
-- Definition 7.5.3 (companion def): Substitution.applyFormula
-- ===================================================================

/-- Definition 7.5.3 (companion): raw simultaneous substitution kernel.
It acts on free occurrences and shadows each quantified variable. The guarded
source instance is `applyInstance`, whose domain supplies the finite-support,
free-variable, bound-exclusion and free-for conditions. -/
@[blueprint "chap7__definition_7_5_3"]
def applyFormula {L : Language} (sigma : Substitution L) :
    FormulaN L → FormulaN L
  | .predN P ts => .predN P (fun i => applyTerm sigma (ts i))
  | .eq_ h t1 t2 => .eq_ h (applyTerm sigma t1) (applyTerm sigma t2)
  | .conj A B => .conj (applyFormula sigma A) (applyFormula sigma B)
  | .disj A B => .disj (applyFormula sigma A) (applyFormula sigma B)
  | .impl A B => .impl (applyFormula sigma A) (applyFormula sigma B)
  | .neg A => .neg (applyFormula sigma A)
  | .all x A =>
    -- Shadow x: replace sigma with sigma' where sigma'(x) = var x
    let sigma' : Substitution L := fun y =>
      if y = x then Term.var y else sigma y
    .all x (applyFormula sigma' A)
  | .ex x A =>
    let sigma' : Substitution L := fun y =>
      if y = x then Term.var y else sigma y
    .ex x (applyFormula sigma' A)

/-- Definition 7.5.3: admissibility of a substitution on a formula. Changed
variables actually occur free, never occur bound, and their images pass the
printed free-for test. The unrestricted variable-to-term map remains general. -/
@[blueprint "chap7__definition_7_5_3"]
structure Admissible {L : Language} (sigma : Substitution L) (A : FormulaN L) : Prop where
  finiteSupport : hasFiniteSupport sigma
  supportFree : ∀ x, support sigma x → x ∈ formulaFVN A
  supportNotBound : ∀ x, support sigma x → x ∉ formulaBVN A
  freeFor : ∀ x, support sigma x → isFreeForN (sigma x) x A

/-- Restrict a substitution to the variables actually free in the recursive
child formula; outside that finite syntactic list the map is the identity. -/
def restrictToFormula {L : Language} (sigma : Substitution L) (A : FormulaN L) :
    Substitution L :=
  fun x => if x ∈ formulaFreeVarIndices A then sigma x else .var x

/-- Immediate syntactic children used in the formula substitution clauses.
A quantified child is its original body, not a term-instantiated subformula. -/
def formulaChildren {L : Language} : FormulaN L → List (FormulaN L)
  | .predN _ _ | .eq_ _ _ _ => []
  | .conj A B | .disj A B | .impl A B => [A, B]
  | .neg A | .all _ A | .ex _ A => [A]

/-- Restricting an admissible substitution to an immediate recursive child
preserves the four source-domain conditions, including actual free support. -/
theorem Admissible.restrictToChild {L : Language} {sigma : Substitution L}
    {A : FormulaN L} (h : Admissible sigma A) (B : FormulaN L)
    (hB : B ∈ formulaChildren A) : Admissible (restrictToFormula sigma B) B := by
  -- REPAIR(T7-52): proof pending
  sorry

/-- Definition 7.5.3: simultaneous substitution on its specified domain.
Each recursive call receives the substitution restricted to that child's free
variables; atomic terms use the unchanged homomorphic term kernel. -/
@[blueprint "chap7__definition_7_5_3" (main := true)]
def applyInstance {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (h : Admissible sigma A) : FormulaN L :=
  match A with
  | .predN P ts => .predN P (fun i => applyTerm sigma (ts i))
  | .eq_ heq t u => .eq_ heq (applyTerm sigma t) (applyTerm sigma u)
  | .conj B C =>
    .conj (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))
      (applyInstance (restrictToFormula sigma C) C
        (h.restrictToChild C (by simp [formulaChildren])))
  | .disj B C =>
    .disj (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))
      (applyInstance (restrictToFormula sigma C) C
        (h.restrictToChild C (by simp [formulaChildren])))
  | .impl B C =>
    .impl (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))
      (applyInstance (restrictToFormula sigma C) C
        (h.restrictToChild C (by simp [formulaChildren])))
  | .neg B => .neg (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))
  | .all x B => .all x (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))
  | .ex x B => .ex x (applyInstance (restrictToFormula sigma B) B
      (h.restrictToChild B (by simp [formulaChildren])))

/-- The distinct proof-local domain for assignments to existential-prefix
variables, including vacuous binders. It does not require support to lie in the
free variables of the closed prenex sentence; later matrix use restricts it. -/
@[blueprint "chap7__definition_7_5_4"]
def IsExistentialPrefixAssignment {L : Language}
    (sigma : Substitution L) (A : FormulaN L) : Prop :=
  isPrenex A ∧ hasFiniteSupport sigma ∧
    ∀ x, support sigma x → (QuantifierKind.existential, x) ∈ prenexPrefix A

end Substitution


-- ===================================================================
-- Definition 7.5.3 (companion structure): SubstitutionPair
-- ===================================================================

/-- Definition 7.5.3: a formula and a substitution satisfying the specified
finite-support, free-support, bound-exclusion and free-for conditions. This is
the general formula-instance domain, distinct from existential-prefix assignments. -/
@[blueprint "chap7__definition_7_5_3"]
structure SubstitutionPair (L : Language) : Type where
  /-- The formula A -/
  formula : FormulaN L
  /-- The substitution sigma -/
  subst : Substitution L
  /-- The four admissibility conditions on this formula and substitution. -/
  admissible : Substitution.Admissible subst formula

end LCS.Herbrand.HerbrandTheorem
