import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import Attach
import LCS.FOResolution.Paramodulation.ProofsStamp

/-! # FOResolution.Paramodulation
    Formalization of Chapter 8, Section 8.6.
    The paramodulation rule for handling equality in resolution.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.Paramodulation

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

-- ===================================================================
-- TreeAddress: position within a term tree (Section 2.2)
-- ===================================================================

/-- Example 8.6.1 (companion): A tree address identifies a position
    within a term tree. The root address e is the empty path; child i u
    descends to child number i and then follows address u. Children are
    numbered from 1 as in Section 2.2; child 0 is invalid. -/
@[blueprint "chap8__example_8_6_1"]
inductive TreeAddress : Type where
  /-- The root address e (empty sequence) -/
  | root : TreeAddress
  /-- Prepend a one-based child number to the remaining path. -/
  | child : Nat → TreeAddress → TreeAddress

/-- Example 8.6.1 (companion): a term occurrence in a signed literal
    selects a one-based predicate argument or an equality side, followed by
    a term-tree suffix. The sign is retained on the literal's atomic head. -/
@[blueprint "chap8__example_8_6_1"]
inductive LiteralTermAddress : Type where
  | predicateArgument : Nat → TreeAddress → LiteralTermAddress
  | equalityLeft : TreeAddress → LiteralTermAddress
  | equalityRight : TreeAddress → LiteralTermAddress

-- ===================================================================
-- Literal: literal with explicit equation support
-- ===================================================================

/-- Example 8.6.1 (companion): a signed atomic literal. Equality uses
    the same atomic carrier in either sign and retains its language witness. -/
@[blueprint "chap8__example_8_6_1"]
abbrev Literal (L : Language) : Type := FOLiteralCore L

/-- Example 8.6.1 (companion): a finite clause of signed atoms. -/
@[blueprint "chap8__example_8_6_1"]
abbrev Clause (L : Language) : Type := FOClauseCore L

/-- Example 8.6.1 (companion): substitutions have finite support. -/
@[blueprint "chap8__example_8_6_1"]
abbrev Substitution (L : Language) : Type := FiniteSubstitution L

/-- Example 8.6.1 (companion): the variable map of a finite substitution. -/
@[blueprint "chap8__example_8_6_1"]
def Substitution.apply {L : Language} (sigma : Substitution L) : Nat → Term L :=
  sigma.map

/-- Example 8.6.1 (companion): already apart occurrences admit identity
    renamings, whose actual support is empty. -/
@[blueprint "chap8__example_8_6_1"]
def identitySubst {L : Language} : Substitution L := FiniteSubstitution.identity

-- ===================================================================
-- Example language types for Examples 8.6.1 and 8.6.2
-- ===================================================================

/-- Example 8.6.1 (companion): Function symbols for the paramodulation
    examples: binary f, binary g, and unary h. -/
@[blueprint "chap8__example_8_6_1"]
inductive ExampleFunc : Type where
  /-- Binary function symbol f -/
  | f : ExampleFunc
  /-- Binary function symbol g -/
  | g : ExampleFunc
  /-- Unary function symbol h -/
  | h : ExampleFunc

/-- Example 8.6.1 (companion): Constant symbols for the paramodulation
    examples: constant a. -/
@[blueprint "chap8__example_8_6_1"]
inductive ExampleConst : Type where
  /-- Constant a -/
  | a : ExampleConst

/-- Example 8.6.1 (companion): Predicate symbols for the paramodulation
    examples: unary P and unary Q. -/
@[blueprint "chap8__example_8_6_1"]
inductive ExamplePred : Type where
  /-- Unary predicate P -/
  | P : ExamplePred
  /-- Unary predicate Q -/
  | Q : ExamplePred

-- ===================================================================
-- ExampleLang: the concrete first-order language for examples
-- ===================================================================

/-- Example 8.6.1 (companion): The concrete first-order language with
    function symbols {f, g, h}, constant {a}, and predicates {P, Q}.
    f and g are binary, h is unary, P and Q are unary. -/
@[blueprint "chap8__example_8_6_1"]
def ExampleLang : Language where
  funSymbols := ExampleFunc
  funArity := fun
    | .f => 2
    | .g => 2
    | .h => 1
  constSymbols := ExampleConst
  predSymbols := ExamplePred
  predArity := fun
    | .P => 1
    | .Q => 1
  hasEquality := true

-- ===================================================================
-- subtermAt: retrieve subterm at a tree address
-- ===================================================================

/-- Example 8.6.1 (companion): Retrieves the subterm of a term at a
    given tree address. Returns none if the address is invalid
    (out of bounds). -/
@[blueprint "chap8__example_8_6_1"]
def subtermAt {L : Language} : Term L → TreeAddress → Option (Term L)
  | t, .root => some t
  | .func _ args, .child (i + 1) addr =>
    if h : i < _ then subtermAt (args ⟨i, h⟩) addr
    else none
  | _, .child _ _ => none

-- ===================================================================
-- replaceAt: replace subterm at a tree address
-- ===================================================================

/-- Example 8.6.1 (companion): Replaces the subterm at address u in a
    term by another term t, yielding Q[u <- t]. Returns none if the
    address is invalid. -/
@[blueprint "chap8__example_8_6_1"]
def replaceAt {L : Language} :
    Term L → TreeAddress → Term L → Option (Term L)
  | _, .root, replacement => some replacement
  | .func f args, .child (i + 1) addr, replacement =>
    if h : i < _ then
      match replaceAt (args ⟨i, h⟩) addr replacement with
      | some newChild =>
        some (.func f (fun j =>
          if j.val = i then newChild else args j))
      | none => none
    else none
  | _, .child _ _, _ => none

-- ===================================================================
-- Literal substitution for the paramodulation framework
-- ===================================================================

/-- Example 8.6.1 (companion): homomorphic substitution in the atom,
    preserving its sign and equality witness. -/
@[blueprint "chap8__example_8_6_1"]
def substLitP {L : Language} (sigma : Substitution L) : Literal L → Literal L
  | .pos atom => .pos (atom.mapTerms (fun t => termSubstAll t sigma.apply))
  | .neg atom => .neg (atom.mapTerms (fun t => termSubstAll t sigma.apply))

/-- Example 8.6.1 (companion): substitute into every signed atom of a clause. -/
@[blueprint "chap8__example_8_6_1"]
def substClause {L : Language} (sigma : Substitution L)
    (c : Clause L) : Clause L := c.map (substLitP sigma)

/-- Shared separation predicate for arbitrary-language clause occurrences.
    Renamings are injective into their local variable images, those images
    are disjoint, and each map fixes variables outside its own source clause. -/
def SeparatingPairCore {L : Language} (rho rho' : FiniteSubstitution L)
    (A B : FOClauseCore L) : Prop :=
  Method.substIsVarOnSet rho.map A.vars ∧
  Method.substIsVarOnSet rho'.map B.vars ∧
  Method.substInjectiveOnSet rho.map A.vars ∧
  Method.substInjectiveOnSet rho'.map B.vars ∧
  (∀ n, Method.substRangeOnSet rho.map A.vars n →
    ¬ Method.substRangeOnSet rho'.map B.vars n) ∧
  (∀ x, ¬ A.vars x → rho.map x = Term.var x) ∧
  (∀ x, ¬ B.vars x → rho'.map x = Term.var x)

/-- Example 8.6.1 (companion): the separating pair for the two parent
    occurrences, using support inclusion and disjoint local images. -/
@[blueprint "chap8__example_8_6_1"]
def IsSeparatingPairP {L : Language} (rho rho' : Substitution L)
    (A B : Clause L) : Prop := SeparatingPairCore rho rho' A B

/-- Example 8.6.1 (companion): two source parents and their finite
    renamings, with equality enabled and the renamed occurrences apart. -/
@[blueprint "chap8__example_8_6_1"]
structure ParentOccurrences (L : Language) where
  equalityEnabled : L.hasEquality = true
  sourceA : Clause L
  sourceB : Clause L
  renameA : Substitution L
  renameB : Substitution L
  separating : IsSeparatingPairP renameA renameB sourceA sourceB

/-- Example 8.6.1 (companion): the actual renamed first parent occurrence. -/
@[blueprint "chap8__example_8_6_1"]
def ParentOccurrences.clauseA {L : Language} (p : ParentOccurrences L) : Clause L :=
  substClause p.renameA p.sourceA

/-- Example 8.6.1 (companion): the actual renamed second parent occurrence. -/
@[blueprint "chap8__example_8_6_1"]
def ParentOccurrences.clauseB {L : Language} (p : ParentOccurrences L) : Clause L :=
  substClause p.renameB p.sourceB

/-- Example 8.6.1 (companion): printed result data with explicit apart
    parent occurrences. This record does not assert an inference relation. -/
@[blueprint "chap8__example_8_6_1"]
structure ParamodulationResult (L : Language) where
  parents : ParentOccurrences L
  address : TreeAddress
  result : Clause L

-- ===================================================================
-- Whole-literal term occurrences
-- ===================================================================

/-- Example 8.6.1 (companion): decode a whole-literal tree address.
    Predicate arguments are numbered 1,...,n; equality sides are 1 and 2.
    The literal root is an atomic-formula node, not an eligible term.
    The term suffix is checked by lookup or replacement. -/
@[blueprint "chap8__example_8_6_1"]
def decodeLiteralAddress {L : Language} (lit : Literal L) :
    TreeAddress → Option LiteralTermAddress
  | .root => none
  | .child i suffix =>
    match lit with
    | .pos (.predN P _) | .neg (.predN P _) =>
      if 0 < i ∧ i ≤ L.predArity P then
        some (.predicateArgument i suffix)
      else none
    | .pos (.eq_ _ _ _) | .neg (.eq_ _ _ _) =>
      match i with
      | 1 => some (.equalityLeft suffix)
      | 2 => some (.equalityRight suffix)
      | _ => none

/-- Example 8.6.1 (companion): retrieve Q/u at any predicate argument or
    either equality side, with a suffix locating a subterm. Variable and
    constant roots are eligible; malformed selectors or suffixes return none. -/
@[blueprint "chap8__example_8_6_1"]
def literalSubtermAt {L : Language} (lit : Literal L)
    (addr : LiteralTermAddress) : Option (Term L) :=
  let atom := match lit with | .pos a | .neg a => a
  match atom, addr with
  | .predN P args, .predicateArgument (i + 1) suffix =>
    if h : i < L.predArity P then subtermAt (args ⟨i, h⟩) suffix else none
  | .eq_ _ s _, .equalityLeft suffix => subtermAt s suffix
  | .eq_ _ _ t, .equalityRight suffix => subtermAt t suffix
  | _, _ => none

/-- Example 8.6.1 (companion): replace exactly the selected atomic term
    occurrence, keeping every other argument or equality side unchanged. -/
@[blueprint "chap8__example_8_6_1"]
def replaceAtomAt {L : Language} (atom : FOAtomCore L)
    (addr : LiteralTermAddress) (replacement : Term L) : Option (FOAtomCore L) :=
  match atom, addr with
  | .predN P args, .predicateArgument (i + 1) suffix =>
    if h : i < L.predArity P then
      (replaceAt (args ⟨i, h⟩) suffix replacement).map fun newTerm =>
        .predN P (fun j => if j.val = i then newTerm else args j)
    else none
  | .eq_ hEq s t, .equalityLeft suffix =>
    (replaceAt s suffix replacement).map fun newS => .eq_ hEq newS t
  | .eq_ hEq s t, .equalityRight suffix =>
    (replaceAt t suffix replacement).map fun newT => .eq_ hEq s newT
  | _, _ => none

/-- Example 8.6.1 (companion): replacement at an explicit whole-literal
    term occurrence preserves the sign, including negative equality. -/
@[blueprint "chap8__example_8_6_1"]
def replaceLiteralAt {L : Language} (lit : Literal L)
    (addr : LiteralTermAddress) (replacement : Term L) : Option (Literal L) :=
  match lit with
  | .pos atom => (replaceAtomAt atom addr replacement).map FOLiteralCore.pos
  | .neg atom => (replaceAtomAt atom addr replacement).map FOLiteralCore.neg

-- ===================================================================
-- paramodulant: the paramodulation rule
-- ===================================================================

/-- Example 8.6.1 (companion): an equation is a two-way rewrite rule.
    Each orientation selects its own side for unification. -/
@[blueprint "chap8__example_8_6_1"]
inductive ParamodulationOrientation : Type where
  | leftToRight
  | rightToLeft

/-- The equation side unified with the addressed recipient subterm. -/
@[blueprint "chap8__example_8_6_1"]
def ParamodulationOrientation.selectedSide {L : Language}
    (direction : ParamodulationOrientation) (s t : Term L) : Term L :=
  match direction with
  | .leftToRight => s
  | .rightToLeft => t

/-- The other equation side replaces the addressed recipient subterm. -/
@[blueprint "chap8__example_8_6_1"]
def ParamodulationOrientation.replacementSide {L : Language}
    (direction : ParamodulationOrientation) (s t : Term L) : Term L :=
  match direction with
  | .leftToRight => t
  | .rightToLeft => s

/-- Example 8.6.1 (companion): explicit data for any donor equation,
    recipient literal and term occurrence. Legality is checked separately
    against the renamed-apart parents, so no list-head choice is imposed. -/
@[blueprint "chap8__example_8_6_1"]
structure ParamodulationSelection (L : Language) where
  left : Term L
  right : Term L
  recipient : Literal L
  donorRemainder : Clause L
  recipientRemainder : Clause L
  address : LiteralTermAddress
  orientation : ParamodulationOrientation
  sigma : Substitution L

/-- Example 8.6.1 (companion): the donor is a positive equation in A;
    the recipient can have either sign in B. Remainders are exactly the
    parent clauses with the selected literals removed, as sets. The finite
    substitution is an MGU of the selected equation side and Q/u, including
    the support condition of the chapter's MGU definition. -/
@[blueprint "chap8__example_8_6_1"]
def IsLegalParamodulationSelection {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L) : Prop :=
  let donor : Literal L := .pos (.eq_ parents.equalityEnabled choice.left choice.right)
  donor ∈ parents.clauseA ∧
  choice.recipient ∈ parents.clauseB ∧
  (∀ lit, lit ∈ choice.donorRemainder ↔ lit ∈ parents.clauseA ∧ lit ≠ donor) ∧
  (∀ lit, lit ∈ choice.recipientRemainder ↔
    lit ∈ parents.clauseB ∧ lit ≠ choice.recipient) ∧
  ∃ r, literalSubtermAt choice.recipient choice.address = some r ∧
    IsMGU choice.sigma [choice.orientation.selectedSide choice.left choice.right, r]

/-- Example 8.6.1 (companion): replace the selected term by the other
    equation side and apply the finite substitution to the entire union
    C ∨ Q[u ← t] ∨ D (or C ∨ Q[u ← s] ∨ D in the reverse orientation).
    This computes a candidate; the inference relation requires legality. -/
@[blueprint "chap8__example_8_6_1"]
def paramodulant {L : Language} (choice : ParamodulationSelection L) :
    Option (Clause L) :=
  (replaceLiteralAt choice.recipient choice.address
    (choice.orientation.replacementSide choice.left choice.right)).map fun newQ =>
      substClause choice.sigma (choice.donorRemainder ++ [newQ] ++ choice.recipientRemainder)

/-- Example 8.6.1 (companion): all legal paramodulation choices in the
    given apart parent occurrences, with the output identified extensionally.
    The computation and inference use the same selected occurrence and MGU. -/
@[blueprint "chap8__example_8_6_1"]
def IsParamodulant {L : Language} (parents : ParentOccurrences L) (result : Clause L) : Prop :=
  ∃ choice : ParamodulationSelection L, IsLegalParamodulationSelection parents choice ∧
    ∃ computed, paramodulant choice = some computed ∧
      ∀ lit, lit ∈ result ↔ lit ∈ computed

/-- Every addressed subterm admits replacement by any term. -/
@[blueprint "chap8__example_8_6_1"]
theorem literalSubtermAt_replace_exists {L : Language}
    (lit : Literal L) (addr : LiteralTermAddress) (r replacement : Term L)
    (found : literalSubtermAt lit addr = some r) :
    ∃ newLit, replaceLiteralAt lit addr replacement = some newLit

/-- A legal computed candidate is a paramodulant of the apart parents. -/
@[blueprint "chap8__example_8_6_1"]
theorem paramodulant_isParamodulant {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L) (result : Clause L)
    (legal : IsLegalParamodulationSelection parents choice)
    (computed : paramodulant choice = some result) : IsParamodulant parents result

/-- Every legal choice computes a clause and certifies that inference. -/
@[blueprint "chap8__example_8_6_1"]
theorem legalParamodulation_computes {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L)
    (legal : IsLegalParamodulationSelection parents choice) :
    ∃ result, paramodulant choice = some result ∧ IsParamodulant parents result

/-- Forward orientation: the MGU guard selects s, and replacement uses t. -/
@[blueprint "chap8__example_8_6_1"]
theorem paramodulation_leftToRight {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L) (newQ : Literal L)
    (legal : IsLegalParamodulationSelection parents { choice with orientation := .leftToRight })
    (replaced : replaceLiteralAt choice.recipient choice.address choice.right = some newQ) :
    IsParamodulant parents
      (substClause choice.sigma (choice.donorRemainder ++ [newQ] ++ choice.recipientRemainder))

/-- Reverse orientation: the MGU guard selects t, and replacement uses s. -/
@[blueprint "chap8__example_8_6_1"]
theorem paramodulation_rightToLeft {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L) (newQ : Literal L)
    (legal : IsLegalParamodulationSelection parents { choice with orientation := .rightToLeft })
    (replaced : replaceLiteralAt choice.recipient choice.address choice.left = some newQ) :
    IsParamodulant parents
      (substClause choice.sigma (choice.donorRemainder ++ [newQ] ++ choice.recipientRemainder))

-- ===================================================================
-- factor: factoring rule
-- ===================================================================

/-- Example 8.6.1 (companion): Check whether two literals have the same
    sign (both positive or both negative), including equality atoms,
    so they are candidates for factoring. -/
@[blueprint "chap8__example_8_6_1"]
def literalsSamePolarity {L : Language} :
    Literal L → Literal L → Bool
  | .pos _, .pos _ => true
  | .neg _, .neg _ => true
  | _, _ => false

/-- Example 8.6.1 (companion): a finite substitution unifies a nonempty
    set of signed literals when all of its literal images agree. Signs and
    predicate/equality symbols are rigid; negative literals retain their sign. -/
@[blueprint "chap8__example_8_6_1"]
def IsLiteralUnifier {L : Language} (sigma : Substitution L)
    (selected : Clause L) : Prop :=
  selected ≠ [] ∧
  ∀ lit ∈ selected, ∀ other ∈ selected,
    substLitP sigma lit = substLitP sigma other

/-- Example 8.6.1 (companion): the MGU of a literal set has support contained
    in its variables, and every finite unifier factors through it globally.
    Composition applies sigma first and then the homomorphic extension of rho. -/
@[blueprint "chap8__example_8_6_1"]
def IsLiteralMGU {L : Language} (sigma : Substitution L)
    (selected : Clause L) : Prop :=
  IsLiteralUnifier sigma selected ∧
  (∀ x, sigma.apply x ≠ Term.var x → FOClauseCore.vars selected x) ∧
  (∀ tau : Substitution L, IsLiteralUnifier tau selected →
    ∃ rho : Substitution L, ∀ x,
      tau.apply x = termSubstAll (sigma.apply x) rho.apply)

/-- Example 8.6.1 (companion): C is a factor of A when some nonempty
    same-sign subset of A has a certified MGU sigma and C is the whole-clause
    image sigma(A). Clauses are compared as literal sets, allowing arbitrary
    list order and duplicate representatives. Singleton identity factors are
    included. No literal is removed before applying the substitution. -/
@[blueprint "chap8__example_8_6_1"]
def factor {L : Language} (A C : Clause L) : Prop :=
  ∃ selected : Clause L, ∃ sigma : Substitution L,
    (∀ lit ∈ selected, lit ∈ A) ∧
    (∀ lit ∈ selected, ∀ other ∈ selected,
      literalsSamePolarity lit other = true) ∧
    IsLiteralMGU sigma selected ∧
    (∀ lit, lit ∈ C ↔ lit ∈ substClause sigma A)

/-- Example 8.6.1 (companion): a singleton literal set has the identity MGU. -/
@[blueprint "chap8__example_8_6_1"]
theorem identity_isLiteralMGU_singleton {L : Language} (lit : Literal L) :
    IsLiteralMGU identitySubst [lit]

/-- Example 8.6.1 (companion): selecting any one literal yields the identity
    factor of the whole clause, even when that clause has only one literal. -/
@[blueprint "chap8__example_8_6_1"]
theorem factor_identity {L : Language} (A : Clause L) (lit : Literal L)
    (hLit : lit ∈ A) : factor A A

/-- Example 8.6.1 (companion): the adopted nonempty-subset rule has no
    factor of the empty input clause. -/
@[blueprint "chap8__example_8_6_1"]
theorem empty_clause_has_no_factor {L : Language} (C : Clause L) :
    ¬ factor ([] : Clause L) C

-- ===================================================================
-- binaryResolvent: binary resolution
-- ===================================================================

/-- Example 8.6.1 (companion): the conjugate reverses the sign of an
    atomic literal, including an equality literal. -/
@[blueprint "chap8__example_8_6_1"]
def conjugateLiteral {L : Language} : Literal L → Literal L :=
  FOLiteralCore.conjugate

/-- Example 8.6.1 (companion): complementary literals have opposite signs
    and exactly the same atom. For resolution this is checked after the MGU. -/
@[blueprint "chap8__example_8_6_1"]
def literalsComplementary {L : Language} : Literal L → Literal L → Prop
  | .pos a, .neg b | .neg a, .pos b => a = b
  | _, _ => False

/-- Example 8.6.1 (companion): C is a binary resolvent of two apart parent
    occurrences, formed by finite separating renamings, when one pivot is
    selected from each, their substituted images are complementary, and sigma
    is an MGU of the first pivot and the conjugate
    of the second. C is exactly the substituted union of the two remainders.
    Set difference removes the selected literal before substitution; membership
    equality makes the rule independent of list ordering and duplicates. -/
@[blueprint "chap8__example_8_6_1"]
def binaryResolvent {L : Language} (A B C : Clause L) : Prop :=
  ∃ renameA renameB : Substitution L,
    IsSeparatingPairP renameA renameB A B ∧
    ∃ pivotA ∈ substClause renameA A, ∃ pivotB ∈ substClause renameB B,
      ∃ sigma : Substitution L,
        literalsComplementary (substLitP sigma pivotA) (substLitP sigma pivotB) ∧
        IsLiteralMGU sigma [pivotA, conjugateLiteral pivotB] ∧
        (∀ lit, lit ∈ C ↔
          (∃ source ∈ substClause renameA A,
            source ≠ pivotA ∧ substLitP sigma source = lit) ∨
          (∃ source ∈ substClause renameB B,
            source ≠ pivotB ∧ substLitP sigma source = lit))

/-- Example 8.6.1 (companion): an empty parent supplies no singleton pivot. -/
@[blueprint "chap8__example_8_6_1"]
theorem binaryResolvent_empty_left {L : Language} (B C : Clause L) :
    ¬ binaryResolvent [] B C

-- ===================================================================
-- reflexivityAxiom: the reflexivity axiom clause {x = x}
-- ===================================================================

/-- Example 8.6.1 (companion): The reflexivity axiom clause {x = x},
    required for completeness of the paramodulation method.
    Uses variable 0. -/
@[blueprint "chap8__example_8_6_1"]
def reflexivityAxiom {L : Language} (hEq : L.hasEquality = true) : Clause L :=
  [.pos (.eq_ hEq (Term.var 0) (Term.var 0))]

-- ===================================================================
-- functionalReflexivityAxiom: {f(x1,...,xn) = f(x1,...,xn)}
-- ===================================================================

/-- Example 8.6.1 (companion): the per-symbol unit-clause matrix
    {f(x1,...,xn) = f(x1,...,xn)}, with the same ordered distinct variables
    on both sides. The S-indexed family below imposes occurrence and positive
    rank; this matrix builder alone imposes neither family condition. -/
@[blueprint "chap8__example_8_6_1"]
def functionalReflexivityAxiom {L : Language} (hEq : L.hasEquality = true)
    (f : L.funSymbols) : Clause L :=
  let args : Fin (L.funArity f) → Term L := fun i => Term.var i.val
  [.pos (.eq_ hEq (Term.func f args) (Term.func f args))]

/-- Function-symbol occurrences in a finite term, retaining duplicates. -/
def termFunctionSymbolsCore {L : Language} : Term L → List L.funSymbols
  | .var _ => []
  | .const _ => []
  | .func f args => f :: (List.ofFn fun i => termFunctionSymbolsCore (args i)).flatten

/-- Function-symbol occurrences in every argument or equality side of a signed atom. -/
def literalFunctionSymbolsCore {L : Language} (lit : Literal L) : List L.funSymbols :=
  let atom := match lit with | .pos a | .neg a => a
  match atom with
  | .predN _ args => (List.ofFn fun i => termFunctionSymbolsCore (args i)).flatten
  | .eq_ _ s t => termFunctionSymbolsCore s ++ termFunctionSymbolsCore t

/-- Example 8.6.2 (companion): symbols occurring in the original finite input S.
    Every term occurrence is visited, in both literal signs and both equality
    sides. Constants are a separate symbol sort. Repetitions do not affect
    membership in the resulting family of clauses. -/
@[blueprint "chap8__example_8_6_2"]
def originalFunctionSymbols {L : Language} (S : List (Clause L)) : List L.funSymbols :=
  S.flatMap fun C => C.flatMap literalFunctionSymbolsCore

/-- Example 8.6.2 (companion): the functional reflexivity axioms indexed by
    the original S, for exactly its occurring function symbols of rank n > 0.
    This is a concrete finite list representing the family extensionally;
    symbols and clauses need no decidable equality. A clause already in S is
    still included. Ordinary reflexivity is a separate axiom. -/
@[blueprint "chap8__example_8_6_2"]
def functionalReflexivityAxioms {L : Language} (hEq : L.hasEquality = true)
    (S : List (Clause L)) : List (Clause L) :=
  ((originalFunctionSymbols S).filter fun f => decide (0 < L.funArity f)).map
    (functionalReflexivityAxiom hEq)

/-- Family membership is exactly an occurring positive-rank symbol's unit equation. -/
@[blueprint "chap8__example_8_6_2"]
theorem mem_functionalReflexivityAxioms {L : Language} (hEq : L.hasEquality = true)
    (S : List (Clause L)) (C : Clause L) :
    C ∈ functionalReflexivityAxioms hEq S ↔
      ∃ f, f ∈ originalFunctionSymbols S ∧ 0 < L.funArity f ∧
        functionalReflexivityAxiom hEq f = C

/-- A particular function contributes its clause exactly when it occurs
    in original S and has positive rank. Unused and nullary functions contribute none. -/
@[blueprint "chap8__example_8_6_2"]
theorem functionalReflexivityAxioms_for_symbol {L : Language} (hEq : L.hasEquality = true)
    (S : List (Clause L)) (f : L.funSymbols) :
    functionalReflexivityAxiom hEq f ∈ functionalReflexivityAxioms hEq S ↔
      f ∈ originalFunctionSymbols S ∧ 0 < L.funArity f

/-- The empty original input contributes no functional reflexivity axioms. -/
@[blueprint "chap8__example_8_6_2"]
theorem functionalReflexivityAxioms_empty {L : Language} (hEq : L.hasEquality = true) :
    functionalReflexivityAxioms hEq [] = []

/-- Functional reflexivity uses exactly one positive repeated-term equation. -/
@[blueprint "chap8__example_8_6_2"]
theorem functionalReflexivityAxiom_shape {L : Language} (hEq : L.hasEquality = true)
    (f : L.funSymbols) :
    functionalReflexivityAxiom hEq f =
      [.pos (.eq_ hEq (Term.func f (fun i => Term.var i.val))
        (Term.func f (fun i => Term.var i.val)))]

/-- The ordered variable arguments of a functional reflexivity clause are distinct. -/
@[blueprint "chap8__example_8_6_2"]
theorem functionalReflexivity_variables_distinct {L : Language} (f : L.funSymbols)
    (i j : Fin (L.funArity f)) (different : i ≠ j) :
    (Term.var i.val : Term L) ≠ Term.var j.val

/-- Occurrence in an existing positive-rank functional clause still includes
    that clause in the family; the family is not subtracted from S. -/
@[blueprint "chap8__example_8_6_2"]
theorem functionalReflexivityAxioms_alreadyPresent {L : Language}
    (hEq : L.hasEquality = true) (S : List (Clause L)) (f : L.funSymbols)
    (positive : 0 < L.funArity f) (present : functionalReflexivityAxiom hEq f ∈ S) :
    functionalReflexivityAxiom hEq f ∈ functionalReflexivityAxioms hEq S

/-- Ordinary variable reflexivity remains separate from the functional family. -/
@[blueprint "chap8__example_8_6_2"]
theorem reflexivityAxiom_not_functional {L : Language} (hEq : L.hasEquality = true)
    (S : List (Clause L)) :
    reflexivityAxiom hEq ∉ functionalReflexivityAxioms hEq S

-- ===================================================================
-- Finite derivations for the binary and equality calculi
-- ===================================================================

/-- A finite derivation, indexed by its exact premise family and conclusion.
    Each constructor records the relevant legal inference. The two switches
    select the available unary factoring and binary paramodulation rules;
    binary resolution is always available. Inductive construction excludes
    cyclic or infinite derivations. No semantic oracle or implicit axiom leaf
    is supplied by this shared carrier. -/
inductive ClauseDerivationCore {L : Language} (premises : List (Clause L))
    (allowFactoring allowParamodulation : Bool) : Clause L → Prop where
  | input {C : Clause L} (member : C ∈ premises) :
      ClauseDerivationCore premises allowFactoring allowParamodulation C
  | resolution {A B C : Clause L}
      (left : ClauseDerivationCore premises allowFactoring allowParamodulation A)
      (right : ClauseDerivationCore premises allowFactoring allowParamodulation B)
      (legal : binaryResolvent A B C) :
      ClauseDerivationCore premises allowFactoring allowParamodulation C
  | factoring {A C : Clause L} (enabled : allowFactoring = true)
      (parent : ClauseDerivationCore premises allowFactoring allowParamodulation A)
      (legal : factor A C) :
      ClauseDerivationCore premises allowFactoring allowParamodulation C
  | paramodulation {C : Clause L} (enabled : allowParamodulation = true)
      (parents : ParentOccurrences L)
      (donor : ClauseDerivationCore premises allowFactoring allowParamodulation parents.sourceA)
      (recipient : ClauseDerivationCore premises allowFactoring allowParamodulation parents.sourceB)
      (legal : IsParamodulant parents C) :
      ClauseDerivationCore premises allowFactoring allowParamodulation C

/-- Example 8.6.2 (companion): a finite empty-clause derivation from the
    explicit premise family using only legal binary resolution steps.
    Equality-free hypotheses on completeness are supplied by those statements;
    this syntactic relation itself uses the general signed atomic carrier. -/
@[blueprint "chap8__example_8_6_2"]
def BinaryRefutation {L : Language} (premises : List (Clause L)) : Prop :=
  ClauseDerivationCore premises false false []

/-- Example 8.6.2 (companion): a finite empty-clause derivation using legal
    binary resolution and factoring, including singleton identity factors.
    Every leaf must belong to the explicit premise family. -/
@[blueprint "chap8__example_8_6_2"]
def BinaryFactoringRefutation {L : Language} (premises : List (Clause L)) : Prop :=
  ClauseDerivationCore premises true false []

/-- Example 8.6.2 (companion): a finite empty-clause derivation in the
    equality-enabled three-rule calculus: binary resolution, factoring and
    either selected-side paramodulation orientation. Equality atoms use the
    canonical FOAtomCore.toFormula embedding, whose formulaEvalN interpretation
    is identity of term values. The supplied premises are the entire allowed
    leaf family; ordinary and functional reflexivity must be added explicitly
    by the corresponding completeness statement. -/
@[blueprint "chap8__example_8_6_2"]
def EqualityRefutation {L : Language} (_hEq : L.hasEquality = true)
    (premises : List (Clause L)) : Prop :=
  ClauseDerivationCore premises true true []

-- ===================================================================
-- Helper: build Fin-indexed argument vectors
-- ===================================================================

/-- Example 8.6.1 (companion): Build a Fin 1 -> Term L from one term. -/
@[blueprint "chap8__example_8_6_1"]
def pvec1 (a : Term ExampleLang) : Fin 1 → Term ExampleLang
  | ⟨0, _⟩ => a

/-- Example 8.6.1 (companion): Build a Fin 2 -> Term L from two terms. -/
@[blueprint "chap8__example_8_6_1"]
def pvec2 (a b : Term ExampleLang) : Fin 2 → Term ExampleLang
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

-- ===================================================================
-- Example 8.6.1: Concrete clauses and paramodulant
-- ===================================================================

/-- Example 8.6.1 (companion): Shorthand for building f(a,b) in
    ExampleLang. -/
@[blueprint "chap8__example_8_6_1"]
def mkF (a b : Term ExampleLang) : Term ExampleLang :=
  Term.func ExampleFunc.f (pvec2 a b)

/-- Example 8.6.1 (companion): Shorthand for building g(a,b). -/
@[blueprint "chap8__example_8_6_1"]
def mkG (a b : Term ExampleLang) : Term ExampleLang :=
  Term.func ExampleFunc.g (pvec2 a b)

/-- Example 8.6.1 (companion): Shorthand for building h(a). -/
@[blueprint "chap8__example_8_6_1"]
def mkH (a : Term ExampleLang) : Term ExampleLang :=
  Term.func ExampleFunc.h (pvec1 a)

/-- Example 8.6.1 (companion): Shorthand for the constant a. -/
@[blueprint "chap8__example_8_6_1"]
def mkA : Term ExampleLang :=
  Term.const ExampleConst.a

/-- Example 8.6.1 (companion): Shorthand for building the atomic formula
    P(t). -/
@[blueprint "chap8__example_8_6_1"]
def mkPredP (t : Term ExampleLang) : FOAtomCore ExampleLang :=
  FOAtomCore.predN ExamplePred.P (pvec1 t)

/-- Example 8.6.1 (companion): Shorthand for building the atomic formula
    Q(t). -/
@[blueprint "chap8__example_8_6_1"]
def mkPredQ (t : Term ExampleLang) : FOAtomCore ExampleLang :=
  FOAtomCore.predN ExamplePred.Q (pvec1 t)

/-- Example 8.6.1: Clause A = {f(x, h(y)) = g(x, y), P(x)}.
    Variables: x = 0, y = 1. -/
@[blueprint "chap8__example_8_6_1" (main := true)]
def clauseA_8_6_1 : Clause ExampleLang :=
  [ .pos (.eq_ rfl
      (mkF (Term.var 0) (mkH (Term.var 1)))
      (mkG (Term.var 0) (Term.var 1))),
    FOLiteralCore.pos (mkPredP (Term.var 0)) ]

/-- Example 8.6.1: Clause B = {Q(h(f(h(x), h(a))))}.
    Variable: x = 2 (renamed apart from clause A). -/
@[blueprint "chap8__example_8_6_1" (main := true)]
def clauseB_8_6_1 : Clause ExampleLang :=
  [ FOLiteralCore.pos (mkPredQ (mkH (mkF (mkH (Term.var 2)) (mkH mkA)))) ]

/-- Example 8.6.1: The printed output {Q(h(g(h(z),h(a)))), P(h(z))}.
    The substitution x ↦ h(z), y ↦ a instead sends g(x,y) to g(h(z),a).
    This preserves the printed data; it does not certify the inference. -/
@[blueprint "chap8__example_8_6_1" (main := true)]
def paramodulant_8_6_1 : Clause ExampleLang :=
  [ FOLiteralCore.pos (mkPredQ (mkH (mkG (mkH (Term.var 2)) (mkH mkA)))),
    FOLiteralCore.pos (mkPredP (mkH (Term.var 2))) ]

/-- Example 8.6.1 (companion): the stored premise copies already have
    disjoint variables, so the identity pair separates them. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleParents1_separating :
    IsSeparatingPairP (identitySubst (L := ExampleLang)) identitySubst
      clauseA_8_6_1 clauseB_8_6_1

/-- Example 8.6.1 (companion): explicit apart parent occurrences over
    the displayed equality-enabled language. -/
@[blueprint "chap8__example_8_6_1"]
def exampleParents1 : ParentOccurrences ExampleLang where
  equalityEnabled := rfl
  sourceA := clauseA_8_6_1
  sourceB := clauseB_8_6_1
  renameA := identitySubst
  renameB := identitySubst
  separating := exampleParents1_separating

/-- Example 8.6.1: The printed clauses, address 11, and output, stored as
    data. The displayed h(a) in the second argument of g conflicts with
    the substitution calculation below. -/
@[blueprint "chap8__example_8_6_1" (main := true)]
def paramodulationExample1 : ParamodulationResult ExampleLang :=
  { parents := exampleParents1,
    address := TreeAddress.child 1 (TreeAddress.child 1 TreeAddress.root),
    result := paramodulant_8_6_1 }

/-- Example 8.6.1 (companion): the finite substitution x ↦ h(z), y ↦ a,
    with x = 0, y = 1 and the apart variable z = 2. -/
@[blueprint "chap8__example_8_6_1"]
def exampleSubst1 : Substitution ExampleLang where
  support := [0, 1]
  map := fun
    | 0 => mkH (Term.var 2)
    | 1 => mkA
    | n => Term.var n
  outsideSupport := by
    intro n hn
    match n with
    | 0 => simp at hn
    | 1 => simp at hn
    | n + 2 => rfl

/-- Example 8.6.1 (companion): only x and y can be changed. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSubst1_finite (n : Nat) (hn : n ∉ [0, 1]) :
    exampleSubst1.apply n = Term.var n

/-- Example 8.6.1 (companion): the selected sides have common image
    f(h(z),h(a)); the replacement and residual literal have images
    g(h(z),a) and P(h(z)). These are substitution calculations. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSubst1_images :
    termSubstAll (mkF (Term.var 0) (mkH (Term.var 1))) exampleSubst1.apply =
      mkF (mkH (Term.var 2)) (mkH mkA) ∧
    termSubstAll (mkF (mkH (Term.var 2)) (mkH mkA)) exampleSubst1.apply =
      mkF (mkH (Term.var 2)) (mkH mkA) ∧
    termSubstAll (mkG (Term.var 0) (Term.var 1)) exampleSubst1.apply =
      mkG (mkH (Term.var 2)) mkA ∧
    substLitP exampleSubst1 (FOLiteralCore.pos (mkPredP (Term.var 0))) =
      FOLiteralCore.pos (mkPredP (mkH (Term.var 2)))

/-- Example 8.6.1 (companion): the calculated second argument of g is a,
    which differs from the printed h(a). -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSubst1_printedConflict :
    termSubstAll (Term.var 1) exampleSubst1.apply ≠ mkH mkA

-- ===================================================================
-- Example 8.6.2: Language variant with unary g
-- ===================================================================

/-- Example 8.6.2 (companion): The language for Example 8.6.2 where g
    is unary (the textbook uses g(x) with a single argument in this
    example, unlike Example 8.6.1 where g is binary). Reuses ExampleFunc
    but changes g's arity to 1. -/
@[blueprint "chap8__example_8_6_2"]
def ExampleLang2 : Language where
  funSymbols := ExampleFunc
  funArity := fun
    | .f => 2
    | .g => 1
    | .h => 1
  constSymbols := ExampleConst
  predSymbols := ExamplePred
  predArity := fun
    | .P => 1
    | .Q => 1
  hasEquality := true

-- Helpers for building terms in ExampleLang2

/-- Example 8.6.2 (companion): Build a Fin 1 -> Term ExampleLang2 from
    one term. -/
@[blueprint "chap8__example_8_6_2"]
def pvec1' (a : Term ExampleLang2) :
    Fin 1 → Term ExampleLang2
  | ⟨0, _⟩ => a

/-- Example 8.6.2 (companion): Build a Fin 2 -> Term ExampleLang2 from
    two terms. -/
@[blueprint "chap8__example_8_6_2"]
def pvec2' (a b : Term ExampleLang2) :
    Fin 2 → Term ExampleLang2
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

/-- Example 8.6.2 (companion): Build f(a,b) in ExampleLang2. -/
@[blueprint "chap8__example_8_6_2"]
def mkF' (a b : Term ExampleLang2) : Term ExampleLang2 :=
  Term.func ExampleFunc.f (pvec2' a b)

/-- Example 8.6.2 (companion): Build g(a) (unary) in ExampleLang2. -/
@[blueprint "chap8__example_8_6_2"]
def mkG' (a : Term ExampleLang2) : Term ExampleLang2 :=
  Term.func ExampleFunc.g (pvec1' a)

/-- Example 8.6.2 (companion): Build h(a) in ExampleLang2. -/
@[blueprint "chap8__example_8_6_2"]
def mkH' (a : Term ExampleLang2) : Term ExampleLang2 :=
  Term.func ExampleFunc.h (pvec1' a)

/-- Example 8.6.2 (companion): Build constant a in ExampleLang2. -/
@[blueprint "chap8__example_8_6_2"]
def mkA' : Term ExampleLang2 :=
  Term.const ExampleConst.a

-- ===================================================================
-- Example 8.6.2: Concrete clauses and paramodulant
-- ===================================================================

/-- Example 8.6.2: Clause A = {f(g(x), x) = h(a)}.
    Variable: x = 0. Here g is unary. -/
@[blueprint "chap8__example_8_6_2" (main := true)]
def clauseA_8_6_2 : Clause ExampleLang2 :=
  [ .pos (.eq_ rfl
      (mkF' (mkG' (Term.var 0)) (Term.var 0))
      (mkH' mkA')) ]

/-- Example 8.6.2: Clause B = {f(x, y) = h(y)}.
    Variables: x = 3, y = 4 (renamed apart from clause A). -/
@[blueprint "chap8__example_8_6_2" (main := true)]
def clauseB_8_6_2 : Clause ExampleLang2 :=
  [ .pos (.eq_ rfl
      (mkF' (Term.var 3) (Term.var 4))
      (mkH' (Term.var 4))) ]

/-- Example 8.6.2: the printed output {h(z) = h(a)}, stored literally.
    The separate left-side-root selection below gives a legal inference;
    the printed root address retains its unresolved source interpretation. -/
@[blueprint "chap8__example_8_6_2" (main := true)]
def paramodulant_8_6_2 : Clause ExampleLang2 :=
  [ .pos (.eq_ rfl (mkH' (Term.var 4)) (mkH' mkA')) ]

/-- Example 8.6.2 (companion): the stored premise copies already have
    disjoint variables, so the identity pair separates them. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleParents2_separating :
    IsSeparatingPairP (identitySubst (L := ExampleLang2)) identitySubst
      clauseB_8_6_2 clauseA_8_6_2

/-- Example 8.6.2 (companion): B supplies the donor equality and A is
    the recipient containing the selected left-side term. These are explicit
    apart parent occurrences over the displayed equality-enabled language. -/
@[blueprint "chap8__example_8_6_2"]
def exampleParents2 : ParentOccurrences ExampleLang2 where
  equalityEnabled := rfl
  sourceA := clauseB_8_6_2
  sourceB := clauseA_8_6_2
  renameA := identitySubst
  renameB := identitySubst
  separating := exampleParents2_separating

/-- Example 8.6.2: The printed clauses, root address e in A, and output
    {h(z) = h(a)}, stored as data. At the whole-literal root e lies an
    equality formula, not a term. A left-side-relative root corresponds
    to whole-literal address 1 and explains the output; the source does
    not settle this address origin. B is stored as donor and A as recipient;
    the separate address-1 selection certifies the left-side-root reading. -/
@[blueprint "chap8__example_8_6_2" (main := true)]
def paramodulationExample2 : ParamodulationResult ExampleLang2 :=
  { parents := exampleParents2,
    address := TreeAddress.root,
    result := paramodulant_8_6_2 }

/-- Example 8.6.2 (companion): x ↦ g(z), y ↦ z. Here x = 3 is B's
    first variable, y = 4 is B's second variable, and z = 0 is A's
    apart variable. The common image uses z = 0; the printed output's
    z = 4 is related by the finite variable exchange below. -/
@[blueprint "chap8__example_8_6_2"]
def exampleSubst2 : Substitution ExampleLang2 where
  support := [3, 4]
  map := fun
    | 3 => mkG' (Term.var 0)
    | 4 => Term.var 0
    | n => Term.var n
  outsideSupport := by
    intro n hn
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => simp at hn
    | 4 => simp at hn
    | n + 5 => rfl

/-- Example 8.6.2 (companion): only the two displayed domain variables
    can be changed; z remains fixed. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSubst2_finite (n : Nat) (hn : n ∉ [3, 4]) :
    exampleSubst2.apply n = Term.var n

/-- Example 8.6.2 (companion): both equation left sides have common
    image f(g(z),z), and the right sides have images h(a) and h(z). -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSubst2_images :
    termSubstAll (mkF' (mkG' (Term.var 0)) (Term.var 0)) exampleSubst2.apply =
      mkF' (mkG' (Term.var 0)) (Term.var 0) ∧
    termSubstAll (mkF' (Term.var 3) (Term.var 4)) exampleSubst2.apply =
      mkF' (mkG' (Term.var 0)) (Term.var 0) ∧
    termSubstAll (mkH' mkA') exampleSubst2.apply = mkH' mkA' ∧
    termSubstAll (mkH' (Term.var 4)) exampleSubst2.apply = mkH' (Term.var 0)

/-- Example 8.6.2 (companion): replacing A's left side at its own root
    by B's right side, then substituting, gives {h(z) = h(a)} with z = 0.
    The explicit equalityLeft root is whole-literal address 1; the printed
    root e remains stored separately. This equation calculates the left-side
    reading without selecting a correction of the printed example. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSubst2_leftSideRoot :
    (replaceLiteralAt
      (.pos (.eq_ rfl (mkF' (mkG' (Term.var 0)) (Term.var 0)) (mkH' mkA')))
      (LiteralTermAddress.equalityLeft TreeAddress.root) (mkH' (Term.var 4))).map
        (fun lit => substClause exampleSubst2 [lit]) =
      some [.pos (.eq_ rfl (mkH' (Term.var 0)) (mkH' mkA'))]

/-- Example 8.6.2 (companion): exchange variables 0 and 4, fixing every
    other variable, to express the result with the printed output's z = 4. -/
@[blueprint "chap8__example_8_6_2"]
def exampleResultRename2 : Substitution ExampleLang2 where
  support := [0, 4]
  map := fun
    | 0 => Term.var 4
    | 4 => Term.var 0
    | n => Term.var n
  outsideSupport := by
    intro n hn
    match n with
    | 0 => simp at hn
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => simp at hn
    | n + 5 => rfl

/-- Example 8.6.2 (companion): the calculated clause and the stored printed
    clause differ only by the displayed finite exchange of variable names. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSubst2_printedRenaming :
    substClause exampleResultRename2
      [.pos (.eq_ rfl (mkH' (Term.var 0)) (mkH' mkA'))] = paramodulant_8_6_2

/-- Example 8.6.1 (companion): substitution preserves negative equality,
    substituting both sides and retaining its equality witness. -/
@[blueprint "chap8__example_8_6_1"]
theorem substLitP_negativeEquality {L : Language} (hEq : L.hasEquality = true)
    (sigma : Substitution L) (s t : Term L) :
    substLitP sigma (.neg (.eq_ hEq s t)) =
      .neg (.eq_ hEq (termSubstAll s sigma.apply) (termSubstAll t sigma.apply))

/-- Example 8.6.1 (companion): replacement in a negative equality keeps
    its negative sign and the unchanged right side. -/
@[blueprint "chap8__example_8_6_1"]
theorem replaceLiteralAt_negativeEquality {L : Language} (hEq : L.hasEquality = true)
    (s t r : Term L) (addr : TreeAddress) :
    replaceLiteralAt (.neg (.eq_ hEq s t)) (.equalityLeft addr) r =
      (replaceAt s addr r).map (fun s' => FOLiteralCore.neg (.eq_ hEq s' t))

/-- Example 8.6.1 (companion): equal positive signs do not make the
    distinct rigid predicate atoms P(a) and Q(a) unifiable. -/
@[blueprint "chap8__example_8_6_1"]
theorem distinct_predicates_not_unifiable (sigma : Substitution ExampleLang) :
    ¬ IsLiteralUnifier sigma
      [.pos (mkPredP mkA), .pos (mkPredQ mkA)]

/-- Example 8.6.1 (companion): the ground unit equality clauses have
    disjoint empty variable sets and admit the finite identity separating pair. -/
@[blueprint "chap8__example_8_6_1"]
theorem binaryEqualityUnits_separating :
    IsSeparatingPairP identitySubst identitySubst
      [FOLiteralCore.pos (.eq_ (L := ExampleLang) rfl mkA mkA)]
      [FOLiteralCore.neg (.eq_ rfl mkA mkA)]

/-- Example 8.6.1 (companion): explicit positive and negative ground equality
    parent occurrences for the singleton-pivot rule. -/
@[blueprint "chap8__example_8_6_1"]
def binaryEqualityUnits : ParentOccurrences ExampleLang where
  equalityEnabled := rfl
  sourceA := [.pos (.eq_ rfl mkA mkA)]
  sourceB := [.neg (.eq_ rfl mkA mkA)]
  renameA := identitySubst
  renameB := identitySubst
  separating := binaryEqualityUnits_separating

/-- Example 8.6.1 (companion): the opposing unit equalities resolve to the
    empty clause, using the identity MGU of the selected equality atoms. -/
@[blueprint "chap8__example_8_6_1"]
theorem binaryEqualityUnits_resolve :
    binaryResolvent binaryEqualityUnits.sourceA binaryEqualityUnits.sourceB []

/-- Example 8.6.1 (companion): opposite signs on distinct rigid predicates
    P(a) and Q(a) do not provide legal binary pivots under any substitution. -/
@[blueprint "chap8__example_8_6_1"]
theorem distinct_predicates_not_complementary (sigma : Substitution ExampleLang) :
    ¬ literalsComplementary (substLitP sigma (.pos (mkPredP mkA)))
      (substLitP sigma (.neg (mkPredQ mkA)))

/-- Example 8.6.1 (companion): the literal root is not a term occurrence. -/
@[blueprint "chap8__example_8_6_1"]
theorem decodeLiteralAddress_root {L : Language} (lit : Literal L) :
    decodeLiteralAddress lit .root = none

/-- Example 8.6.1 (companion): any predicate argument is accessible at its
    whole-literal child address, for either sign. -/
@[blueprint "chap8__example_8_6_1"]
theorem literalSubtermAt_predicateArgument {L : Language} (P : L.predSymbols)
    (args : Fin (L.predArity P) → Term L) (i : Fin (L.predArity P)) :
    literalSubtermAt (.pos (.predN P args)) (.predicateArgument (i.val + 1) .root) =
      some (args i) ∧
    literalSubtermAt (.neg (.predN P args)) (.predicateArgument (i.val + 1) .root) =
      some (args i)

/-- Example 8.6.1 (companion): replace any one predicate argument and keep
    every other argument and the literal sign unchanged. -/
@[blueprint "chap8__example_8_6_1"]
theorem replaceLiteralAt_predicateArgument {L : Language} (P : L.predSymbols)
    (args : Fin (L.predArity P) → Term L) (i : Fin (L.predArity P)) (r : Term L) :
    replaceLiteralAt (.pos (.predN P args)) (.predicateArgument (i.val + 1) .root) r =
      some (.pos (.predN P (fun j => if j.val = i.val then r else args j))) ∧
    replaceLiteralAt (.neg (.predN P args)) (.predicateArgument (i.val + 1) .root) r =
      some (.neg (.predN P (fun j => if j.val = i.val then r else args j)))

/-- Example 8.6.1 (companion): every term suffix in the right equality side
    is looked up in that side, for either literal sign. -/
@[blueprint "chap8__example_8_6_1"]
theorem literalSubtermAt_equalityRight {L : Language} (hEq : L.hasEquality = true)
    (s t : Term L) (suffix : TreeAddress) :
    literalSubtermAt (.pos (.eq_ hEq s t)) (.equalityRight suffix) = subtermAt t suffix ∧
    literalSubtermAt (.neg (.eq_ hEq s t)) (.equalityRight suffix) = subtermAt t suffix

/-- Example 8.6.1 (companion): replacement in the right side of a negative
    equality preserves its left side, equality witness, and negative sign. -/
@[blueprint "chap8__example_8_6_1"]
theorem replaceLiteralAt_negativeEquality_right {L : Language} (hEq : L.hasEquality = true)
    (s t r : Term L) (suffix : TreeAddress) :
    replaceLiteralAt (.neg (.eq_ hEq s t)) (.equalityRight suffix) r =
      (replaceAt t suffix r).map (fun t' => FOLiteralCore.neg (.eq_ hEq s t'))

/-- Example 8.6.1 (companion): argument zero is not a whole-literal child. -/
@[blueprint "chap8__example_8_6_1"]
theorem literalSubtermAt_zero_argument {L : Language} (lit : Literal L)
    (suffix : TreeAddress) : literalSubtermAt lit (.predicateArgument 0 suffix) = none

/-- Example 8.6.1 (companion): printed address 11 selects the f-subterm
    in Q(h(f(h(z),h(a)))), starting at the predicate's root. -/
@[blueprint "chap8__example_8_6_1"]
theorem example1_address_lookup :
    clauseB_8_6_1.head?.bind (fun lit =>
      decodeLiteralAddress lit paramodulationExample1.address) =
        some (.predicateArgument 1 (.child 1 .root)) ∧
    clauseB_8_6_1.head?.bind (fun lit =>
      literalSubtermAt lit (.predicateArgument 1 (.child 1 .root))) =
        some (mkF (mkH (Term.var 2)) (mkH mkA))

/-- Example 8.6.1 (companion): replacing the subtree at printed address 11
    by r gives Q(h(r)), preserving the surrounding predicate and function. -/
@[blueprint "chap8__example_8_6_1"]
theorem example1_address_replacement (r : Term ExampleLang) :
    clauseB_8_6_1.head?.bind (fun lit =>
      replaceLiteralAt lit (.predicateArgument 1 (.child 1 .root)) r) =
        some (.pos (mkPredQ (mkH r)))

/-- Regression for the reverse rule: a non-head donor a = h(a) and a
    non-head negative equality recipient rewrite h(a) to a. Both residual
    literals survive. These ground parents are already apart. -/
@[blueprint "chap8__example_8_6_1"]
theorem paramodulation_reverse_regression :
    ∃ parents : ParentOccurrences ExampleLang,
      parents.sourceA = [.pos (mkPredP mkA), .pos (.eq_ rfl mkA (mkH mkA))] ∧
      parents.sourceB = [.pos (mkPredQ mkA), .neg (.eq_ rfl (mkH mkA) mkA)] ∧
      IsParamodulant parents
        [.pos (mkPredP mkA), .neg (.eq_ rfl mkA mkA), .pos (mkPredQ mkA)]

/-- Example 8.6.1 (companion): the separately named rule-consistent
    result contains a as the second argument of g. The printed output is retained. -/
@[blueprint "chap8__example_8_6_1"]
def ruleConsistentResult1 : Clause ExampleLang :=
  [.pos (mkPredQ (mkH (mkG (mkH (Term.var 2)) mkA))),
   .pos (mkPredP (mkH (Term.var 2)))]

/-- Example 8.6.1 (companion): select A's equation and B's occurrence 11
    with the finite substitution x ↦ h(z), y ↦ a. -/
@[blueprint "chap8__example_8_6_1"]
def exampleSelection1 : ParamodulationSelection ExampleLang where
  left := mkF (Term.var 0) (mkH (Term.var 1))
  right := mkG (Term.var 0) (Term.var 1)
  recipient := .pos (mkPredQ (mkH (mkF (mkH (Term.var 2)) (mkH mkA))))
  donorRemainder := [.pos (mkPredP (Term.var 0))]
  recipientRemainder := []
  address := .predicateArgument 1 (.child 1 .root)
  orientation := .leftToRight
  sigma := exampleSubst1

/-- Example 8.6.1 (companion): the displayed finite substitution is an MGU
    of the selected donor side and recipient subterm, with contained support
    and global finite-substitution factorization. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSubst1_isMGU :
    IsMGU exampleSubst1
      [mkF (Term.var 0) (mkH (Term.var 1)), mkF (mkH (Term.var 2)) (mkH mkA)]

/-- Example 8.6.2 (companion): the separately named left-side-root result
    uses the recipient's variable z = 0. The printed z = 4 is related by the
    existing finite exchange; the printed address remains e. -/
@[blueprint "chap8__example_8_6_2"]
def leftSideRootResult2 : Clause ExampleLang2 :=
  [.pos (.eq_ rfl (mkH' (Term.var 0)) (mkH' mkA'))]

/-- Example 8.6.2 (companion): B donates its left-to-right equation to
    A's left equality side, at whole-literal address 1, using x ↦ g(z), y ↦ z. -/
@[blueprint "chap8__example_8_6_2"]
def exampleSelection2 : ParamodulationSelection ExampleLang2 where
  left := mkF' (Term.var 3) (Term.var 4)
  right := mkH' (Term.var 4)
  recipient := .pos (.eq_ rfl (mkF' (mkG' (Term.var 0)) (Term.var 0)) (mkH' mkA'))
  donorRemainder := []
  recipientRemainder := []
  address := .equalityLeft .root
  orientation := .leftToRight
  sigma := exampleSubst2

/-- Example 8.6.2 (companion): the selected donor/recipient left sides
    have the stated finite MGU, with contained support and global factorization. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSubst2_isMGU :
    IsMGU exampleSubst2
      [mkF' (Term.var 3) (Term.var 4), mkF' (mkG' (Term.var 0)) (Term.var 0)]

/-- Example 8.6.1 (companion): the chosen apart parents, address 11,
    and MGU satisfy every guard of the legal inference. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSelection1_legal : IsLegalParamodulationSelection exampleParents1 exampleSelection1

/-- Example 8.6.1 (companion): the operation substitutes the residual P
    and the replaced Q; their order is immaterial to the clause relation. -/
@[blueprint "chap8__example_8_6_1"]
theorem exampleSelection1_computes :
    paramodulant exampleSelection1 = some
      [.pos (mkPredP (mkH (Term.var 2))), .pos (mkPredQ (mkH (mkG (mkH (Term.var 2)) mkA)))]

/-- Example 8.6.1 (companion): the rule-consistent alternative is a
    paramodulant of the stored apart parents. -/
@[blueprint "chap8__example_8_6_1"]
theorem example1_ruleConsistent_isParamodulant :
    IsParamodulant paramodulationExample1.parents ruleConsistentResult1

/-- Example 8.6.1 (companion): the alternative and the printed output
    differ even as sets of literals, at the second argument of g. -/
@[blueprint "chap8__example_8_6_1"]
theorem example1_printed_obstruction :
    ¬ (∀ lit, lit ∈ ruleConsistentResult1 ↔ lit ∈ paramodulant_8_6_1)

/-- Example 8.6.2 (companion): the donor is B, the recipient is A, and
    the selected legal term address is the root of A's left equality side. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSelection2_legal : IsLegalParamodulationSelection exampleParents2 exampleSelection2

/-- Example 8.6.2 (companion): compute the separate left-side-root reading. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSelection2_computes : paramodulant exampleSelection2 = some leftSideRootResult2

/-- Example 8.6.2 (companion): the left-side-root alternative is a
    paramodulant of the stored, donor-first apart parents. -/
@[blueprint "chap8__example_8_6_2"]
theorem example2_leftSideRoot_isParamodulant :
    IsParamodulant paramodulationExample2.parents leftSideRootResult2

/-- Example 8.6.2 (companion): the printed literal-root address is not a
    term address in the selected recipient. This preserves SQ36's distinction. -/
@[blueprint "chap8__example_8_6_2"]
theorem example2_printed_address_obstruction :
    decodeLiteralAddress exampleSelection2.recipient paramodulationExample2.address = none

/-- Example 8.6.2 (companion): the legal alternative's result agrees with
    the printed data after the separately displayed finite variable exchange. -/
@[blueprint "chap8__example_8_6_2"]
theorem example2_alternative_printedRenaming :
    substClause exampleResultRename2 leftSideRootResult2 = paramodulant_8_6_2

/-- Example 8.6.2 (companion): an equivalent MGU retaining the printed
    result variable z = 4: recipient variable 0 ↦ 4 and donor variable 3 ↦ g(4).
    Variable 4 is fixed. This changes the MGU naming, not the printed address. -/
@[blueprint "chap8__example_8_6_2"]
def examplePrintedSubst2 : Substitution ExampleLang2 where
  support := [0, 3]
  map := fun
    | 0 => Term.var 4
    | 3 => mkG' (Term.var 4)
    | n => Term.var n
  outsideSupport := by
    intro n outside
    match n with
    | 0 => simp at outside
    | 1 => rfl
    | 2 => rfl
    | 3 => simp at outside
    | n + 4 => rfl

/-- Example 8.6.2 (companion): the output-naming substitution is also an
    MGU of the same selected terms, with support in their original variables. -/
@[blueprint "chap8__example_8_6_2"]
theorem examplePrintedSubst2_isMGU :
    IsMGU examplePrintedSubst2
      [mkF' (Term.var 3) (Term.var 4), mkF' (mkG' (Term.var 0)) (Term.var 0)]

/-- Example 8.6.2 (companion): the left-side-root reading with the MGU
    that retains the printed output variable. Its legal address is still 1. -/
@[blueprint "chap8__example_8_6_2"]
def examplePrintedSelection2 : ParamodulationSelection ExampleLang2 :=
  { exampleSelection2 with sigma := examplePrintedSubst2 }

/-- Example 8.6.2 (companion): this explicit address-1 selection is legal. -/
@[blueprint "chap8__example_8_6_2"]
theorem examplePrintedSelection2_legal :
    IsLegalParamodulationSelection exampleParents2 examplePrintedSelection2

/-- Example 8.6.2 (companion): the address-1 calculation yields the
    stored output exactly; it does not certify the stored root address e. -/
@[blueprint "chap8__example_8_6_2"]
theorem examplePrintedSelection2_computes :
    paramodulant examplePrintedSelection2 = some paramodulant_8_6_2

/-- Example 8.6.2 (companion): the printed output is a paramodulant under
    the separately specified left-side-root reading. SQ36's printed address
    remains distinct, as example2_printed_address_obstruction records. -/
@[blueprint "chap8__example_8_6_2"]
theorem example2_leftSideRoot_printedResult :
    IsParamodulant paramodulationExample2.parents paramodulationExample2.result

/-- Truth of a signed atom under the canonical first-order interpretation. -/
def literalHoldsCore {L : Language} (M : Structure L) (v : Assignment M) : Literal L → Prop
  | .pos atom => LCS.FirstOrder.SemanticsN.formulaEvalN M atom.toFormula v
  | .neg atom => ¬ LCS.FirstOrder.SemanticsN.formulaEvalN M atom.toFormula v

/-- Example 8.6.1 (companion): no nonempty structure satisfies every
    universally closed clause of the finite input. Empty clauses are false;
    the empty family is satisfiable. Equality, when present, is identity. -/
@[blueprint "chap8__example_8_6_1"]
def ClausesUnsatisfiable {L : Language} (S : List (Clause L)) : Prop :=
  ¬ ∃ M : Structure L, ∀ C ∈ S, ∀ v : Assignment M,
    ∃ lit ∈ C, literalHoldsCore M v lit

/-- Example 8.6.1 (companion): finite binary-plus-factoring derivability
    of an arbitrary intermediate clause, with the same explicit leaf family. -/
@[blueprint "chap8__example_8_6_1"]
def BinaryFactoringDerivation {L : Language} (S : List (Clause L)) (C : Clause L) : Prop :=
  ClauseDerivationCore S true false C

/-- Example 8.6.1 (companion): each general resolvent has a finite
    binary-plus-factoring simulation whose conclusion subsumes it. Subsumption
    uses an explicit finite substitution; it accommodates residual literals
    that coalesce during factoring. No extra leaves or inference rules occur. -/
@[attach_debt, blueprint "chap8__example_8_6_1"]
theorem general_resolution_step_simulated {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] (A B C : Clause L)
    (step : Method.IsResolvent hNoEq C A B) :
    ∃ D : Clause L, BinaryFactoringDerivation [A, B] D ∧
      ∃ sigma : Substitution L, ∀ lit ∈ D, substLitP sigma lit ∈ C

/-- Example 8.6.1 (companion): a finite well-formed general resolution
    refutation is simulated by binary resolution and factoring, with exactly
    the same allowed input family and empty-clause conclusion. -/
@[attach_debt, blueprint "chap8__example_8_6_1"]
theorem general_resolution_refutation_simulated {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] (S : List (Clause L))
    (T : Method.FOResolutionTree L hNoEq)
    (leaves : Method.FOResolutionTree.leavesFrom hNoEq T (fun C => C ∈ S))
    (legal : Method.FOResolutionTree.isWellFormed hNoEq T)
    (empty : Method.FOResolutionTree.label hNoEq T = []) :
    BinaryFactoringRefutation S

/-- Example 8.6.1 (companion): a concrete equality-free signature with
    one unary predicate P and one constant a, sufficient for the binary-only
    incompleteness witness. It has no function symbols. -/
@[blueprint "chap8__example_8_6_1"]
def binaryCounterexampleLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Unit
  predSymbols := Unit
  predArity := fun _ => 1
  hasEquality := false

/-- Example 8.6.1 (companion): the atom P(x), for a specified variable. -/
@[blueprint "chap8__example_8_6_1"]
def binaryCounterexampleAtom (x : Nat) : FOAtomCore binaryCounterexampleLang :=
  .predN () (fun _ => Term.var x)

/-- Example 8.6.1 (companion): the explicit finite counterexample
    { {P(x),P(y)}, {¬P(u),¬P(v)} }, with four distinct variable names.
    Both clauses are universally closed. Factoring admits the opposite unit
    clauses, whereas binary-only derivations retain two-literal clauses. -/
@[blueprint "chap8__example_8_6_1"]
def binaryCounterexample : List (Clause binaryCounterexampleLang) :=
  [[.pos (binaryCounterexampleAtom 0), .pos (binaryCounterexampleAtom 1)],
   [.neg (binaryCounterexampleAtom 2), .neg (binaryCounterexampleAtom 3)]]

/-- Example 8.6.1 (companion): the witness is unsatisfiable, since
    assigning all four variables the value of a forces both P(a) and ¬P(a). -/
@[blueprint "chap8__example_8_6_1"]
theorem binaryCounterexample_unsatisfiable : ClausesUnsatisfiable binaryCounterexample

/-- Example 8.6.1 (companion): binary resolution alone is incomplete,
    witnessed by this specified finite equality-free unsatisfiable input,
    independently of any search strategy. -/
@[attach_debt, blueprint "chap8__example_8_6_1"]
theorem binary_only_incomplete :
    ClausesUnsatisfiable binaryCounterexample ∧ ¬ BinaryRefutation binaryCounterexample

/-- Example 8.6.1 (companion): binary resolution together with factoring
    is refutationally complete for every finite equality-free clause family.
    No formula witness, nonempty-clause assumption or search algorithm is required. -/
@[attach_debt, blueprint "chap8__example_8_6_1"]
theorem binary_factoring_complete {L : Language} (hNoEq : L.withoutEquality)
    (S : List (Clause L)) (unsatisfiable : ClausesUnsatisfiable S) :
    BinaryFactoringRefutation S

/-- Example 8.6.2 (companion): the three-rule equality calculus is
    refutationally complete for a finite clause family S, with equality
    interpreted as identity. Its leaves belong to S, ordinary reflexivity,
    or the functional reflexivity family for positive-rank symbols occurring
    in the original S. The finite derivation uses legal binary resolution,
    factoring and either paramodulation orientation on apart parent occurrences.
    This is refutation existence, with no effective proof-search assertion. -/
@[attach_debt, blueprint "chap8__example_8_6_2"]
theorem paramodulation_complete_with_functional_reflexivity {L : Language}
    (hEq : L.hasEquality = true) (S : List (Clause L))
    (unsatisfiable : ClausesUnsatisfiable S) :
    EqualityRefutation hEq
      (S ++ [reflexivityAxiom hEq] ++ functionalReflexivityAxioms hEq S)

/-- Example 8.6.2 (companion): the same three-rule equality calculus is
    refutationally complete for every finite identity-unsatisfiable S with
    ordinary reflexivity as its only added axiom. Binary resolution, factoring
    and both paramodulation orientations on apart parents remain available.
    Every clause already in S remains an allowed leaf, including any functional
    reflexivity clauses. This asserts a finite refutation, not a search algorithm. -/
@[attach_debt, blueprint "chap8__example_8_6_2"]
theorem paramodulation_complete_with_reflexivity {L : Language}
    (hEq : L.hasEquality = true) (S : List (Clause L))
    (unsatisfiable : ClausesUnsatisfiable S) :
    EqualityRefutation hEq (S ++ [reflexivityAxiom hEq])

end LCS.FOResolution.Paramodulation
