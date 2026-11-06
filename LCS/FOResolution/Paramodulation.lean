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

/-- A legal computed candidate is a paramodulant of the apart parents. -/
@[blueprint "chap8__example_8_6_1"]
theorem paramodulant_isParamodulant {L : Language}
    (parents : ParentOccurrences L) (choice : ParamodulationSelection L) (result : Clause L)
    (legal : IsLegalParamodulationSelection parents choice)
    (computed : paramodulant choice = some result) : IsParamodulant parents result

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

/-- Example 8.6.2 (companion): the donor is B, the recipient is A, and
    the selected legal term address is the root of A's left equality side. -/
@[blueprint "chap8__example_8_6_2"]
theorem exampleSelection2_legal : IsLegalParamodulationSelection exampleParents2 exampleSelection2

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

end LCS.FOResolution.Paramodulation
