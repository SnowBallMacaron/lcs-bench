import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import LCS.Herbrand.HerbrandTheorem.SkolemFunctions
import LCS.Herbrand.HerbrandTheorem.Substitutions
import Attach
import LCS.Herbrand.HerbrandTheorem.SkolemExamples.ProofsStamp

/-! # Herbrand.HerbrandTheorem.SkolemExamples
    Chapter 7, Section 5.2: Examples 7.5.1 and 7.5.2.

    Example 7.5.1 (the Skolem symbols f, g, a of the sequent of Example
    7.3.4, with the altered proof diagrams of that proof) and Example 7.5.2
    (its functional form and the provable ground sequent obtained by
    substituting a, f(a), f(a), g(f(a)) for x, y1, y2, z1).

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
-- Example 7.5.1 (companion): SkolemSymbolEntry
-- ===================================================================

/-- Example 7.5.1 (companion structure): A Skolem symbol entry records the Skolem function symbol name, its arity, and the index of the universal quantifier it is associated with in the quantifier prefix. -/
@[blueprint "chap7__example_7_5_1"]
structure SkolemSymbolEntry (L : Language) : Type where
  /-- The index of the universal quantifier Q_i in the prefix -/
  univIndex : Nat
  /-- The name of the Skolem symbol f^A_i (as a Nat) -/
  symbolName : Nat
  /-- The arity of the Skolem function (= m_i, the number of
      existential quantifiers above Q_i) -/
  arity : Nat
  /-- The formula from which this Skolem symbol is derived -/
  sourceFormula : FormulaN L

-- ===================================================================
-- Example 7.5.1 (companion): SkolemAssignment
-- ===================================================================

/-- Example 7.5.1 (companion abbrev): A Skolem assignment is a list of Skolem symbol entries, one for each universal quantifier in the sequent's succedent formulae. -/
@[blueprint "chap7__example_7_5_1"]
abbrev SkolemAssignment (L : Language) : Type :=
  List (SkolemSymbolEntry L)

-- ===================================================================
-- Example 7.5.1 (companion def): exampleLang_7_5
-- ===================================================================

/-- Example 7.5.1 (companion type): Function symbols for the Skolem example language. The Skolem functions f (unary), g (unary), and constant a are the new symbols introduced by Skolemization. These extend the base language of Example 7.3.4. -/
@[blueprint "chap7__example_7_5_1"]
inductive SkolemExFunc_7_5 : Type where
  /-- Unary Skolem function f (for forall y) -/
  | f : SkolemExFunc_7_5
  /-- Unary Skolem function g (for forall z) -/
  | g : SkolemExFunc_7_5

/-- Example 7.5.1 (companion): Constant symbols for the Skolem
    example language: the Skolem constant a (for forall x_1). -/
@[blueprint "chap7__example_7_5_1"]
inductive SkolemExConst_7_5 : Type where
  /-- Skolem constant a (for forall x_1) -/
  | a : SkolemExConst_7_5

/-- Example 7.5.1 (companion def): The language for the Skolem function examples, extending the language of Example 7.3.4 with Skolem function symbols f, g and Skolem constant a. Uses the same binary predicates P and Q from Example 7.3.4. -/
@[blueprint "chap7__example_7_5_1"]
def exampleLang_7_5 : Language where
  funSymbols := SkolemExFunc_7_5
  funArity := fun
    | .f => 1
    | .g => 1
  constSymbols := SkolemExConst_7_5
  predSymbols := MidseqExPred
  predArity := fun _ => 2

-- ===================================================================
-- Example 7.5.1 (companion def): skolemExampleSequent_7_3_4
-- ===================================================================

/-- Example 7.5.1 (companion def): The succedent formulae from Example 7.3.4 in the base language (without Skolem symbols): [exists x forall y not P(x,y), exists y_1 forall z not Q(y_1,z), forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1))]. Variables: x=0, y=1, y_1=2, z=3, x_1=4, y_2=5, z_1=6. -/
@[blueprint "chap7__example_7_5_1"]
def skolemExampleSequent_7_3_4 : List (FormulaN midseqExLang) :=
  midsequentExampleSequent.succedent

-- ===================================================================
-- Example 7.5.1 (companion def): skolemF_forallY
-- ===================================================================

/-- Example 7.5.1 (companion def): Unary Skolem function f associated with forall y in exists x forall y not P(x,y), with arity 1 (one existential quantifier exists x above forall y). -/
@[blueprint "chap7__example_7_5_1"]
def skolemF_forallY : SkolemSymbolEntry exampleLang_7_5 where
  univIndex := 1
  symbolName := 0
  arity := 1
  sourceFormula :=
    let mkP (a b : Term exampleLang_7_5) :=
      FormulaN.predN MidseqExPred.P (vec2 a b)
    FormulaN.ex 0 (FormulaN.all 1 (FormulaN.neg (mkP (Term.var 0) (Term.var 1))))

-- ===================================================================
-- Example 7.5.1 (companion def): skolemG_forallZ
-- ===================================================================

/-- Example 7.5.1 (companion def): Unary Skolem function g associated with forall z in exists y_1 forall z not Q(y_1,z), with arity 1 (one existential quantifier exists y_1 above forall z). -/
@[blueprint "chap7__example_7_5_1"]
def skolemG_forallZ : SkolemSymbolEntry exampleLang_7_5 where
  univIndex := 1
  symbolName := 1
  arity := 1
  sourceFormula :=
    let mkQ (a b : Term exampleLang_7_5) :=
      FormulaN.predN MidseqExPred.Q (vec2 a b)
    FormulaN.ex 2 (FormulaN.all 3 (FormulaN.neg (mkQ (Term.var 2) (Term.var 3))))

-- ===================================================================
-- Example 7.5.1 (companion def): skolemA_forallX1
-- ===================================================================

/-- Example 7.5.1 (companion def): Skolem constant a associated with forall x_1 in forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1)), with arity 0 (no existential quantifiers above forall x_1, since it is the outermost quantifier). -/
@[blueprint "chap7__example_7_5_1"]
def skolemA_forallX1 : SkolemSymbolEntry exampleLang_7_5 where
  univIndex := 0
  symbolName := 2
  arity := 0
  sourceFormula :=
    let mkP (a b : Term exampleLang_7_5) :=
      FormulaN.predN MidseqExPred.P (vec2 a b)
    let mkQ (a b : Term exampleLang_7_5) :=
      FormulaN.predN MidseqExPred.Q (vec2 a b)
    FormulaN.all 4
      (FormulaN.ex 5
        (FormulaN.ex 6
          (FormulaN.conj
            (mkP (Term.var 4) (Term.var 5))
            (mkQ (Term.var 5) (Term.var 6)))))

-- ===================================================================
-- Example 7.5.1: skolemExample_7_5_1
-- ===================================================================

/-- Example 7.5.1: Concrete demonstration of Skolem function assignment for the sequent from Example 7.3.4. The assignment associates: - unary function f with forall y in exists x forall y not P(x,y) - unary function g with forall z in exists y_1 forall z not Q(y_1,z) - constant a with forall x_1 in forall x_1 exists y_2 exists z_1 (P(x_1,y_2) and Q(y_2,z_1)) -/
@[blueprint "chap7__example_7_5_1" (main := true)]
def skolemExample_7_5_1 : SkolemAssignment exampleLang_7_5 :=
  [skolemF_forallY, skolemG_forallZ, skolemA_forallX1]

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A labelled diagram retains the original indexed rule at each edge and all
transformed sequent boundaries. Stored source rules certify only the source
proof; the Boolean marks a spoiled rule in the transformed diagram. -/
inductive LKAlteredDiagram (L K : Language) where
  | leaf (boundary : Sequent K)
  | one (label : LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep L)
      (boundary : Sequent K) (spoiled : Bool) (child : LKAlteredDiagram L K)
  | two (label : LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep L)
      (boundary : Sequent K) (left right : LKAlteredDiagram L K)

namespace LKAlteredDiagram

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def mapSequent {L K : Language} (f : FormulaN L → FormulaN K)
    (s : Sequent L) : Sequent K :=
  ⟨s.antecedent.map f, s.succedent.map f⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Map every formula boundary, retaining the source rule labels and branching.
The supplied marker records newly spoiled source inferences. -/
def map {L K : Language} (f : FormulaN K → FormulaN K)
    (mark : LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep L → Bool) :
    LKAlteredDiagram L K → LKAlteredDiagram L K
  | .leaf s => .leaf (mapSequent f s)
  | .one r s b t => .one r (mapSequent f s) (b || mark r) (map f mark t)
  | .two r s t u => .two r (mapSequent f s) (map f mark t) (map f mark u)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Select a complete labelled subtree, retaining all its boundaries. -/
def subtreeAt {L K : Language} :
    LKAlteredDiagram L K → List Nat → Option (LKAlteredDiagram L K)
  | t, [] => some t
  | .one _ _ _ t, 0 :: p | .two _ _ t _, 0 :: p => subtreeAt t p
  | .two _ _ _ t, 1 :: p => subtreeAt t p
  | _, _ => none

end LKAlteredDiagram


/-- Example 7.5.1: inclusion of the original variable-only signature into the
signature with f, g, a. Empty function/constant sorts require no choices. -/
@[blueprint "chap7__example_7_5_1"]
def skolemExampleLiftTerm : Term midseqExLang → Term exampleLang_7_5
  | .var x => .var x
  | .const c => nomatch c
  | .func f _ => nomatch f

/-- Example 7.5.1: the inclusion preserves every binder and connective. -/
@[blueprint "chap7__example_7_5_1"]
def skolemExampleLiftFormula : FormulaN midseqExLang → FormulaN exampleLang_7_5
  | .predN p ts => .predN p (fun i => skolemExampleLiftTerm (ts i))
  | .eq_ h _ _ => nomatch h
  | .neg A => .neg (skolemExampleLiftFormula A)
  | .conj A B => .conj (skolemExampleLiftFormula A) (skolemExampleLiftFormula B)
  | .disj A B => .disj (skolemExampleLiftFormula A) (skolemExampleLiftFormula B)
  | .impl A B => .impl (skolemExampleLiftFormula A) (skolemExampleLiftFormula B)
  | .all x A => .all x (skolemExampleLiftFormula A)
  | .ex x A => .ex x (skolemExampleLiftFormula A)

-- ===================================================================
-- Example 7.5.2: functionalFormExample_7_5_2
-- ===================================================================

/-- Example 7.5.2: The functional form of the sequent from Example 7.3.4: [exists x not P(x, f(x)), exists y_1 not Q(y_1, g(y_1)), exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1))] obtained by applying Skolem function substitution. -/
@[blueprint "chap7__example_7_5_2"]
def functionalFormExample_7_5_2 : List (FormulaN exampleLang_7_5) :=
  let mkP (a b : Term exampleLang_7_5) :=
    FormulaN.predN MidseqExPred.P (vec2 a b)
  let mkQ (a b : Term exampleLang_7_5) :=
    FormulaN.predN MidseqExPred.Q (vec2 a b)
  -- f(x) for the first formula (Skolem function f applied to x)
  let fx := Term.func SkolemExFunc_7_5.f (fun _ => Term.var 0)
  -- g(y_1) for the second formula (Skolem function g applied to y_1)
  let gy1 := Term.func SkolemExFunc_7_5.g (fun _ => Term.var 2)
  -- a (Skolem constant) for the third formula
  let a := Term.const SkolemExConst_7_5.a
  -- Formula 1: exists x not P(x, f(x))
  let f1 := FormulaN.ex 0
    (FormulaN.neg (mkP (Term.var 0) fx))
  -- Formula 2: exists y_1 not Q(y_1, g(y_1))
  let f2 := FormulaN.ex 2
    (FormulaN.neg (mkQ (Term.var 2) gy1))
  -- Formula 3: exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1))
  let f3 := FormulaN.ex 5
    (FormulaN.ex 6
      (FormulaN.conj
        (mkP a (Term.var 5))
        (mkQ (Term.var 5) (Term.var 6))))
  [f1, f2, f3]

-- ===================================================================
-- Example 7.5.2 (companion def): groundSequentExample_7_5_2
-- ===================================================================

/-- Example 7.5.2 (companion def): The provable ground sequent obtained from the functional form by deleting remaining existential quantifiers and substituting ground terms: [not P(a, f(a)), not Q(f(a), g(f(a))), P(a, f(a)) and Q(f(a), g(f(a)))]. This demonstrates that the functional form can be instantiated to produce a propositionally provable ground sequent. -/
@[blueprint "chap7__example_7_5_2"]
def groundSequentExample_7_5_2 : List (FormulaN exampleLang_7_5) :=
  let mkP (a b : Term exampleLang_7_5) :=
    FormulaN.predN MidseqExPred.P (vec2 a b)
  let mkQ (a b : Term exampleLang_7_5) :=
    FormulaN.predN MidseqExPred.Q (vec2 a b)
  let a := Term.const SkolemExConst_7_5.a
  let fa := Term.func SkolemExFunc_7_5.f (fun _ => a)
  let gfa := Term.func SkolemExFunc_7_5.g (fun _ => fa)
  -- not P(a, f(a))
  let g1 := FormulaN.neg (mkP a fa)
  -- not Q(f(a), g(f(a)))
  let g2 := FormulaN.neg (mkQ fa gfa)
  -- P(a, f(a)) and Q(f(a), g(f(a)))
  let g3 := FormulaN.conj (mkP a fa) (mkQ fa gfa)
  [g1, g2, g3]

/-- Example 7.5.2: the original three sentences satisfy the sequent-wide
closedness and distinct-binder convention and are prenex. -/
theorem skolemExampleInput :
    HerbrandInputConvention skolemExampleSequent_7_3_4 ∧
    ∀ A ∈ skolemExampleSequent_7_3_4, isPrenex A := by
  -- REPAIR(T7-131): proof pending
  sorry

/-- Example 7.5.2: the canonical allocation of the original sequent.
Only the normalization certificates are proof fields; symbol allocation is
the occurrence-indexed construction of Definition 7.5.1. -/
@[blueprint "chap7__example_7_5_2"]
def skolemExampleAllocation : SkolemData midseqExLang skolemExampleSequent_7_3_4 :=
  mkSkolemData skolemExampleSequent_7_3_4 skolemExampleInput.1 skolemExampleInput.2

/-- Example 7.5.2: the complete universal-occurrence classification.
The first two universals have exactly one existential dependency; the third
has none. Thus the indexed signature has precisely unary f, unary g and a. -/
theorem skolemExampleAllocatedOccurrences
    (o : UniversalPrefixOccurrence skolemExampleSequent_7_3_4) :
    (o.sentence.val, o.position.val, o.dependencies) ∈
      ([(0, 1, [0]), (1, 1, [2]), (2, 0, [])] : List (Nat × Nat × List Nat)) := by
  -- REPAIR(T7-131): proof pending
  sorry

/-- Example 7.5.2: name the canonical allocated symbols in the stored example
signature. Positive-dependency occurrences are exactly the first two unary
ones; the unique zero-dependency occurrence names a. Original symbol sorts
are empty. Every unary argument is retained. -/
@[blueprint "chap7__example_7_5_2"]
def skolemExampleNameTerm :
    Term (validitySkolemLanguage skolemExampleSequent_7_3_4) → Term exampleLang_7_5
  | .var x => .var x
  | .const (.inl c) => nomatch c
  | .const (.inr _) => .const .a
  | .func (.inl f) _ => nomatch f
  | .func (.inr o) ts =>
    .func (if o.val.sentence.val = 0 then .f else .g)
      (fun _ => skolemExampleNameTerm (ts ⟨0, o.property⟩))

/-- Example 7.5.2: the symbol naming preserves predicates, formula order,
connectives and all existential binders. The allocated source is equality-free. -/
@[blueprint "chap7__example_7_5_2"]
def skolemExampleNameFormula :
    FormulaN (validitySkolemLanguage skolemExampleSequent_7_3_4) → FormulaN exampleLang_7_5
  | .predN p ts => .predN p (fun i => skolemExampleNameTerm (ts i))
  | .eq_ h _ _ => nomatch h
  | .neg A => .neg (skolemExampleNameFormula A)
  | .conj A B => .conj (skolemExampleNameFormula A) (skolemExampleNameFormula B)
  | .disj A B => .disj (skolemExampleNameFormula A) (skolemExampleNameFormula B)
  | .impl A B => .impl (skolemExampleNameFormula A) (skolemExampleNameFormula B)
  | .all x A => .all x (skolemExampleNameFormula A)
  | .ex x A => .ex x (skolemExampleNameFormula A)

/-- Example 7.5.2: equality with Definition 7.5.2's corrected allocated
transformation, under the concrete f/g/a naming of its occurrence symbols. -/
@[attach_debt, blueprint "chap7__example_7_5_2" (main := true)]
theorem functionalFormExample_eq_allocated :
    (functionalFormSequent skolemExampleAllocation).map skolemExampleNameFormula =
      functionalFormExample_7_5_2

/-- Example 7.5.1: the surviving upper proof, with the original P/Q identity
leaves, weakenings, conjunction, Q-then-P negations and all exchanges. -/
@[blueprint "chap7__example_7_5_2"]
def skolemExampleUpperProof :
    FOLKProofTree (Sequent.mk [] groundSequentExample_7_5_2) :=
  let a : Term exampleLang_7_5 := .const .a
  let fa : Term exampleLang_7_5 := .func .f (fun _ => a)
  let gfa : Term exampleLang_7_5 := .func .g (fun _ => fa)
  let p : FormulaN exampleLang_7_5 := .predN MidseqExPred.P (vec2 a fa)
  let q : FormulaN exampleLang_7_5 := .predN MidseqExPred.Q (vec2 fa gfa)
  let pAx := FOLKProofTree.axiom_ (Sequent.mk [p] [p]) ⟨p, rfl, rfl⟩
  let qAx := FOLKProofTree.axiom_ (Sequent.mk [q] [q]) ⟨q, rfl, rfl⟩
  let left := FOLKProofTree.onePremise (.exchangeLeft [] q p [] [p])
    (.onePremise (.weakenLeft q [p] [p]) pAx)
  let right := FOLKProofTree.onePremise (.weakenLeft p [q] [q]) qAx
  let conj := FOLKProofTree.twoPremise (.andRight p q [p, q] []) left right
  let negQ := FOLKProofTree.onePremise
    (.exchangeRight [p] [] (.conj p q) (.neg q) [])
    (.onePremise (.negRight q [p] [.conj p q])
      (.onePremise (.exchangeLeft [] p q [] [.conj p q]) conj))
  .onePremise (.exchangeRight [] [] (.neg q) (.neg p) [.conj p q])
    (.onePremise (.exchangeRight [] [.neg q] (.conj p q) (.neg p) [])
      (.onePremise (.negRight p [] [.neg q, .conj p q]) negQ))

/-- Example 7.5.2: the four simultaneous assignments x↦a, y₁↦f(a),
y₂↦f(a), z₁↦g(f(a)); all other variables are fixed. The two f(a) images
belong to separate source variables 2 and 5. -/
@[blueprint "chap7__example_7_5_2"]
def skolemExampleGroundSubstitution : Substitution exampleLang_7_5 :=
  let a : Term exampleLang_7_5 := .const .a
  let fa : Term exampleLang_7_5 := .func .f (fun _ => a)
  let gfa : Term exampleLang_7_5 := .func .g (fun _ => fa)
  fun x => match x with
    | 0 => a
    | 2 => fa
    | 5 => fa
    | 6 => gfa
    | y => .var y

/-- Example 7.5.2: erase precisely the displayed existential prefixes, then
apply the four displayed assignments simultaneously to the matrices. Formula
order, both binders of the third formula, and both occurrences of f(a) in the
assignment tuple are explicit. The ground proof is skolemExampleUpperProof. -/
@[blueprint "chap7__example_7_5_2" (main := true)]
theorem groundSequentExample_eq_substitution :
    let a : Term exampleLang_7_5 := .const .a
    let fa : Term exampleLang_7_5 := .func .f (fun _ => a)
    let gfa : Term exampleLang_7_5 := .func .g (fun _ => fa)
    functionalFormExample_7_5_2.map prenexPrefix =
      [[(.existential, 0)], [(.existential, 2)], [(.existential, 5), (.existential, 6)]] ∧
    [0, 2, 5, 6].map skolemExampleGroundSubstitution = [a, fa, fa, gfa] ∧
    (functionalFormExample_7_5_2.map prenexMatrix).map
      (Substitution.applyFormula skolemExampleGroundSubstitution) =
      groundSequentExample_7_5_2

end LCS.Herbrand.HerbrandTheorem
