import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import Attach
import LCS.Herbrand.HerbrandTheorem.Part1.ProofsStamp

section
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

/-- The right-hand Herbrand sequent consists of distinct rectified sentences,
with distinct names at every binder occurrence across the sequent.
The list represents the succedent of a sequent with empty antecedent. -/
@[blueprint "chap7__definition_7_5_1"]
def HerbrandInputConvention {L : Language} (Γ : List (FormulaN L)) : Prop :=
  Γ.Nodup ∧
  (∀ A ∈ Γ, formulaFVN A = ∅) ∧
  (Γ.flatMap formulaBoundVarIndices).Nodup

/-- An occurrence in a sentence's outermost-first universal prefix, including
vacuous binders. Sentence positions distinguish occurrences across Γ. -/
@[blueprint "chap7__definition_7_5_1"]
structure UniversalPrefixOccurrence {L : Language} (Γ : List (FormulaN L)) where
  sentence : Fin Γ.length
  position : Fin (prenexPrefix (Γ.get sentence)).length
  universal : ((prenexPrefix (Γ.get sentence)).get position).1 = .universal

/-- Ordered existential binders strictly above this universal occurrence. -/
@[blueprint "chap7__definition_7_5_1"]
def UniversalPrefixOccurrence.dependencies {L : Language}
    {Γ : List (FormulaN L)} (o : UniversalPrefixOccurrence Γ) : List Nat :=
  ((prenexPrefix (Γ.get o.sentence)).take o.position.val).filterMap fun
    | (.existential, x) => some x
    | (.universal, _) => none

/-- Positive-dependency universal occurrences index the new function symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def ValiditySkolemFunction {L : Language} (Γ : List (FormulaN L)) :=
  {o : UniversalPrefixOccurrence Γ // 0 < o.dependencies.length}

/-- Zero-dependency universal occurrences index the new constant symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def ValiditySkolemConstant {L : Language} (Γ : List (FormulaN L)) :=
  {o : UniversalPrefixOccurrence Γ // o.dependencies.length = 0}

/-- Definition 7.5.1: extend all of L by disjoint families indexed by sentence
and universal occurrence. Existing symbols, ranks, predicates and equality are
preserved. New functions have positive rank; zero dependencies give constants. -/
@[blueprint "chap7__definition_7_5_1"]
def validitySkolemLanguage {L : Language} (Γ : List (FormulaN L)) : Language where
  funSymbols := Sum L.funSymbols (ValiditySkolemFunction Γ)
  funArity := fun
    | .inl f => L.funArity f
    | .inr o => o.val.dependencies.length
  constSymbols := Sum L.constSymbols (ValiditySkolemConstant Γ)
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Definition 7.5.1: allocation on a normalized prenex input sequent.
The indexed extension and its symbol assignments are determined by Γ;
there is one new symbol per universal occurrence, even for a vacuous binder. -/
@[blueprint "chap7__definition_7_5_1" (main := true)]
structure ValiditySkolemAllocation {L : Language} (Γ : List (FormulaN L)) : Type where
  inputConvention : HerbrandInputConvention Γ
  prenex : ∀ A ∈ Γ, isPrenex A

/-- The symbol associated with a universal occurrence, in the function or
constant component of the extended signature according to its dependencies. -/
@[blueprint "chap7__definition_7_5_1"]
def ValiditySkolemAllocation.symbol {L : Language} {Γ : List (FormulaN L)}
    (_allocation : ValiditySkolemAllocation Γ) (o : UniversalPrefixOccurrence Γ) :
    Sum (validitySkolemLanguage Γ).funSymbols
      (validitySkolemLanguage Γ).constSymbols :=
  if h : o.dependencies.length = 0 then
    .inr (.inr ⟨o, h⟩)
  else
    .inl (.inr ⟨o, Nat.pos_of_ne_zero h⟩)

/-- The Skolem term uses all ordered existential dependencies as arguments,
and uses the constant constructor exactly when there are no dependencies. -/
@[blueprint "chap7__definition_7_5_2"]
def ValiditySkolemAllocation.term {L : Language} {Γ : List (FormulaN L)}
    (_allocation : ValiditySkolemAllocation Γ) (o : UniversalPrefixOccurrence Γ) :
    Term (validitySkolemLanguage Γ) :=
  if h : o.dependencies.length = 0 then
    .const (.inr ⟨o, h⟩)
  else
    .func (.inr ⟨o, Nat.pos_of_ne_zero h⟩)
      (fun i => .var (o.dependencies.get i))

/-- Canonical allocation for a normalized prenex input; no symbol supply in L
is needed, since the extension contains the occurrence-indexed new symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def mkValiditySkolemAllocation {L : Language} (Γ : List (FormulaN L))
    (hΓ : HerbrandInputConvention Γ) (hPrenex : ∀ A ∈ Γ, isPrenex A) :
    ValiditySkolemAllocation Γ :=
  ⟨hΓ, hPrenex⟩



-- ===================================================================
-- Definition 7.5.1: SkolemData
-- ===================================================================

/-- Definition 7.5.1: canonical allocation for the normalized prenex sequent Γ.
Every universal occurrence indexes a distinct new function or constant in an
extension of all of L; its rank is determined by its existential dependencies. -/
@[blueprint "chap7__definition_7_5_1" (main := true)]
abbrev SkolemData (L : Language) (Γ : List (FormulaN L)) :=
  ValiditySkolemAllocation Γ

/-- A universal occurrence has a Skolem function exactly when it has positive
existential dependency count. -/
@[blueprint "chap7__definition_7_5_1"]
def SkolemData.isSkolemFunction {L : Language} {Γ : List (FormulaN L)}
    (_sd : SkolemData L Γ) (o : UniversalPrefixOccurrence Γ) : Prop :=
  0 < o.dependencies.length

/-- A universal occurrence has a Skolem constant exactly when it has no
existential dependencies. -/
@[blueprint "chap7__definition_7_5_1"]
def SkolemData.isSkolemConstant {L : Language} {Γ : List (FormulaN L)}
    (_sd : SkolemData L Γ) (o : UniversalPrefixOccurrence Γ) : Prop :=
  o.dependencies.length = 0

-- ===================================================================
-- Definition 7.5.1 (companion def): existentialCountAbove
-- ===================================================================

/-- Definition 7.5.1 (companion def): Computes m_i, the number of existential quantifiers ABOVE position i in the quantifier prefix. The prefix is given as a list of (QuantifierKind, variable) pairs from outermost to innermost. Position i is 0-indexed in the same OUTERMOST-first convention (i = 0 is the outermost quantifier, i = n-1 is the innermost). The existentials "above" position i are those at outermost-first indices 0, 1, ..., i-1, i.e., strictly closer to the root than position i. -/
@[blueprint "chap7__definition_7_5_1"]
def existentialCountAbove
    (prefix_ : List (QuantifierKind × Nat)) (i : Nat) : Nat :=
  -- Outermost-first convention: the quantifiers above position i are
  -- the first i elements of the outermost-first list. This matches
  -- the occurrence indices used by the canonical allocation and
  -- the prefix traversals in functionalForm and sigmaMatrix.
  let above := prefix_.take i
  above.filter (fun (q, _) =>
    match q with
    | .existential => true
    | .universal => false) |>.length

-- ===================================================================
-- Example 7.5.2 (arity pin): existentialCountAbove_ex_7_5_2_formula3
-- ===================================================================

/-- Ex 7.5.2 arity pin: verifies existentialCountAbove convention on formula 3
    (forall x_1 exists y_2 exists z_1 ...): the outermost universal has arity 0
    (constant). -/
@[blueprint "chap7__example_7_5_2"]
example : existentialCountAbove [(QuantifierKind.universal, 4),
    (QuantifierKind.existential, 5), (QuantifierKind.existential, 6)] 0 = 0 := by
  decide

/-- Ex 7.5.2 arity pin: verifies existentialCountAbove convention on formula 1
    (exists x forall y ...): the universal at outermost-first index 1 has
    arity 1 (one existential above). -/
@[blueprint "chap7__example_7_5_2"]
example : existentialCountAbove [(QuantifierKind.existential, 0),
    (QuantifierKind.universal, 1)] 1 = 1 := by
  decide

-- ===================================================================
-- Definition 7.5.1 (companion def): mkSkolemData
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonical Skolem data for the globally renamed input Γ. -/
def mkSkolemData {L : Language} (Γ : List (FormulaN L))
    (hΓ : HerbrandInputConvention Γ) (hPrenex : ∀ A ∈ Γ, isPrenex A) :
    SkolemData L Γ :=
  mkValiditySkolemAllocation Γ hΓ hPrenex

/-- Integrity of the source convention and prenex domain; occurrence identity,
rank and dependency order are fixed by the indexed representation. -/
@[blueprint "chap7__definition_7_5_1"]
def SkolemData.WellFormed {L : Language} {Γ : List (FormulaN L)}
    (_sd : SkolemData L Γ) : Prop :=
  HerbrandInputConvention Γ ∧ ∀ A ∈ Γ, isPrenex A

-- retained: used by LCS.Herbrand.HerbrandTheorem.Main.Part2
/-- A resolver is well formed exactly when it returns the canonical allocated
function or constant at every universal occurrence of Γ. -/
def SkolemResolverWellFormed {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ)
    (resolveSymbol : UniversalPrefixOccurrence Γ →
      Sum (validitySkolemLanguage Γ).funSymbols
        (validitySkolemLanguage Γ).constSymbols) : Prop :=
  ∀ o, resolveSymbol o = sd.symbol o

/-- Embed every original term into the validity-Skolem signature extension. -/
@[blueprint "chap7__definition_7_5_1"]
def liftValidityTerm {L : Language} (Γ : List (FormulaN L)) :
    Term L → Term (validitySkolemLanguage Γ)
  | .var x => .var x
  | .const c => .const (.inl c)
  | .func f ts => .func (.inl f) (fun i => liftValidityTerm Γ (ts i))

/-- Embed a source formula, preserving its connectives, binders and predicates. -/
@[blueprint "chap7__definition_7_5_1"]
def liftValidityFormula {L : Language} (Γ : List (FormulaN L)) :
    FormulaN L → FormulaN (validitySkolemLanguage Γ)
  | .predN P ts => .predN P (fun i => liftValidityTerm Γ (ts i))
  | .eq_ h t u => .eq_ h (liftValidityTerm Γ t) (liftValidityTerm Γ u)
  | .neg A => .neg (liftValidityFormula Γ A)
  | .conj A B => .conj (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .disj A B => .disj (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .impl A B => .impl (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .all x A => .all x (liftValidityFormula Γ A)
  | .ex x A => .ex x (liftValidityFormula Γ A)

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

end LCS.Herbrand.HerbrandTheorem
end

section
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
namespace LKAlteredDiagram

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def mapSequent {L K : Language} (f : FormulaN L → FormulaN K)
    (s : Sequent L) : Sequent K :=
  ⟨s.antecedent.map f, s.succedent.map f⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Copy every node, including exchanges and both axiom leaves. -/
def ofProof {L K : Language} (f : FormulaN L → FormulaN K) :
    {s : Sequent L} → FOLKProofTree s → LKAlteredDiagram L K
  | s, .axiom_ _ _ => .leaf (mapSequent f s)
  | s, .onePremise r t => .one (.one r) (mapSequent f s) false (ofProof f t)
  | s, .twoPremise r t u => .two (.two r) (mapSequent f s) (ofProof f t) (ofProof f u)

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
/-- Boundary lookup uses the same 0/1 addresses as the original indexed tree. -/
def boundaryAt {L K : Language} : LKAlteredDiagram L K → List Nat → Option (Sequent K)
  | .leaf s, [] | .one _ s _ _, [] | .two _ s _ _, [] => some s
  | .one _ _ _ t, 0 :: p | .two _ _ t _, 0 :: p => boundaryAt t p
  | .two _ _ _ t, 1 :: p => boundaryAt t p
  | _, _ => none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Addresses of the marked universal-right inferences. -/
def spoiledSites {L K : Language} : LKAlteredDiagram L K → List (List Nat)
  | .leaf _ => []
  | .one _ _ b t => (if b then [[]] else []) ++ t.spoiledSites.map (0 :: ·)
  | .two _ _ t u => t.spoiledSites.map (0 :: ·) ++ u.spoiledSites.map (1 :: ·)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Select the original universal-right inference using its eigenvariable. -/
def replacesEigen {L : Language} (x : Nat) :
    LCS.Herbrand.SharpenedHauptsatz.Permutability.AnyFOLKStep L → Bool
  | .one (.allRight y _ _ _ _ _ _) => y == x
  | _ => false

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Select a complete labelled subtree, retaining all its boundaries. -/
def subtreeAt {L K : Language} :
    LKAlteredDiagram L K → List Nat → Option (LKAlteredDiagram L K)
  | t, [] => some t
  | .one _ _ _ t, 0 :: p | .two _ _ t _, 0 :: p => subtreeAt t p
  | .two _ _ _ t, 1 :: p => subtreeAt t p
  | _, _ => none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A legal indexed proof realizes the entire raw diagram when boundaries,
branching, and rule constructors agree at every node and no edge is marked.
Source labels live in L; the realizing proof lives in K. -/
def Realizes {L K : Language} :
    LKAlteredDiagram L K → {s : Sequent K} → FOLKProofTree s → Prop
  | .leaf b, s, .axiom_ _ _ => b = s
  | .one (.one r) b spoiled child, s, .onePremise q t =>
    b = s ∧ spoiled = false ∧ r.ctorIdx = q.ctorIdx ∧ Realizes child t
  | .two (.two r) b left right, s, .twoPremise q t u =>
    b = s ∧ r.ctorIdx = q.ctorIdx ∧ Realizes left t ∧ Realizes right u
  | _, _, _ => False

end LKAlteredDiagram
end LCS.Herbrand.HerbrandTheorem
end

section
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.5.1: the complete original labelled proof, including the exchanges
implicit in the printed display. The existing f/g/a assignment is unchanged. -/
def skolemExampleOriginalDiagram : LKAlteredDiagram midseqExLang exampleLang_7_5 :=
  .ofProof skolemExampleLiftFormula midsequentExampleTree

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.5.1: first alteration, replacing free x₁ occurrences by a at
EVERY node. Quantified occurrences and binder labels remain in place, so the
bottom universal-right boundary is retained and marked as spoiled. -/
def skolemExampleFirstAlteration : LKAlteredDiagram midseqExLang exampleLang_7_5 :=
  skolemExampleOriginalDiagram.map (fun A => formulaSubstN A (.const .a) 4)
    (LKAlteredDiagram.replacesEigen 4)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.5.1: second alteration, replacing free y occurrences by f(a)
in the first diagram. The ∀y¬P(a,y) boundary is retained; its original
universal-right inference joins the previously spoiled bottom inference. -/
def skolemExampleSecondAlteration : LKAlteredDiagram midseqExLang exampleLang_7_5 :=
  skolemExampleFirstAlteration.map
    (fun A => formulaSubstN A (.func .f (fun _ => .const .a)) 1)
    (LKAlteredDiagram.replacesEigen 1)

/-- Example 7.5.1: the marked inferences are the actual root and depth-eight
universal-right nodes; no existential or structural step is marked. -/
theorem skolemExampleSpoiledSites :
    skolemExampleOriginalDiagram.spoiledSites = [] ∧
    skolemExampleFirstAlteration.spoiledSites = [[]] ∧
    skolemExampleSecondAlteration.spoiledSites = [[], List.replicate 8 0] := by
  -- REPAIR(T7-129): proof pending
  sorry

/-- Example 7.5.1: all three labelled diagrams retain the original end sequent,
whose three formulas are sentences. -/
theorem skolemExampleAlterationEnd :
    skolemExampleFirstAlteration.boundaryAt [] =
      skolemExampleOriginalDiagram.boundaryAt [] ∧
    skolemExampleSecondAlteration.boundaryAt [] =
      skolemExampleOriginalDiagram.boundaryAt [] := by
  -- REPAIR(T7-129): proof pending
  sorry

/-- Example 7.5.1: the two transformed midsequents at the SAME original node.
The existential binders below this boundary have not been erased or moved. -/
theorem skolemExampleAlterationMidsequents :
    let p (s t : Term exampleLang_7_5) := FormulaN.predN MidseqExPred.P (vec2 s t)
    let q (s t : Term exampleLang_7_5) := FormulaN.predN MidseqExPred.Q (vec2 s t)
    let a : Term exampleLang_7_5 := .const .a
    let fa : Term exampleLang_7_5 := .func .f (fun _ => a)
    skolemExampleFirstAlteration.boundaryAt (List.replicate 19 0) =
      some ⟨[], [.neg (p a (.var 1)), .neg (q (.var 1) (.var 3)),
        .conj (p a (.var 1)) (q (.var 1) (.var 3))]⟩ ∧
    skolemExampleSecondAlteration.boundaryAt (List.replicate 19 0) =
      some ⟨[], [.neg (p a fa), .neg (q fa (.var 3)), .conj (p a fa) (q fa (.var 3))]⟩ := by
  -- REPAIR(T7-129): proof pending
  sorry

/-- Example 7.5.1: the retained universal boundaries cannot be legal
universal-right steps: their premise principal formulas are no variable
instances of their conclusion bodies, for any proposed eigenvariable. -/
theorem skolemExampleSpoiledBoundaries :
    (∀ v : Nat, ∀ A : FormulaN exampleLang_7_5,
      (skolemExampleFirstAlteration.boundaryAt []).bind
        (fun s => s.succedent.getLast?) = some (.all 4 A) →
      (skolemExampleFirstAlteration.boundaryAt [0]).bind
        (fun s => s.succedent.getLast?) ≠ some (formulaSubstN A (.var v) 4)) ∧
    (∀ v : Nat, ∀ A : FormulaN exampleLang_7_5,
      (skolemExampleSecondAlteration.boundaryAt (List.replicate 8 0)).bind
        (fun s => s.succedent.getLast?) = some (.all 1 A) →
      (skolemExampleSecondAlteration.boundaryAt (List.replicate 9 0)).bind
        (fun s => s.succedent.getLast?) ≠ some (formulaSubstN A (.var v) 1)) := by
  -- REPAIR(T7-129): proof pending
  sorry

-- ===================================================================
-- Definition 7.5.2 (companion def): skolemTerm
-- ===================================================================

/-- Definition 7.5.2: the term allocated to the universal occurrence `o` in Γ.
Zero dependencies give `Term.const`; positive dependencies give `Term.func`
with the existential variables strictly above `o`, in outermost-first order.
The function rank and argument-vector length are both definitionally the length
of this same dependency list, including existential binders unused in the matrix. -/
@[blueprint "chap7__definition_7_5_2"]
def skolemTerm {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (o : UniversalPrefixOccurrence Γ) :
    Term (validitySkolemLanguage Γ) := sd.term o

/-- Definition 7.5.2: functional form of the selected sentence of Γ in its
allocated extension. `sd` carries `HerbrandInputConvention Γ` and prenexness.
Every step is indexed by a position in the original sentence's full prefix;
its symbol and dependencies are therefore independent of the shrinking body.
The right fold starts with the embedded matrix, substitutes the allocated term
at each universal, and reconstructs each existential. Thus all universals,
including vacuous ones, are removed and existential order is preserved.
Global binder distinctness ensures that each inserted term's existential
variables are captured only by their original enclosing existential binders. -/
@[blueprint "chap7__definition_7_5_2"]
def functionalForm {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length) :
    FormulaN (validitySkolemLanguage Γ) :=
  let prefix_ := prenexPrefix (Γ.get j)
  (List.ofFn (fun p : Fin prefix_.length => p)).foldr (fun p body =>
    match h : (prefix_.get p).1 with
    | .universal => formulaSubstN body (skolemTerm sd ⟨j, p, h⟩) (prefix_.get p).2
    | .existential => .ex (prefix_.get p).2 body)
    (liftValidityFormula Γ (prenexMatrix (Γ.get j)))

/-- Definition 7.5.2: apply the single allocation indexed by Γ to every source
sentence, in sequent order. All results share `validitySkolemLanguage Γ`, so
symbols from different sentences retain their distinct occurrence identities.
For an empty input sequent, the resulting list is empty. -/
@[blueprint "chap7__definition_7_5_2" (main := true)]
def functionalFormSequent {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) : List (FormulaN (validitySkolemLanguage Γ)) :=
  List.ofFn (functionalForm sd)

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.5.1: the third alteration replaces free z by g(f(a)) at every
node of the second diagram, retaining and marking the ∀z¬Q(f(a),z) edge. -/
def skolemExampleThirdAlteration : LKAlteredDiagram midseqExLang exampleLang_7_5 :=
  skolemExampleSecondAlteration.map
    (fun A => formulaSubstN A (.func .g (fun _ => .func .f (fun _ => .const .a))) 3)
    (LKAlteredDiagram.replacesEigen 3)

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

/-- Example 7.5.1: all three universal-right edges are spoiled, while the
entire subtree above the original midsequent is realized by the displayed
legal propositional/structural proof. In the final diagram each retained
universal body fails the variable-instance test at its actual premise. -/
theorem skolemExampleThirdAlterationSpec :
    skolemExampleThirdAlteration.spoiledSites =
      [[], List.replicate 8 0, List.replicate 15 0] ∧
    skolemExampleThirdAlteration.boundaryAt [] =
      skolemExampleOriginalDiagram.boundaryAt [] ∧
    (∀ d x, (d, x) ∈ ([(0, 4), (8, 1), (15, 3)] : List (Nat × Nat)) →
      ∃ A : FormulaN exampleLang_7_5,
        ((skolemExampleThirdAlteration.boundaryAt (List.replicate d 0)).bind
          (fun s => s.succedent.getLast?)) = some (.all x A) ∧
        ∀ v : Nat,
          ((skolemExampleThirdAlteration.boundaryAt (List.replicate (d + 1) 0)).bind
            (fun s => s.succedent.getLast?)) ≠ some (formulaSubstN A (.var v) x)) ∧
    (∃ upper, skolemExampleThirdAlteration.subtreeAt (List.replicate 19 0) = some upper ∧
      upper.Realizes skolemExampleUpperProof) ∧
    AllRulesPropStructInessentialLK skolemExampleUpperProof ∧
    skolemExampleUpperProof.isCutFree := by
  -- REPAIR(T7-130): proof pending
  sorry

-- ===================================================================
-- Definition 7.5.3: Substitution
-- ===================================================================

/-- Definition 7.5.3: A substitution function (for short, a substitution) is any function sigma : V -> TERM_L assigning terms to the variables in V. Using Nat for variables, this is simply a function Nat -> Term L. -/
@[blueprint "chap7__definition_7_5_3" (main := true)]
abbrev Substitution (L : Language) : Type := Nat → Term L

end LCS.Herbrand.HerbrandTheorem
end

section
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Restrict a substitution to the variables actually free in the recursive
child formula; outside that finite syntactic list the map is the identity. -/
def restrictToFormula {L : Language} (sigma : Substitution L) (A : FormulaN L) :
    Substitution L :=
  fun x => if x ∈ formulaFreeVarIndices A then sigma x else .var x

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

/-- On the source domain, guarded recursion computes the raw simultaneous
instance. Support restriction only discards assignments irrelevant to a child. -/
theorem applyInstance_eq_applyFormula {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (h : Admissible sigma A) :
    applyInstance sigma A h = applyFormula sigma A := by
  -- REPAIR(T7-52): proof pending
  sorry

/-- The distinct proof-local domain for assignments to existential-prefix
variables, including vacuous binders. It does not require support to lie in the
free variables of the closed prenex sentence; later matrix use restricts it. -/
@[blueprint "chap7__definition_7_5_4"]
def IsExistentialPrefixAssignment {L : Language}
    (sigma : Substitution L) (A : FormulaN L) : Prop :=
  isPrenex A ∧ hasFiniteSupport sigma ∧
    ∀ x, support sigma x → (QuantifierKind.existential, x) ∈ prenexPrefix A

/-- A list enumerates exactly the changed variables, once each. Empty support
has the empty enumeration; enumeration order is not fixed. -/
@[blueprint "chap7__definition_7_5_3"]
def ExactSupportEnumeration {L : Language} (sigma : Substitution L)
    (xs : List Nat) : Prop :=
  xs.Nodup ∧ ∀ x, x ∈ xs ↔ support sigma x

/-- Every support variable is absent from every supported image. The two
support indices are independent, so cross-image dependencies are excluded. -/
@[blueprint "chap7__definition_7_5_3"]
def SupportImagesDisjoint {L : Language} (sigma : Substitution L) : Prop :=
  ∀ x, support sigma x → ∀ y, support sigma y → x ∉ termFV (sigma y)

/-- Raw left-to-right iteration of the existing single-variable formula
substitution. Each step uses the original image sigma x. -/
@[blueprint "chap7__definition_7_5_3"]
def applySequential {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (xs : List Nat) : FormulaN L :=
  xs.foldl (fun B x => formulaSubstN B (sigma x) x) A

/-- A ground substitution has finite support and closed images on that support.
Variables outside the support retain their variable terms; empty support is
allowed. No restriction to a particular Herbrand signature is imposed. -/
@[blueprint "chap7__definition_7_5_3"]
def IsGround {L : Language} (sigma : Substitution L) : Prop :=
  hasFiniteSupport sigma ∧ ∀ x, support sigma x → termFV (sigma x) = ∅

/-- Under the outer formula admissibility conditions and full support/image
disjointness, an exact support enumeration gives both the raw simultaneous
formula substitution and the guarded source instance. -/
@[attach_debt, blueprint "chap7__definition_7_5_3"]
theorem applySequential_eq_simultaneous {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (hA : Admissible sigma A) (xs : List Nat)
    (hxs : ExactSupportEnumeration sigma xs) (hDisjoint : SupportImagesDisjoint sigma) :
    applySequential sigma A xs = applyFormula sigma A ∧
    applySequential sigma A xs = applyInstance sigma A hA 

/-- Every permutation of an exact support enumeration gives the same sequential
formula instance on the adopted admissible domain. -/
@[blueprint "chap7__definition_7_5_3"]
theorem applySequential_perm {L : Language} (sigma : Substitution L)
    (A : FormulaN L) (hA : Admissible sigma A) (xs ys : List Nat)
    (hxs : ExactSupportEnumeration sigma xs) (hPerm : xs.Perm ys)
    (hDisjoint : SupportImagesDisjoint sigma) :
    applySequential sigma A xs = applySequential sigma A ys 

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Closed support images imply the full two-index disjointness condition. -/
theorem IsGround.supportImagesDisjoint {L : Language} {sigma : Substitution L}
    (h : IsGround sigma) : SupportImagesDisjoint sigma := by
  intro x hx y hy
  rw [h.2 y hy]
  exact fun impossible => impossible

/-- The sequential/simultaneous equalities for ground substitutions, retaining
all outer admissibility conditions on the formula. -/
@[blueprint "chap7__definition_7_5_3"]
theorem IsGround.applySequential_eq_simultaneous {L : Language} {sigma : Substitution L}
    (h : IsGround sigma) (A : FormulaN L) (hA : Admissible sigma A)
    (xs : List Nat) (hxs : ExactSupportEnumeration sigma xs) :
    applySequential sigma A xs = applyFormula sigma A ∧
    applySequential sigma A xs = applyInstance sigma A hA 

/-- Ground substitutions are independent of the chosen support permutation. -/
@[blueprint "chap7__definition_7_5_3"]
theorem IsGround.applySequential_perm {L : Language} {sigma : Substitution L}
    (h : IsGround sigma) (A : FormulaN L) (hA : Admissible sigma A)
    (xs ys : List Nat) (hxs : ExactSupportEnumeration sigma xs) (hPerm : xs.Perm ys) :
    applySequential sigma A xs = applySequential sigma A ys 



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Restricting a ground assignment to a matrix's free variables preserves
its general ground-substitution property; the matrix may discard vacuous entries. -/
theorem IsGround.restrictToFormula {L : Language} {sigma : Substitution L}
    (h : IsGround sigma) (A : FormulaN L) : IsGround (restrictToFormula sigma A) := by
  have hs : ∀ x, support (Substitution.restrictToFormula sigma A) x →
      support sigma x ∧ x ∈ formulaFreeVarIndices A := by
    intro x hx
    by_cases hm : x ∈ formulaFreeVarIndices A
    · exact ⟨by simpa [support, Substitution.restrictToFormula, hm] using hx, hm⟩
    · simp [support, Substitution.restrictToFormula, hm] at hx
  refine ⟨Set.Finite.subset h.1 (fun x hx => (hs x hx).1), ?_⟩
  intro x hx
  have hh := hs x hx
  simpa [Substitution.restrictToFormula, hh.2] using h.2 x hh.1

end Substitution
end LCS.Herbrand.HerbrandTheorem
end

