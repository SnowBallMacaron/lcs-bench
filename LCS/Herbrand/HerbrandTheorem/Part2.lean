import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import LCS.Herbrand.HerbrandTheorem.Part1
import Attach
import LCS.Herbrand.HerbrandTheorem.Part2.ProofsStamp

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


/-- The simultaneous formula instance defined by an admissible substitution pair. -/
@[blueprint "chap7__definition_7_5_3"]
def SubstitutionPair.substitutionInstance {L : Language} (sp : SubstitutionPair L) :
    FormulaN L :=
  Substitution.applyInstance sp.subst sp.formula sp.admissible

/-- Definition 7.5.3 (counterexamples): an explicit equality-free signature
with unary f, distinct constants a=false and b=true, and a binary predicate P.
In particular it has variable-bearing atoms; no claim is made for degenerate
signatures with no such atoms. -/
@[blueprint "chap7__definition_7_5_3"]
def substitutionExampleLang : Language where
  funSymbols := Unit
  funArity := fun _ => 1
  constSymbols := Bool
  predSymbols := Unit
  predArity := fun _ => 2
  hasEquality := false













/-- Definition 7.5.3: an actual admissible finite-support substitution whose
sequential result differs from its simultaneous instance in a fixed signature. -/
@[blueprint "chap7__definition_7_5_3"]
theorem sequentialSubstitution_canDiffer :
    ∃ (sigma : Substitution substitutionExampleLang) (A : FormulaN substitutionExampleLang)
      (h : Substitution.Admissible sigma A) (xs : List Nat),
      Substitution.ExactSupportEnumeration sigma xs ∧
      Substitution.applySequential sigma A xs ≠ Substitution.applyInstance sigma A h 



















-- ===================================================================
-- Theorem 7.5.1 (required helper): newVariable
-- ===================================================================

/-- All variable indices occurring in Γ, including free occurrences and every
binder occurrence. Fresh proof-local names avoid this entire finite list. -/
@[blueprint "chap7__definition_7_5_4"]
def sourceVariableIndices {L : Language} (Γ : List (FormulaN L)) : List Nat :=
  Γ.flatMap (fun A => formulaFreeVarIndices A ++ formulaBoundVarIndices A)

/-- A finite proof-local assignment of distinct fresh variables to terms.
Only terms in the supplied domain have names; the source is the whole Γ. -/
@[blueprint "chap7__definition_7_5_4"]
structure FreshTermNames {L : Language} (Γ : List (FormulaN L))
    (terms : List (Term (validitySkolemLanguage Γ))) : Type where
  name : (t : Term (validitySkolemLanguage Γ)) → t ∈ terms → Nat
  injective : ∀ t u (ht : t ∈ terms) (hu : u ∈ terms),
    name t ht = name u hu → t = u
  fresh : ∀ t (ht : t ∈ terms) x, x ∈ sourceVariableIndices Γ → name t ht ≠ x



/-- The name of a term in a finite proof-local domain. No value is supplied
for a term outside that domain. -/
@[blueprint "chap7__definition_7_5_4"]
def newVariable {L : Language} {Γ : List (FormulaN L)}
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms) (t : Term (validitySkolemLanguage Γ))
    (ht : t ∈ terms) : Nat := names.name t ht





/-- All substituted universal-occurrence terms requested by this σ-matrix.
The list includes vacuous universals even when their terms do not occur in HT. -/
@[blueprint "chap7__definition_7_5_4"]
def sigmaMatrixRequiredTerms {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ)) :
    List (Term (validitySkolemLanguage Γ)) :=
  let prefix_ := prenexPrefix (Γ.get j)
  (List.ofFn (fun p : Fin prefix_.length => p)).flatMap fun p =>
    match h : (prefix_.get p).1 with
    | .universal => [Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)]
    | .existential => []

/-- Every actual universal position contributes its required term. -/
@[blueprint "chap7__definition_7_5_4"]
theorem sigmaMatrixTerm_mem {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (p : Fin (prenexPrefix (Γ.get j)).length)
    (h : ((prenexPrefix (Γ.get j)).get p).1 = .universal) :
    Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩) ∈
      sigmaMatrixRequiredTerms sd j sigma 

/-- The finite naming table covers every term used by this σ-matrix.
One shared table may cover the requirements of many proof-local pairs. -/
@[blueprint "chap7__definition_7_5_4"]
def SigmaMatrixNamesCover {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (_names : FreshTermNames Γ terms) : Prop :=
  ∀ t, t ∈ sigmaMatrixRequiredTerms sd j sigma → t ∈ terms







-- ===================================================================
-- Theorem 7.5.1 (required helper): sigmaMatrix
-- ===================================================================

/-- Definition 7.5.4: stages of the σ-matrix for the fixed source sentence.
Stage zero replaces every universal variable in the original embedded matrix
by its proof-local name. Stage k+1 is obtained from stage k by restoring the
binder at original outermost-first position n-(k+1): an existential wraps the
previous stage, and a universal replaces its fresh name by the original variable
before wrapping it. Every Skolem term uses the original ordered existential
dependencies, allocation and naming table. The source stages are 0 through n;
the total Nat-indexed function retains stage n at larger indices. -/
@[blueprint "chap7__definition_7_5_4" (main := true)]
def sigmaMatrix {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) (i : Nat) :
    FormulaN (validitySkolemLanguage Γ) :=
  let prefix_ := prenexPrefix (Γ.get j)
  let mat := liftValidityFormula Γ (prenexMatrix (Γ.get j))
  let base := (List.ofFn (fun p : Fin prefix_.length => p)).foldl (fun body p =>
    match h : (prefix_.get p).1 with
    | .universal =>
      let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
      let v := newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h))
      formulaSubstN body (.var v) (prefix_.get p).2
    | .existential => body) mat
  let rec stage : Nat → FormulaN (validitySkolemLanguage Γ)
    | 0 => base
    | k + 1 =>
      let previous := stage k
      if hk : k < prefix_.length then
        let p : Fin prefix_.length := ⟨prefix_.length - (k + 1), by omega⟩
        match h : (prefix_.get p).1 with
        | .universal =>
          let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
          let v := newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h))
          .all (prefix_.get p).2 (formulaSubstN previous (.var (prefix_.get p).2) v)
        | .existential => .ex (prefix_.get p).2 previous
      else previous
  stage i

/-- Definition 7.5.4: each successor stage uses the preceding stage of the
same original sentence. The restored quantifier is the next one counted from
the inner end, and universal dependencies are still read at its original position. -/
@[blueprint "chap7__definition_7_5_4"]
theorem sigmaMatrix_succ {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names)
    (i : Nat) (hi : i < (prenexPrefix (Γ.get j)).length) :
    sigmaMatrix sd j sigma names hCover (i + 1) =
      let prefix_ := prenexPrefix (Γ.get j)
      let p : Fin prefix_.length := ⟨prefix_.length - (i + 1), Nat.sub_lt (Nat.zero_lt_of_lt hi) (Nat.succ_pos i)⟩
      match h : (prefix_.get p).1 with
      | .universal =>
        let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
        let v := newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h))
        .all (prefix_.get p).2
          (formulaSubstN (sigmaMatrix sd j sigma names hCover i) (.var (prefix_.get p).2) v)
      | .existential => .ex (prefix_.get p).2 (sigmaMatrix sd j sigma names hCover i) 

-- ===================================================================
-- Lemma 7.5.1 (required helper): universalClosure
-- ===================================================================

/-- Lemma 7.5.1 (required helper): Constructs the universal closure of a formula A by wrapping universal quantifiers forall y_1 ... forall y_n around A, where the list of variables [y_1, ..., y_n] is given explicitly. universalClosure A [y_1, ..., y_n] = forall y_1 (forall y_2 (... (forall y_n A) ...)). -/
@[blueprint "chap7__lemma_7_5_1"]
def universalClosure {L : Language}
    (A : FormulaN L) (vars : List Nat) : FormulaN L :=
  vars.foldr (fun v body => FormulaN.all v body) A

-- ===================================================================
-- Lemma 7.5.1 (helper): folkProvable_allRight
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (helper): folkProvable_allLeft_cut
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (helper): universalClosure_iff_folkProvable
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (LK variant): universal_closure_provability_iff_LK
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1 (LKe variant): universal_closure_provability_iff_LKe
-- ===================================================================



-- ===================================================================
-- Lemma 7.5.1: lemma_7_5_1
-- ===================================================================

/-- Lemma 7.5.1: Let A be a rectified formula, and let FV(A) = {y_1, ..., y_n} be its set of free variables. The sequent -> A is (LK or LKe)-provable iff the sequent -> forall y_1 ... forall y_n A is (LK or LKe)-provable. This is the textbook's unified "(LK or LK_e) provable" statement. The first conjunct gives the LK reading (§6.2, without equality); the second gives the LKe reading (§6.3, with equality). STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded by `hRect`. -/
@[blueprint "chap7__lemma_7_5_1" (main := true)]
theorem lemma_7_5_1 {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) :
    (∀ (_hNoEq : L.withoutEquality),
       folkProvable (Sequent.mk [] [A]) ↔
       folkProvable (Sequent.mk [] [universalClosure A fvs])) ∧
    (lkeProvable (Sequent.mk [] [A]) ↔
     lkeProvable (Sequent.mk [] [universalClosure A fvs])) 

-- ===================================================================
-- Section 7.5.1: reducing a nonempty sequent to one disjunction
-- ===================================================================

/-- The ordered, right-associated disjunction of a head formula and a tail.
A singleton is its sole formula; the head supplies the nonempty base case. -/
@[blueprint "chap7__lemma_7_5_1"]
def nonemptyDisjunction {L : Language} (A : FormulaN L) :
    List (FormulaN L) → FormulaN L
  | [] => A
  | B :: rest => .disj A (nonemptyDisjunction B rest)

/-- The §7.5.1 disjunction of a nonempty sequent: negate every antecedent,
then append the unchanged succedent, retaining order and repetitions and
associating disjunctions to the right. Either side may be empty; the two sides
cannot both be empty. No new symbol or quantifier is introduced. -/
@[blueprint "chap7__lemma_7_5_1"]
def sequentDisjunction {L : Language} :
    (s : Sequent L) → s.antecedent ++ s.succedent ≠ [] → FormulaN L
  | ⟨[], []⟩, h => False.elim (h rfl)
  | ⟨[], B :: rest⟩, _ => nonemptyDisjunction B rest
  | ⟨A :: rest, delta⟩, _ =>
      nonemptyDisjunction (.neg A) (rest.map FormulaN.neg ++ delta)

/-- Section 7.5.1: In LK over a language without equality, a nonempty
sequent is provable iff the singleton succedent containing its ordered
disjunction of negated antecedents followed by succedents is provable.
The input formulae may be open and need not be prenex or globally renamed. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem sequent_disjunction_provability_iff_LK {L : Language}
    (hL : L.withoutEquality) (s : Sequent L)
    (hNonempty : s.antecedent ++ s.succedent ≠ []) :
    folkProvable s ↔ folkProvable (Sequent.mk [] [sequentDisjunction s hNonempty]) 

/-- Section 7.5.1: In LKₑ over a language with equality, a nonempty
sequent is provable iff the singleton succedent containing the same ordered
disjunction is provable. Equality keeps its identity interpretation, and the
translation remains in the original language. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem sequent_disjunction_provability_iff_LKe {L : Language}
    (hL : L.hasEquality = true) (s : Sequent L)
    (hNonempty : s.antecedent ++ s.succedent ≠ []) :
    lkeProvable s ↔ lkeProvable (Sequent.mk [] [sequentDisjunction s hNonempty]) 

/-- The sentence associated with a nonempty sequent in §7.5.1: form its
ordered disjunction, explicitly rectify the whole formula, enumerate the free
variables of that rectified formula without repetitions, and universally close
it. An empty free-variable list contributes no quantifiers. All stages remain
in the original language. -/
@[blueprint "chap7__lemma_7_5_1"]
def associatedSentence {L : Language} (s : Sequent L)
    (hNonempty : s.antecedent ++ s.succedent ≠ []) : FormulaN L :=
  let A := rectify (sequentDisjunction s hNonempty)
  universalClosure A (formulaFreeVarIndices A).eraseDups

/-- Section 7.5.1: The explicitly associated formula is a sentence, and
LK proves the original nonempty sequent iff it proves that sentence alone
on the right. The reduction composes disjunction formation, rectification and
universal closure; no sentencehood or rectification of the input is assumed. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem sequent_sentence_reduction_LK {L : Language}
    (hL : L.withoutEquality) (s : Sequent L)
    (hNonempty : s.antecedent ++ s.succedent ≠ []) :
    FormulaN.isSentence (associatedSentence s hNonempty) ∧
    (folkProvable s ↔
      folkProvable (Sequent.mk [] [associatedSentence s hNonempty])) 

/-- Section 7.5.1: The explicitly associated formula is a sentence, and
LKₑ proves the original nonempty sequent iff it proves that sentence alone
on the right. The reduction composes disjunction formation, rectification and
universal closure; no sentencehood or rectification of the input is assumed. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem sequent_sentence_reduction_LKe {L : Language}
    (hL : L.hasEquality = true) (s : Sequent L)
    (hNonempty : s.antecedent ++ s.succedent ≠ []) :
    FormulaN.isSentence (associatedSentence s hNonempty) ∧
    (lkeProvable s ↔
      lkeProvable (Sequent.mk [] [associatedSentence s hNonempty])) 

/-- A concrete whole-sequent representative for the Herbrand convention.
The empty sequent stays empty. Every nonempty input is reduced to its associated
sentence, converted to NNF and rectified as one whole formula. The resulting
singleton has syntactically distinct entries, so syntactic contraction acts as
the identity here; no identification modulo alpha-equivalence is used. -/
@[blueprint "chap7__lemma_7_5_1"]
def herbrandConventionSuccedent {L : Language} : Sequent L → List (FormulaN L)
  | ⟨[], []⟩ => []
  | ⟨[], B :: rest⟩ =>
      [rectify (associatedSentence (Sequent.mk [] (B :: rest)) (by simp)).toNNF]
  | ⟨A :: rest, delta⟩ =>
      [rectify (associatedSentence (Sequent.mk (A :: rest) delta) (by simp)).toNNF]

/-- The §7.5.1/§7.5.4 convention reduction in LK: every original
sequent has the explicit representative with empty antecedent, syntactically
distinct closed rectified sentences, and distinct names at all binder occurrences
across the whole succedent. Provability is preserved in LK and in the original
language. All convention requirements are on the existential output. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem herbrand_sequent_convention_LK {L : Language}
    (hL : L.withoutEquality) (s : Sequent L) :
    ∃ Gamma : List (FormulaN L),
      Gamma = herbrandConventionSuccedent s ∧
      HerbrandInputConvention Gamma ∧ (∀ A ∈ Gamma, isRectified A) ∧
      (folkProvable s ↔ folkProvable (Sequent.mk [] Gamma)) 

/-- The §7.5.1/§7.5.4 convention reduction in LKₑ: every original
sequent has the explicit representative with empty antecedent, syntactically
distinct closed rectified sentences, and distinct names at all binder occurrences
across the whole succedent. Provability is preserved in LKₑ and in the original
language. All convention requirements are on the existential output. -/
@[attach_debt, blueprint "chap7__lemma_7_5_1"]
theorem herbrand_sequent_convention_LKe {L : Language}
    (hL : L.hasEquality = true) (s : Sequent L) :
    ∃ Gamma : List (FormulaN L),
      Gamma = herbrandConventionSuccedent s ∧
      HerbrandInputConvention Gamma ∧ (∀ A ∈ Gamma, isRectified A) ∧
      (lkeProvable s ↔ lkeProvable (Sequent.mk [] Gamma)) 

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
section ValidityDuality
open LCS.FirstOrder.SemanticsN



/-- The four linked equivalences in the §7.5.2 explanation of validity and
satisfiability methods. For B = ¬A, validity of A is equivalent to
unsatisfiability of B, validity of B ⇒, validity of ⇒ ¬B, and validity of ⇒ A.
Validity and satisfiability quantify over all nonempty structures and all
assignments as appropriate, including for open formulae. Both one-sided
sequents remain in L, and equality is interpreted as identity. The endpoint
uses semantic double negation. The existing validity and satisfiability
transformations retain their opposite quantifier-elimination polarities. -/
@[blueprint "chap7__theorem_7_6_1"]
theorem skolem_validity_duality {L : Language} (A B : FormulaN L)
    (hB : B = .neg A) :
    (universallyValidN A ↔ ¬ satisfiableN B) ∧
    (¬ satisfiableN B ↔ sequentValid (Sequent.mk [B] [])) ∧
    (sequentValid (Sequent.mk [B] []) ↔ sequentValid (Sequent.mk [] [.neg B])) ∧
    (sequentValid (Sequent.mk [] [.neg B]) ↔ sequentValid (Sequent.mk [] [A])) 

end ValidityDuality
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

/-- Definition 7.5.4: simultaneous renaming of the still-unrestored universal
variables among the first `remaining` positions of the original prefix. Each
image is the specified fresh name of the instantiated canonical Skolem term;
all other variables are fixed. Lookup uses the finite coverage certificate,
including vacuous occurrences, and never queries an unrestricted naming map. -/
@[blueprint "chap7__definition_7_5_4"]
def sigmaMatrixSubstitution {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) (remaining : Nat) :
    Substitution (validitySkolemLanguage Γ) :=
  let prefix_ := prenexPrefix (Γ.get j)
  fun x => (List.ofFn (fun p : Fin prefix_.length => p)).foldr (fun p image =>
    if p.val < remaining ∧ (prefix_.get p).2 = x then
      match h : (prefix_.get p).1 with
      | .universal =>
        let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
        .var (newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h)))
      | .existential => image
    else image) (.var x)

/-- Definition 7.5.4: bounded stages retain the original inner prefix and
simultaneously rename exactly the remaining outer universal variables in the
original matrix. This specifies the fresh preimage at every universal step:
restore that original occurrence, leaving the other prescribed names intact.
The assignment domain is the proof-local existential prefix, including vacuous
binders, rather than admissible substitution on the closed source sentence. -/
theorem sigmaMatrix_stage_spec {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (hSigma : Substitution.IsExistentialPrefixAssignment sigma
      (liftValidityFormula Γ (Γ.get j)))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names)
    (i : Nat) (hi : i ≤ (prenexPrefix (Γ.get j)).length) :
    sigmaMatrix sd j sigma names hCover i =
      toPrenexHelper ((prenexPrefix (Γ.get j)).drop
        ((prenexPrefix (Γ.get j)).length - i))
        (Substitution.applyFormula
          (sigmaMatrixSubstitution sd j sigma names hCover
            ((prenexPrefix (Γ.get j)).length - i))
          (liftValidityFormula Γ (prenexMatrix (Γ.get j)))) := by
  -- REPAIR(T7-55): proof pending
  sorry

/-- Definition 7.5.4: stage zero is the simultaneous substitution instance
of the original embedded matrix. Existential variables remain unchanged. -/
@[blueprint "chap7__definition_7_5_4"]
theorem sigmaMatrix_base {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (hSigma : Substitution.IsExistentialPrefixAssignment sigma
      (liftValidityFormula Γ (Γ.get j)))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) :
    sigmaMatrix sd j sigma names hCover 0 =
      Substitution.applyFormula
        (sigmaMatrixSubstitution sd j sigma names hCover (prenexPrefix (Γ.get j)).length)
        (liftValidityFormula Γ (prenexMatrix (Γ.get j))) 

/-- Full-prefix recovery on the defined-terms, proof-local assignment domain.
The equality is syntactic, in the extension of L; every original binder,
including a vacuous binder, is restored with its original variable. -/
theorem sigmaMatrix_go_full {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (hSigma : Substitution.IsExistentialPrefixAssignment sigma
      (liftValidityFormula Γ (Γ.get j)))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) :
    sigmaMatrix sd j sigma names hCover (prenexPrefix (Γ.get j)).length =
      liftValidityFormula Γ (Γ.get j) := by
  -- REPAIR(T7-55): proof pending
  sorry

/-- The full σ-matrix equals the original sentence embedded in the extension,
on the existential-prefix assignment domain with all required names defined.
The source stage is n, within 0≤i≤n. Availability outside the finite naming
domain is a source handoff, not an additional premise of Herbrand's theorem. -/
@[blueprint "chap7__definition_7_5_4"]
theorem sigmaMatrix_eq_original {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (hSigma : Substitution.IsExistentialPrefixAssignment sigma
      (liftValidityFormula Γ (Γ.get j)))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) :
    sigmaMatrix sd j sigma names hCover (prenexPrefix (Γ.get j)).length =
      liftValidityFormula Γ (Γ.get j) 

end LCS.Herbrand.HerbrandTheorem
end

