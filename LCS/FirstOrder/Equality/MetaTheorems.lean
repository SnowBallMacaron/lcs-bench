import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Completeness.MetaTheorems
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import Attach
import LCS.FirstOrder.Equality.MetaTheorems.ProofsStamp

/-! # FirstOrder.Equality.MetaTheorems
    Formalization of Chapter 5, Sections 5.6.6-5.6.8.
    Lowenheim-Skolem, compactness, model existence theorems,
    maximal consistent sets, and nonstandard models of arithmetic
    (languages with equality).
-/

namespace LCS.FirstOrder.Equality.MetaTheorems

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax (peanoLanguage ArithFunc ArithConst)
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables (formulaFVN)
open LCS.FirstOrder.Semantics (zeroTerm mkSucc mkPlus mkTimes peanoNatStructure)
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Completeness.MetaTheorems
open Classical

-- ===================================================================
-- Theorem 5.6.4 (companion def): isConsistentSetEq
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- No finite list of members of Gamma proves the empty succedent in G_=. -/
def isConsistentSetEqEmptySucc {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L)) : Prop :=
  ∀ (cs : List (FormulaN L)),
    (∀ c, c ∈ cs → c ∈ Gamma) →
    ¬ (sequentProvableEq hL (Sequent.mk cs []))

/-- G_=-consistency is equivalent to unprovability of the empty succedent
from finite subsets. Equality supplies formulas even when predicates are absent. -/
theorem isConsistentSetEq_iff_emptySucc {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L)) :
    isConsistentSetEq hL Gamma ↔ isConsistentSetEqEmptySucc hL Gamma := by
  -- REPAIR(T26): proof pending
  sorry

-- ===================================================================
-- Lemma 5.6.5 (companion def): isMaximalConsistentSetEq
-- ===================================================================

/-- Lemma 5.6.5 (companion): A set Delta of normalized formulae is
maximally consistent with respect to G_= iff it is consistent
(isConsistentSetEq Delta) and for every consistent set Sigma, if
Delta is a subset of Sigma then Delta equals Sigma. -/
@[blueprint "chap5__lemma_5_6_5"]
def isMaximalConsistentSetEq {L : Language} (hL : L.hasEquality = true)
    (Delta : Set (FormulaN L)) : Prop :=
  isConsistentSetEq hL Delta ∧
  ∀ (Sigma : Set (FormulaN L)),
    isConsistentSetEq hL Sigma → Set.subset Delta Sigma → Delta = Sigma

-- ===================================================================
-- Example 5.6.3 (companion def): paSuccZeroAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x not(S(x) doteq 0):
zero is not the successor of any number. -/
@[blueprint "chap5__example_5_3_2"]
def paSuccZeroAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0
    (FormulaN.neg
      (FormulaN.eq_ rfl (mkSucc (Term.var 0)) zeroTerm))

-- ===================================================================
-- Example 5.6.3 (companion def): paSuccInjectiveAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x forall y
(S(x) doteq S(y) supset x doteq y): successor is injective. -/
@[blueprint "chap5__example_5_3_2"]
def paSuccInjectiveAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.impl
      (FormulaN.eq_ rfl (mkSucc (Term.var 0)) (mkSucc (Term.var 1)))
      (FormulaN.eq_ rfl (Term.var 0) (Term.var 1))))

-- ===================================================================
-- Example 5.6.3 (companion def): paAddZeroAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x (x+0 doteq x):
base case of addition. -/
@[blueprint "chap5__example_5_3_2"]
def paAddZeroAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0
    (FormulaN.eq_ rfl (mkPlus (Term.var 0) zeroTerm) (Term.var 0))

-- ===================================================================
-- Example 5.6.3 (companion def): paAddSuccAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x forall y
(x+S(y) doteq S(x+y)): successor step of addition. -/
@[blueprint "chap5__example_5_3_2"]
def paAddSuccAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.eq_ rfl
      (mkPlus (Term.var 0) (mkSucc (Term.var 1)))
      (mkSucc (mkPlus (Term.var 0) (Term.var 1)))))

-- ===================================================================
-- Example 5.6.3 (companion def): paMulZeroAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x (x*0 doteq 0):
base case of multiplication. -/
@[blueprint "chap5__example_5_3_2"]
def paMulZeroAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0
    (FormulaN.eq_ rfl (mkTimes (Term.var 0) zeroTerm) zeroTerm)

-- ===================================================================
-- Example 5.6.3 (companion def): paMulSuccAxiom
-- ===================================================================

/-- Example 5.6.3 (companion): The axiom forall x forall y
(x*S(y) doteq x*y+x): successor step of multiplication. -/
@[blueprint "chap5__example_5_3_2"]
def paMulSuccAxiom : FormulaN peanoLanguage :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.eq_ rfl
      (mkTimes (Term.var 0) (mkSucc (Term.var 1)))
      (mkPlus (mkTimes (Term.var 0) (Term.var 1)) (Term.var 0))))

-- ===================================================================
-- Example 5.6.3 (companion def): numeral
-- ===================================================================

/-- Example 5.6.3 (companion): The numeral n as a term:
S(S(...(0))) with n occurrences of S. numeral 0 = 0,
numeral (n+1) = S(numeral n). -/
@[blueprint "chap5__example_5_6_3"]
def numeral : Nat → Term peanoLanguage
  | 0 => zeroTerm
  | n + 1 => mkSucc (numeral n)

-- ===================================================================
-- Example 5.6.3 (companion def): paInductionSchema
-- ===================================================================

/-- Example 5.6.3 (companion): Forms
(A(0) ∧ ∀x(A(x) ⊃ A(S(x)))) ⊃ ∀y A(y), with x = 0 and y = 1.
The set `peanoArithAxioms` admits these instances when FV(A) = {0}
and variable 1 is free for variable 0 in A. -/
@[blueprint "chap5__example_5_3_2"]
def paInductionSchema (A : FormulaN peanoLanguage) :
    FormulaN peanoLanguage :=
  let a0 := formulaSubstN A zeroTerm 0
  let aSx := formulaSubstN A (mkSucc (Term.var 0)) 0
  let aY := formulaSubstN A (Term.var 1) 0
  FormulaN.impl
    (FormulaN.conj
      a0
      (FormulaN.all 0 (FormulaN.impl A aSx)))
    (FormulaN.all 1 aY)

-- ===================================================================
-- Example 5.6.3: peanoArithAxioms
-- ===================================================================

/-- Example 5.6.3: The set A_P consists of the six Peano axioms for successor,
addition, and multiplication, together with the induction instances
`paInductionSchema B` for FV(B) = {0} and variable 1 free for variable 0 in B. -/
@[blueprint "chap5__example_5_3_2"]
def peanoArithAxioms : Set (FormulaN peanoLanguage) :=
  fun A =>
    A = paSuccZeroAxiom ∨
    A = paSuccInjectiveAxiom ∨
    A = paAddZeroAxiom ∨
    A = paAddSuccAxiom ∨
    A = paMulZeroAxiom ∨
    A = paMulSuccAxiom ∨
    (∃ B : FormulaN peanoLanguage,
      formulaFVN B = Set.singleton 0 ∧
      isFreeForN (Term.var 1) 0 B ∧ A = paInductionSchema B)

-- ===================================================================
-- Example 5.6.3 (companion def): expandedArithLanguage
-- ===================================================================

/-- Example 5.6.3 (companion): The expansion L' of the language of
predicate-free arithmetic L obtained by adding a new constant symbol c. The constant
symbols are the Sum type (ArithConst + Unit), where the Unit summand
represents c. -/
@[blueprint "chap5__example_5_6_3"]
def expandedArithLanguage : Language where
  funSymbols := ArithFunc
  funArity := fun
    | .succ  => 1
    | .plus  => 2
    | .times => 2
  constSymbols := ArithConst ⊕ Unit
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := true

-- ===================================================================
-- Example 5.6.3 (companion def): newConstantC
-- ===================================================================

/-- Example 5.6.3 (companion): The constant term for the new constant
c in the expanded language L'. -/
@[blueprint "chap5__example_5_6_3"]
def newConstantC : Term expandedArithLanguage :=
  Term.const (Sum.inr ())

-- ===================================================================
-- Example 5.6.3 (companion def): numeralExpanded
-- (helper to lift numerals into the expanded language)
-- ===================================================================

/-- Example 5.6.3 (companion): The numeral n as a term in the expanded
arithmetic language L'. Uses the original zero constant (Sum.inl
ArithConst.zero) and the successor function. -/
@[blueprint "chap5__example_5_6_3"]
def numeralExpanded : Nat → Term expandedArithLanguage
  | 0 => Term.const (Sum.inl ArithConst.zero)
  | n + 1 =>
    Term.func ArithFunc.succ (fun _ => numeralExpanded n)

-- ===================================================================
-- Example 5.6.3 (companion def): inequationSet
-- ===================================================================

/-- Example 5.6.3 (companion): The set
I = {not(0 doteq c), not(1 doteq c), ..., not(n doteq c), ...}.
A formula is in I iff there exists n : Nat such that the formula
equals not(numeral_expanded n doteq c). -/
@[blueprint "chap5__example_5_6_3"]
def inequationSet : Set (FormulaN expandedArithLanguage) :=
  fun A => ∃ n : Nat,
    A = FormulaN.neg (FormulaN.eq_ rfl (numeralExpanded n) newConstantC)

-- ===================================================================
-- Example 5.6.3 (companion def): liftArithFormula
-- (helper to embed peanoLanguage formulae into expandedArithLanguage)
-- ===================================================================

/-- Example 5.6.3 (companion): Lifts a term from peanoLanguage to
expandedArithLanguage by mapping ArithConst to Sum.inl ArithConst. -/
@[blueprint "chap5__example_5_6_3"]
def liftArithTerm : Term peanoLanguage → Term expandedArithLanguage
  | Term.var x => Term.var x
  | Term.const c => Term.const (Sum.inl c)
  | Term.func f ts => Term.func f (fun i => liftArithTerm (ts i))

/-- Example 5.6.3 (companion): Lifts a formula from peanoLanguage to
expandedArithLanguage by lifting all embedded terms. -/
@[blueprint "chap5__example_5_6_3"]
def liftArithFormula :
    FormulaN peanoLanguage → FormulaN expandedArithLanguage
  | FormulaN.predN P _ => Empty.elim P
  | FormulaN.eq_ _ t1 t2 =>
    FormulaN.eq_ rfl (liftArithTerm t1) (liftArithTerm t2)
  | FormulaN.conj A B =>
    FormulaN.conj (liftArithFormula A) (liftArithFormula B)
  | FormulaN.disj A B =>
    FormulaN.disj (liftArithFormula A) (liftArithFormula B)
  | FormulaN.impl A B =>
    FormulaN.impl (liftArithFormula A) (liftArithFormula B)
  | FormulaN.neg A =>
    FormulaN.neg (liftArithFormula A)
  | FormulaN.all x A =>
    FormulaN.all x (liftArithFormula A)
  | FormulaN.ex x A =>
    FormulaN.ex x (liftArithFormula A)

-- ===================================================================
-- Example 5.6.3 (companion def): gammaNonstandard
-- ===================================================================

/-- Example 5.6.3 (companion): The set Gamma = A_P union I, where A_P
is the set of Peano axioms (lifted to the expanded language) and I is
the set of inequation formulae. -/
@[blueprint "chap5__example_5_6_3"]
def gammaNonstandard : Set (FormulaN expandedArithLanguage) :=
  Set.union
    (fun A => ∃ B : FormulaN peanoLanguage, B ∈ peanoArithAxioms ∧ A = liftArithFormula B)
    inequationSet

-- ===================================================================
-- Example 5.6.3 (companion def): StructureIsomorphism
-- ===================================================================

/-- Example 5.6.3 (companion): An isomorphism of predicate-free arithmetic
structures M and N: a bijection of their carriers preserving zero, successor,
addition, and multiplication. -/
@[blueprint "chap5__example_5_6_3"]
structure StructureIsomorphism
    (M N : Structure peanoLanguage) : Type where
  /-- The underlying bijection from M.carrier to N.carrier -/
  toFun : M.carrier → N.carrier
  /-- The bijection is injective -/
  injective : Function.Injective toFun
  /-- The bijection is surjective -/
  surjective : Function.Surjective toFun
  /-- Preserves constants -/
  preservesConst : ∀ (c : peanoLanguage.constSymbols),
    toFun (M.interpConst c) = N.interpConst c
  /-- Preserves function symbols -/
  preservesFunc : ∀ (f : peanoLanguage.funSymbols)
    (ts : Fin (peanoLanguage.funArity f) → M.carrier),
    toFun (M.interpFunc f ts) = N.interpFunc f (toFun ∘ ts)

-- ===================================================================
-- Lindenbaum's Lemma for G_= (equality version)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lindenbaum chain for equality consistency. Same construction as the
    non-equality version but using isConsistentSetEq. -/
noncomputable def lindenbaumChainEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) : Nat → Set (FormulaN L)
  | 0 => Gamma
  | n + 1 =>
    let prev := lindenbaumChainEq hL Gamma n
    let A := Countable.enumerate n
    if _ : isConsistentSetEq hL (fun x => prev x ∨ x = A)
    then fun x => prev x ∨ x = A
    else prev

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lindenbaumLimitEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) : Set (FormulaN L) :=
  fun A => ∃ n, lindenbaumChainEq hL Gamma n A

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem chainEq_consistent {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (hCon : isConsistentSetEq hL Gamma) :
    ∀ n, isConsistentSetEq hL (lindenbaumChainEq hL Gamma n) := by
-- BEGIN PROOF
  intro n; induction n with
  | zero => exact hCon
  | succ k ih =>
    show isConsistentSetEq hL (
      if _ : isConsistentSetEq hL (fun x => lindenbaumChainEq hL Gamma k x ∨
        x = Countable.enumerate k)
      then fun x => lindenbaumChainEq hL Gamma k x ∨ x = Countable.enumerate k
      else lindenbaumChainEq hL Gamma k)
    split <;> assumption

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem chainEq_mono {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L)) :
    ∀ n A, lindenbaumChainEq hL Gamma n A →
      lindenbaumChainEq hL Gamma (n + 1) A := by
-- BEGIN PROOF
  intro n A hA
  show (if _ : isConsistentSetEq hL (fun x => lindenbaumChainEq hL Gamma n x ∨
      x = Countable.enumerate n)
    then fun x => lindenbaumChainEq hL Gamma n x ∨ x = Countable.enumerate n
    else lindenbaumChainEq hL Gamma n) A
  split
  · exact Or.inl hA
  · exact hA

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem chainEq_mono_ge {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L)) :
    ∀ n m, n ≤ m → ∀ A, lindenbaumChainEq hL Gamma n A →
      lindenbaumChainEq hL Gamma m A := by
-- BEGIN PROOF
  intro n m h; induction h with
  | refl => exact fun A hA => hA
  | step _ ih => exact fun A hA => chainEq_mono hL Gamma _ A (ih A hA)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem list_in_limitEq_bounded {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L))
    (cs : List (FormulaN L))
    (hcs : ∀ c, c ∈ cs → lindenbaumLimitEq hL Gamma c) :
    ∃ k, ∀ c, c ∈ cs → lindenbaumChainEq hL Gamma k c := by
-- BEGIN PROOF
  induction cs with
  | nil => exact ⟨0, fun _ h => by simp at h⟩
  | cons a as ih =>
    have ha := hcs a List.mem_cons_self
    have has := ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨kas, hkas⟩ := has
    refine ⟨max ka kas, fun c hc => ?_⟩
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact chainEq_mono_ge hL Gamma ka _ (Nat.le_max_left ka kas) _ hka
    · exact chainEq_mono_ge hL Gamma kas _ (Nat.le_max_right ka kas) c (hkas c hc)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The limit of the equality Lindenbaum chain is consistent. -/
theorem limitEq_consistent {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (hCon : isConsistentSetEq hL Gamma) :
    isConsistentSetEq hL (lindenbaumLimitEq hL Gamma) := by
-- BEGIN PROOF
  apply (isConsistentSetEq_iff_emptySucc hL (lindenbaumLimitEq hL Gamma)).mpr
  intro cs hcs hprov
  obtain ⟨k, hk⟩ := list_in_limitEq_bounded hL Gamma cs hcs
  have hConK := chainEq_consistent hL Gamma hCon k
  exact (isConsistentSetEq_iff_emptySucc hL (lindenbaumChainEq hL Gamma k)).mp
    hConK cs (fun c hc => hk c hc) hprov

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The limit is maximal w.r.t. equality consistency. -/
theorem limitEq_maximal {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (_hCon : isConsistentSetEq hL Gamma) :
    ∀ (Sigma : Set (FormulaN L)),
      isConsistentSetEq hL Sigma →
      Set.subset (lindenbaumLimitEq hL Gamma) Sigma →
      lindenbaumLimitEq hL Gamma = Sigma := by
-- BEGIN PROOF
  intro Sigma hSigmaCon hSub
  funext B; apply propext
  constructor
  · exact fun hB => hSub B hB
  · intro hBSigma
    obtain ⟨n, rfl⟩ := Countable.enumerate_surj B
    have hConExt : isConsistentSetEq hL
        (fun x => lindenbaumChainEq hL Gamma n x ∨
          x = Countable.enumerate n) := by
      obtain ⟨B, hB⟩ := hSigmaCon
      refine ⟨B, ?_⟩
      intro cs hcs hprov
      exact hB cs (fun c hc =>
          match hcs c hc with
          | Or.inl h => hSub c ⟨n, chainEq_mono_ge hL Gamma n n
                          (Nat.le_refl n) c h⟩
          | Or.inr h => by rw [h]; exact hBSigma) hprov
    have hStep : lindenbaumChainEq hL Gamma (n + 1) (Countable.enumerate n) := by
      show (if _ : isConsistentSetEq hL (fun x => lindenbaumChainEq hL Gamma n x ∨
          x = Countable.enumerate n)
        then fun x => lindenbaumChainEq hL Gamma n x ∨ x = Countable.enumerate n
        else lindenbaumChainEq hL Gamma n) (Countable.enumerate n)
      rw [dif_pos hConExt]; right; rfl
    exact ⟨n + 1, hStep⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lindenbaum's Lemma for G_=: every consistent set can be extended
    to a maximal consistent set. Identical construction to the
    non-equality version using isConsistentSetEq. -/
theorem lindenbaum_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (hCon : isConsistentSetEq hL Gamma) :
    ∃ (Delta : Set (FormulaN L)),
      isMaximalConsistentSetEq hL Delta ∧ Set.subset Gamma Delta :=
-- BEGIN PROOF
  ⟨lindenbaumLimitEq hL Gamma,
   ⟨⟨limitEq_consistent hL Gamma hCon, limitEq_maximal hL Gamma hCon⟩,
    fun _ hA => ⟨0, hA⟩⟩⟩

-- ===================================================================
-- Bridge: G_=-consistency implies G-consistency
-- ===================================================================



-- ===================================================================
-- Core helper: G_=-consistency implies satisfiability with countability
-- ===================================================================

/-- Core blocked lemma for equality model existence. From G_=-consistency,
    produce a countable model satisfying Gamma. Both
    consistentEq_implies_satisfiable and lowenheim_skolem_eq reduce to
    this single lemma.

    The proof requires building an IsHintikkaSetEq from a G_=-consistent
    set Gamma that may contain equality formulas. Two approaches:

    (A) Equality search procedure (Gallier Def 5.6.3): Extend the
        non-equality growing closure with equality axiom injection
        (EQ_{1,i}, EQ_{2,i}, EQ_{3,i} at each level). The limit set
        satisfies H0-H5 (base Hintikka) and H6(i)-(iii) (equality).
        The quotient of the term algebra by eqCongruence gives a
        countable model via hintikka_set_eq_satisfiable.

    (B) Henkin construction: Use lindenbaum_eq to extend Gamma to a
        maximal G_=-consistent set Delta. Define t1 ~ t2 iff
        eq_(t1,t2) in Delta. Show ~ is a congruence (from G_= axioms
        and maximality). Build quotient model. Prove truth lemma by
        structural induction on formulas.

    Both approaches require ~400-600 lines of infrastructure.
    The existing signedLimitSetEq handles the hNoEq case (Gamma without
    equality). For Gamma WITH equality, adding all T(eq_ t1 t2)
    conflicts with F(eq_ t1 t2) from negated equalities in Gamma.
    See issue 54d63f0d. -/
theorem consistentEq_implies_satisfiable_countable {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSetEq hL Gamma) :
    ∃ (M : Structure L) (s : Assignment M),
      (∀ A, A ∈ Gamma → formulaEvalN M A s) ∧
      isAtMostCountable M := by
-- BEGIN PROOF
  -- DEBT(Theorem 5.6.4 route: countable model of a G_=-consistent set with equality formulae; issue 54d63f0d)
  sorry

-- ===================================================================
-- Model existence for G_= (equality version)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Model existence for G_=: consistency implies satisfiability.
    Delegates to consistentEq_implies_satisfiable_countable and
    discards the countability witness. -/
theorem consistentEq_implies_satisfiable {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSetEq hL Gamma) :
    satisfiableSetN Gamma := by
-- BEGIN PROOF
  obtain ⟨M, s, hsat, _⟩ := consistentEq_implies_satisfiable_countable hL Gamma hCon
  exact ⟨M, s, hsat⟩



-- ===================================================================
-- Lemma 5.6.4: satisfiable_implies_consistent_eq
-- ===================================================================

/-- Lemma 5.6.4: If a set Gamma of formulae over a first-order language
with equality is satisfiable, then it is consistent with respect to G_=. -/
@[blueprint "chap5__lemma_5_6_4" (main := true)]
theorem satisfiable_implies_consistent_eq {L : Language} (hL : L.hasEquality = true)
    (Gamma : Set (FormulaN L))
    (hSat : satisfiableSetN Gamma) :
    isConsistentSetEq hL Gamma 

-- ===================================================================
-- Theorem 5.6.4: consistent_implies_satisfiable_eq (Model Existence)
-- ===================================================================

/-- Theorem 5.6.4: Model existence for languages with equality. If a set
Gamma of formulae is G_=-consistent (some formula is unprovable from every finite subset), then Gamma is satisfiable. -/
@[blueprint "chap5__theorem_5_6_4" (main := true)]
theorem consistent_implies_satisfiable_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSetEq hL Gamma) :
    satisfiableSetN Gamma 

-- ===================================================================
-- Theorem 5.6.2: lowenheim_skolem_eq (Lowenheim-Skolem, equality)
-- ===================================================================

/-- Theorem 5.6.2: Lowenheim-Skolem for languages with equality. If a set
of formulae Gamma is satisfiable, then it is satisfiable in a structure whose domain is at most countably infinite. -/
@[blueprint "chap5__theorem_5_6_2" (main := true)]
theorem lowenheim_skolem_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hSat : satisfiableSetN Gamma) :
    ∃ (M : Structure L),
      satisfiableSetInN M Gamma ∧ isAtMostCountable M 

/-- Theorem 5.6.2 (finite-model remark): In every language with equality,
the singleton theory {∀x ∀y (x ≐ y)} is satisfiable and forces every model
to have a one-element, hence finite, domain. -/
@[blueprint "chap5__theorem_5_6_2"]
theorem ls_model_may_be_finite {L : Language} (hL : L.hasEquality = true) :
    ∃ Γ : Set (FormulaN L), satisfiableSetN Γ ∧
      ∀ M : Structure L, satisfiableSetInN M Γ → isFiniteDomain M 

-- ===================================================================
-- Theorem 5.6.3: compactness_eq (Compactness, equality)
-- ===================================================================

/-- Theorem 5.6.3: Compactness for languages with equality. A set Gamma of
formulae is satisfiable iff every finite subset of Gamma is satisfiable. -/
@[blueprint "chap5__theorem_5_6_3" (main := true)]
theorem compactness_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hFSS : finiteSubsetSatisfiableN Gamma) :
    satisfiableSetN Gamma 

-- ===================================================================
-- Lemma 5.6.5: maximal_consistent_extension_eq
-- ===================================================================

/-- Lemma 5.6.5: Given a first-order language with equality, every
consistent set Gamma is a subset of some maximal consistent set Delta (with respect to G_=). -/
@[blueprint "chap5__lemma_5_6_5" (main := true)]
theorem maximal_consistent_extension_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSetEq hL Gamma) :
    ∃ (Delta : Set (FormulaN L)),
      isMaximalConsistentSetEq hL Delta ∧ Set.subset Gamma Delta 

-- ===================================================================
-- Example 5.6.3: Models of the arithmetic theory and its expansion
-- ===================================================================

/-- Example 5.6.3: The natural-number structure 𝒩 models A_P. -/
theorem peanoNatStructure_models_peanoArithAxioms :
    ∀ A ∈ peanoArithAxioms, validInN peanoNatStructure A := by
  intro A hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | ⟨B, hFV, hFree, rfl⟩
  all_goals try simp [validInN, paSuccZeroAxiom, paSuccInjectiveAxiom,
    paAddZeroAxiom, paAddSuccAxiom, paMulZeroAxiom, paMulSuccAxiom,
    formulaEvalN, termEval, mkSucc, mkPlus, mkTimes, zeroTerm,
    peanoNatStructure, vec1, vec2, assignUpdate, Nat.add_assoc, Nat.mul_succ]
  -- REPAIR(T129): proof pending
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.6.3: Expand 𝒩 to L′ by interpreting the new constant c as k. -/
def expandedPeanoNatStructure (k : Nat) : Structure expandedArithLanguage where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc := peanoNatStructure.interpFunc
  interpConst
    | .inl c => peanoNatStructure.interpConst c
    | .inr _ => k
  interpPred := fun p => Empty.elim p



/-- Example 5.6.3: Every finite subset of Γ has a model obtained by
expanding 𝒩 with a suitable natural-number interpretation of c. -/
theorem gammaNonstandard_finite_nat_model
    (cs : List (FormulaN expandedArithLanguage))
    (hcs : ∀ A ∈ cs, A ∈ gammaNonstandard) :
    ∃ k : Nat, ∀ A ∈ cs, validInN (expandedPeanoNatStructure k) A := by
  -- REPAIR(T129): proof pending
  sorry

/-- The formulae of the finite-signature expanded arithmetic language
admit a surjective enumeration by natural numbers. -/
theorem expandedArithFormula_countable :
    Nonempty (Countable (FormulaN expandedArithLanguage)) := by
  -- REPAIR(T129): proof pending
  sorry



/-- Example 5.6.3: Γ has a model with at most countably many elements,
satisfying each member under every assignment. -/
@[attach_debt, blueprint "chap5__example_5_6_3"]
theorem gammaNonstandard_countable_model :
    ∃ M : Structure expandedArithLanguage,
      isAtMostCountable M ∧ ∀ A ∈ gammaNonstandard, validInN M A 

/-- Example 5.6.3: A chosen countable model M₀ of Γ in the expanded language. -/
@[blueprint "chap5__example_5_6_3"]
noncomputable def nonstandardModel0 : Structure expandedArithLanguage :=
  Classical.choose gammaNonstandard_countable_model



/-- Example 5.6.3: The reduct M of M₀ to the arithmetic language, retaining
its carrier, zero, successor, addition, and multiplication. -/
@[blueprint "chap5__example_5_6_3"]
noncomputable def nonstandardModel : Structure peanoLanguage where
  carrier := nonstandardModel0.carrier
  carrierNonempty := ⟨nonstandardModel0.interpConst (.inl ArithConst.zero)⟩
  interpFunc := nonstandardModel0.interpFunc
  interpConst := fun c => nonstandardModel0.interpConst (.inl c)
  interpPred := fun p => Empty.elim p

/-- Example 5.6.3: The element a of M is the interpretation of c in M₀. -/
@[blueprint "chap5__example_5_6_3"]
noncomputable def nonstandardElement : nonstandardModel.carrier :=
  nonstandardModel0.interpConst (.inr ())

















/-- Example 5.6.3: M is not isomorphic to the natural-number structure 𝒩. -/
@[blueprint "chap5__example_5_6_3" (main := true)]
theorem nonstandardModel_not_isomorphic :
    ¬ Nonempty (StructureIsomorphism nonstandardModel peanoNatStructure) 

end LCS.FirstOrder.Equality.MetaTheorems
