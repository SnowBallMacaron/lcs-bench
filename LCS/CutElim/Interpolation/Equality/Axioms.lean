import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import Attach
import LCS.CutElim.Interpolation.Equality.Axioms.ProofsStamp

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 6.5.1 (companion): The closed formula
forall x (x = x), the universally quantified reflexivity axiom
for equality. Uses a single universally bound variable (var 0). -/
@[blueprint "chap6__definition_6_5_1"]
def closedReflAxiom {L : Language} (hL : L.hasEquality = true) : FormulaN L :=
  FormulaN.all 0 (FormulaN.eq_ hL (Term.var 0) (Term.var 0))

-- ===================================================================
-- Definition 6.5.1 (companion def): closedFunCongAxiom
-- ===================================================================

/-- Definition 6.5.1 (companion): For an n-ary function symbol f,
the closed formula:
forall x1...xn forall y1...yn
  (x1=y1 /\ ... /\ xn=yn -> f(x1,...,xn) = f(y1,...,yn)).
Conjunctions are nested to the right, ending at the last conjunct.
All variables are universally quantified so the formula is closed.
Variables x_i use indices 0..n-1, variables y_i use indices n..2n-1. -/
@[blueprint "chap6__definition_6_5_1"]
def closedFunCongAxiom {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) : FormulaN L :=
  let n := L.funArity f
  -- Build x_i = y_i conjunctions
  let xs := fun (i : Fin n) => Term.var i.val
  let ys := fun (i : Fin n) => Term.var (n + i.val)
  -- Build the conjunction of equalities x1=y1 /\ ... /\ xn=yn
  let eqPairs : List (FormulaN L) :=
    (List.finRange n).map (fun i => FormulaN.eq_ hL (xs i) (ys i))
  let antecedent : FormulaN L :=
    match eqPairs with
    | [] => FormulaN.eq_ hL (Term.func f xs) (Term.func f ys)
    | h :: t => conjoinFormulae h (h :: t)
  let consequent : FormulaN L :=
    FormulaN.eq_ hL (Term.func f xs) (Term.func f ys)
  let body : FormulaN L :=
    match eqPairs with
    | [] => consequent
    | _ => FormulaN.impl antecedent consequent
  -- Universally quantify the x-block outside the y-block
  let quantifyAll (start : Nat) (count : Nat) (inner : FormulaN L) :
      FormulaN L :=
    (List.range count).foldr (fun i acc => FormulaN.all (start + i) acc) inner
  quantifyAll 0 n (quantifyAll n n body)

-- ===================================================================
-- Definition 6.5.1 (companion def): closedPredCongAxiom
-- ===================================================================

/-- Definition 6.5.1 (companion): For an n-ary predicate symbol P,
the closed formula:
forall x1...xn forall y1...yn
  (x1=y1 /\ ... /\ xn=yn /\ P(x1,...,xn) -> P(y1,...,yn)).
Conjunctions are nested to the right, ending at the last conjunct.
All variables are universally quantified so the formula is closed.
Variables x_i use indices 0..n-1, variables y_i use indices n..2n-1. -/
@[blueprint "chap6__definition_6_5_1"]
def closedPredCongAxiom {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols) : FormulaN L :=
  let n := L.predArity P
  let xs := fun (i : Fin n) => Term.var i.val
  let ys := fun (i : Fin n) => Term.var (n + i.val)
  -- Build the conjunction of equalities and P(x1,...,xn)
  let eqPairs : List (FormulaN L) :=
    (List.finRange n).map (fun i => FormulaN.eq_ hL (xs i) (ys i))
  let premises : List (FormulaN L) :=
    eqPairs ++ [FormulaN.predN P xs]
  let antecedent : FormulaN L :=
    match premises with
    | [] => FormulaN.predN P ys
    | h :: t => conjoinFormulae h (h :: t)
  let consequent : FormulaN L := FormulaN.predN P ys
  let body : FormulaN L :=
    match premises with
    | [] => consequent
    | _ => FormulaN.impl antecedent consequent
  -- Universally quantify the x-block outside the y-block
  let quantifyAll (start : Nat) (count : Nat) (inner : FormulaN L) :
      FormulaN L :=
    (List.range count).foldr (fun i acc => FormulaN.all (start + i) acc) inner
  quantifyAll 0 n (quantifyAll n n body)

-- ===================================================================
-- Definition 6.5.1 (companion def): closedEqCongAxiom
-- ===================================================================

/-- Definition 6.5.1 (companion): The closed predicate-congruence
axiom for built-in equality:
forall s1 s2 t1 t2,
  (s1=t1 /\ (s2=t2 /\ s1=s2)) -> t1=t2.
This case is separate because equality is represented by `FormulaN.eq_`
rather than an element of `L.predSymbols`. -/
@[blueprint "chap6__definition_6_5_1"]
def closedEqCongAxiom {L : Language} (hL : L.hasEquality = true) :
    FormulaN L :=
  FormulaN.allList [0, 1, 2, 3]
    (eqCongruenceImplEq hL
      (Term.var 0) (Term.var 1) (Term.var 2) (Term.var 3))

-- ===================================================================
-- Definition 6.5.1 (helper def): sequentFunSymbolsList
-- ===================================================================

/-- Definition 6.5.1 (helper): Extracts a list of function symbols
occurring in a sequent by collecting from all formulae. Returns a
list (with possible duplicates). -/
@[blueprint "chap6__definition_6_5_1"]
def sequentFunSymbolsList {L : Language} [DecidableEq L.funSymbols]
    (S : Sequent L) : List L.funSymbols :=
  let rec termFunSymbols : Term L → List L.funSymbols
    | .var _ => []
    | .const _ => []
    | .func f ts =>
      [f] ++ (List.finRange (L.funArity f)).flatMap
        (fun i => termFunSymbols (ts i))
  let rec formulaFunSyms : FormulaN L → List L.funSymbols
    | .predN _ ts =>
      (List.finRange _).flatMap (fun i => termFunSymbols (ts i))
    | .eq_ _ t1 t2 => termFunSymbols t1 ++ termFunSymbols t2
    | .conj A B => formulaFunSyms A ++ formulaFunSyms B
    | .disj A B => formulaFunSyms A ++ formulaFunSyms B
    | .impl A B => formulaFunSyms A ++ formulaFunSyms B
    | .neg A => formulaFunSyms A
    | .all _ A => formulaFunSyms A
    | .ex _ A => formulaFunSyms A
  ((S.antecedent ++ S.succedent).flatMap formulaFunSyms).eraseDups

-- ===================================================================
-- Definition 6.5.1 (helper def): sequentPredSymbolsList
-- ===================================================================

/-- Definition 6.5.1 (helper): Extracts the distinct ordinary predicate
symbols occurring in a sequent. Built-in equality is detected separately
by `sequentHasEq`. -/
@[blueprint "chap6__definition_6_5_1"]
def sequentPredSymbolsList {L : Language} [DecidableEq L.predSymbols]
    (S : Sequent L) : List L.predSymbols :=
  let rec formulaPredSyms : FormulaN L → List L.predSymbols
    | .predN P _ => [P]
    | .eq_ _ _ _ => []
    | .conj A B => formulaPredSyms A ++ formulaPredSyms B
    | .disj A B => formulaPredSyms A ++ formulaPredSyms B
    | .impl A B => formulaPredSyms A ++ formulaPredSyms B
    | .neg A => formulaPredSyms A
    | .all _ A => formulaPredSyms A
    | .ex _ A => formulaPredSyms A
  ((S.antecedent ++ S.succedent).flatMap formulaPredSyms).eraseDups

/-- Definition 6.5.1 (helper): Whether an equality atom occurs in any
formula of the antecedent or succedent, including under connectives and quantifiers. -/
@[blueprint "chap6__definition_6_5_1"]
def sequentHasEq {L : Language} (S : Sequent L) : Bool :=
  let rec formulaHasEq : FormulaN L → Bool
    | .predN _ _ => false
    | .eq_ _ _ _ => true
    | .conj A B => formulaHasEq A || formulaHasEq B
    | .disj A B => formulaHasEq A || formulaHasEq B
    | .impl A B => formulaHasEq A || formulaHasEq B
    | .neg A => formulaHasEq A
    | .all _ A => formulaHasEq A
    | .ex _ A => formulaHasEq A
  (S.antecedent ++ S.succedent).any formulaHasEq

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Replay, LCS.CutElim.Interpolation.Equality.Support
theorem eq_of_mem_optionalSingleton {α : Type} (b : Bool) {a c : α}
    (h : a ∈ (if b then [c] else [])) : a = c := by
  cases b <;> simp_all

-- ===================================================================
-- Definition 6.5.1: closedEqualityAxioms
-- ===================================================================

/-- Definition 6.5.1: Given a sequent S = Gamma -> Delta, the set
S_e of closed equality axioms for S. For all predicate and function
symbols occurring in S: reflexivity (forall x (x = x)), function
congruence (forall x1...xn y1...yn (x1=y1 /\ ... /\ xn=yn ->
f(x1,...,xn)=f(y1,...,yn))), and predicate congruence
(forall x1...xn y1...yn (x1=y1 /\ ... /\ xn=yn /\ P(x1,...,xn) ->
P(y1,...,yn))). Collects the closed reflexivity axiom, one closed
function congruence axiom for each function symbol occurring in S,
and one closed predicate congruence axiom for each predicate symbol
occurring in S. The built-in equality predicate's congruence axiom
is included exactly when an equality atom occurs in S. -/
@[blueprint "chap6__definition_6_5_1" (main := true)]
def closedEqualityAxioms {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) : List (FormulaN L) :=
  [closedReflAxiom hL] ++
  (sequentFunSymbolsList S).map (closedFunCongAxiom hL) ++
  ((sequentPredSymbolsList S).map (closedPredCongAxiom hL) ++
    (if sequentHasEq S then [closedEqCongAxiom hL] else []))

-- ===================================================================
-- Helper: membership of symbols in equality axiom toSequents
-- ===================================================================





-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem closedFunCongAxiom_mem_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (f : L.funSymbols) (hf : f ∈ sequentFunSymbolsList S) :
    closedFunCongAxiom hL f ∈ closedEqualityAxioms hL S := by
-- BEGIN PROOF
  simp only [closedEqualityAxioms]
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨f, hf, rfl⟩))

-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem closedPredCongAxiom_mem_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (P : L.predSymbols) (hP : P ∈ sequentPredSymbolsList S) :
    closedPredCongAxiom hL P ∈ closedEqualityAxioms hL S := by
-- BEGIN PROOF
  simp only [closedEqualityAxioms]
  exact List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨P, hP, rfl⟩))

-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem closedEqCongAxiom_mem_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (hEq : sequentHasEq S = true) :
    closedEqCongAxiom hL ∈ closedEqualityAxioms hL S := by
  simp [closedEqualityAxioms, hEq]

-- ===================================================================
-- Helper: lkeProvable for any valid sequent (semantic bridge)
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
/-- Any semantically valid sequent is LKe-provable, using the LKe
semantic cut. This bridges semantic validity to LKe provability.
The proof routes through G= completeness for sequents satisfying
the normalization conditions (no free-bound overlap, no falsum,
no pred0), plus Countable (Term L). For arbitrary sequents, the
statement reduces to normalization infrastructure (alpha-renaming,
falsum elimination, pred0 normalization) which is not yet formalized. -/
theorem lkeProvable_of_sequentValid {L : Language}
    (s : Sequent L) (hvalid : sequentValid s) :
    lkeProvable s := by
-- BEGIN PROOF
  exact LCS.CutElim.LKe.Equivalence.lkeProvable_of_valid s hvalid



-- ===================================================================
-- Helper: n-ary instantiation of closed axioms (core technical lemmas)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Sequentially substitute a list of terms for a list of variables.
Extra variables or terms are ignored once either list is exhausted. -/
def formulaSubstTerms {L : Language} :
    FormulaN L → List Nat → List (Term L) → FormulaN L
  | A, [], _ => A
  | A, _, [] => A
  | A, x :: xs, t :: ts =>
      formulaSubstTerms (formulaSubstN A t x) xs ts

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Maximum variable index occurring in a finite list of terms. -/
def listTermMaxVar {L : Language} (ts : List (Term L)) : Nat :=
  (ts.map termMaxVar).foldl Nat.max 0

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A base strictly above every variable in the body, binder list,
and instantiating terms of a finite universal-instantiation problem. -/
def captureSafeFreshBase {L : Language} (A : FormulaN L)
    (vars : List Nat) (ts : List (Term L)) : Nat :=
  Nat.succ
    (Nat.max (formulaAllMaxVar A)
      (Nat.max (vars.foldl Nat.max 0) (listTermMaxVar ts)))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pairwise-distinct variables, one per binder, chosen above the
formula, binder list, and all instantiating terms. -/
def captureSafeFreshVars {L : Language} (A : FormulaN L)
    (vars : List Nat) (ts : List (Term L)) : List Nat :=
  (List.range vars.length).map
    (fun i => captureSafeFreshBase A vars ts + i)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The capture-safe simultaneous instance represented syntactically
as two sequential passes: first alpha-rename every binder to a fresh
variable, then replace those fresh variables by the requested terms. -/
def captureSafeAllListInstance {L : Language} (A : FormulaN L)
    (vars : List Nat) (ts : List (Term L)) : FormulaN L :=
  let fresh := captureSafeFreshVars A vars ts
  formulaSubstTerms (formulaSubstVars A vars fresh) fresh ts

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): substitution commutes
with a universal prefix when the substituted variable is not bound by
that prefix. -/
theorem formulaSubstN_allList_of_not_mem {L : Language}
    (vars : List Nat) (A : FormulaN L) (t : Term L) (x : Nat)
    (hx : x ∉ vars) :
    formulaSubstN (FormulaN.allList vars A) t x =
      FormulaN.allList vars (formulaSubstN A t x) := by
  induction vars with
  | nil => rfl
  | cons y ys ih =>
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxys : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change
      formulaSubstN
          (FormulaN.all y (FormulaN.allList ys A)) t x =
        FormulaN.all y
          (FormulaN.allList ys (formulaSubstN A t x))
    rw [show
      formulaSubstN
          (FormulaN.all y (FormulaN.allList ys A)) t x =
        FormulaN.all y
          (formulaSubstN (FormulaN.allList ys A) t x) by
      simp [formulaSubstN, hxy]]
    exact congrArg (FormulaN.all y) (ih hxys)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): the bound variables
of a universal prefix are exactly the bound variables of its body
together with the prefix variables. -/
theorem formulaBV_allList_iff {L : Language}
    (vars : List Nat) (A : FormulaN L) (v : Nat) :
    v ∈ formulaBVN (FormulaN.allList vars A) ↔
      v ∈ formulaBVN A ∨ v ∈ vars := by
  induction vars with
  | nil => simp [FormulaN.allList]
  | cons x xs ih =>
    change
      v ∈ formulaBVN
          (FormulaN.all x (FormulaN.allList xs A)) ↔
        v ∈ formulaBVN A ∨ v ∈ x :: xs
    simp only [formulaBVN, List.mem_cons]
    constructor
    · intro h
      rcases h with h | hx
      · rcases ih.mp h with hA | hxs
        · exact Or.inl hA
        · exact Or.inr (Or.inr hxs)
      · change v = x at hx
        exact Or.inr (Or.inl hx)
    · rintro (hA | rfl | hxs)
      · exact Or.inl (ih.mpr (Or.inl hA))
      · exact Or.inr rfl
      · exact Or.inl (ih.mpr (Or.inr hxs))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): sequential variable
renaming does not change the set of bound variables. -/
theorem formulaBV_formulaSubstVars {L : Language}
    (A : FormulaN L) (vars fresh : List Nat) :
    formulaBVN (formulaSubstVars A vars fresh) = formulaBVN A := by
  induction vars generalizing A fresh with
  | nil => simp [formulaSubstVars]
  | cons x xs ih =>
    cases fresh with
    | nil => simp [formulaSubstVars]
    | cons y ys =>
      simp only [formulaSubstVars]
      rw [ih, formulaBV_formulaSubst]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): alpha-renaming an
entire universal prefix is derivable in FOLK. The fresh variables are
required to be pairwise distinct, disjoint from the old binders, and
absent from both the free and bound variables of the body. -/
theorem folkProvable_alphaRenameAllList {L : Language}
    (A : FormulaN L) (vars fresh : List Nat)
    (hLen : vars.length = fresh.length)
    (hVars : vars.Nodup)
    (hFresh : fresh.Nodup)
    (hDisjoint : ∀ z ∈ fresh, z ∉ vars)
    (hAbsent : ∀ z ∈ fresh,
      z ∉ formulaFVN A ∧ z ∉ formulaBVN A) :
    folkProvable
      (Sequent.mk [FormulaN.allList vars A]
        [FormulaN.allList fresh (formulaSubstVars A vars fresh)]) := by
  induction vars generalizing A fresh with
  | nil =>
    have : fresh = [] :=
      List.length_eq_zero_iff.mp (by simpa using hLen.symm)
    subst fresh
    simpa [FormulaN.allList, formulaSubstVars] using
      (folkCutFreeProvable_to_folkProvable (folkCutFree_axiom A))
  | cons x xs ih =>
    cases fresh with
    | nil => simp at hLen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ_inj] at hLen
      simp only [List.nodup_cons] at hVars hFresh
      have hyNotXs : y ∉ xs := by
        exact fun hy => hDisjoint y (List.mem_cons_self)
          (List.mem_cons_of_mem _ hy)
      have hyAbsent := hAbsent y (List.mem_cons_self)
      have hTailDisjoint : ∀ z ∈ ys, z ∉ xs := by
        intro z hz hzx
        exact hDisjoint z (List.mem_cons_of_mem _ hz)
          (List.mem_cons_of_mem _ hzx)
      have hTailAbsent :
          ∀ z ∈ ys,
            z ∉ formulaFVN (formulaSubstN A (.var y) x) ∧
              z ∉ formulaBVN (formulaSubstN A (.var y) x) := by
        intro z hz
        have hzAbsent := hAbsent z (List.mem_cons_of_mem _ hz)
        have hzy : z ≠ y := fun h => hFresh.1 (h ▸ hz)
        constructor
        · exact formulaFV_formulaSubst_ne A x y z hzAbsent.1 hzy
        · rw [formulaBV_formulaSubst]
          exact hzAbsent.2
      have hIH := ih (formulaSubstN A (.var y) x) ys hLen
        hVars.2 hFresh.2 hTailDisjoint hTailAbsent
      obtain ⟨tIH⟩ := hIH
      let targetTail :=
        FormulaN.allList ys
          (formulaSubstVars (formulaSubstN A (.var y) x) xs ys)
      have hyNotBV :
          y ∉ formulaBVN (FormulaN.allList xs A) := by
        intro hy
        rcases (formulaBV_allList_iff xs A y).mp hy with hyA | hyXs
        · exact hyAbsent.2 hyA
        · exact hyNotXs hyXs
      have hFree :
          isFreeForN (.var y) x (FormulaN.allList xs A) := by
        apply isFreeForN_of_bv_disjoint
        intro v hv
        change v = y at hv
        subst v
        exact hyNotBV
      have tLeft :
          FOLKProofTree
            (Sequent.mk
              [FormulaN.all x (FormulaN.allList xs A)]
              [targetTail]) := by
        apply FOLKProofTree.onePremise
          (.allLeft (.var y) x (FormulaN.allList xs A) []
            [targetTail] hFree)
        simpa [targetTail,
          formulaSubstN_allList_of_not_mem xs A (.var y) x hVars.1]
          using tIH
      have hySource :
          y ∉ formulaFVN
            (FormulaN.all x (FormulaN.allList xs A)) := by
        intro hy
        have hy' :=
          (formulaFV_allList_iff (x :: xs) A y).mp hy
        exact hyAbsent.1 hy'.1
      have hEigen :
          ∀ F ∈
              (Sequent.mk
                [FormulaN.all x (FormulaN.allList xs A)]
                ([] ++ [FormulaN.all y targetTail])).antecedent ++
              (Sequent.mk
                [FormulaN.all x (FormulaN.allList xs A)]
                ([] ++ [FormulaN.all y targetTail])).succedent,
            y ∉ formulaFVN F := by
        intro F hF
        simp only [List.nil_append, List.singleton_append,
          List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | hF
        · exact hySource
        · subst F
          intro hy
          exact hy.2 rfl
      refine ⟨?_⟩
      simpa [FormulaN.allList, formulaSubstVars, targetTail,
        formulaSubstN_var_self] using
        FOLKProofTree.onePremise
          (.allRight y y targetTail
            [FormulaN.all x (FormulaN.allList xs A)] []
            hEigen (isFreeForN_var_self targetTail y))
          (by simpa [formulaSubstN_var_self] using tLeft)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): directly instantiate
a universal prefix when the body is open and every instantiating term
is disjoint from every still-bound prefix variable. -/
theorem folkProvable_instantiateAllList {L : Language}
    (A : FormulaN L) (vars : List Nat) (ts : List (Term L))
    (hLen : vars.length = ts.length)
    (hVars : vars.Nodup)
    (hOpen : formulaBVN A = ∅)
    (hTerms : ∀ t ∈ ts, ∀ x ∈ vars, x ∉ termFV t) :
    folkProvable
      (Sequent.mk [FormulaN.allList vars A]
        [formulaSubstTerms A vars ts]) := by
  induction vars generalizing A ts with
  | nil =>
    have : ts = [] :=
      List.length_eq_zero_iff.mp (by simpa using hLen.symm)
    subst ts
    simpa [FormulaN.allList, formulaSubstTerms] using
      (folkCutFreeProvable_to_folkProvable (folkCutFree_axiom A))
  | cons x xs ih =>
    cases ts with
    | nil => simp at hLen
    | cons t ts =>
      simp only [List.length_cons, Nat.succ_inj] at hLen
      simp only [List.nodup_cons] at hVars
      have hOpenSubst :
          formulaBVN (formulaSubstN A t x) = ∅ := by
        rw [formulaBV_formulaSubst, hOpen]
      have hTailTerms :
          ∀ u ∈ ts, ∀ y ∈ xs,
            y ∉ termFV u := by
        intro u hu y hy
        exact hTerms u (List.mem_cons_of_mem _ hu) y
          (List.mem_cons_of_mem _ hy)
      have hIH := ih (formulaSubstN A t x) ts hLen hVars.2
        hOpenSubst hTailTerms
      obtain ⟨tIH⟩ := hIH
      have hFree :
          isFreeForN t x (FormulaN.allList xs A) := by
        apply isFreeForN_of_bv_disjoint
        intro v hv hBV
        rcases (formulaBV_allList_iff xs A v).mp hBV with hA | hxs
        · rw [hOpen] at hA
          exact hA
        · exact hTerms t (List.mem_cons_self) v
            (List.mem_cons_of_mem _ hxs) hv
      refine ⟨?_⟩
      have tPrem :
          FOLKProofTree
            (Sequent.mk
              [formulaSubstN (FormulaN.allList xs A) t x]
              [formulaSubstTerms (formulaSubstN A t x) xs ts]) := by
        rw [formulaSubstN_allList_of_not_mem xs A t x hVars.1]
        exact tIH
      simpa [FormulaN.allList, formulaSubstTerms] using
        FOLKProofTree.onePremise
          (.allLeft t x (FormulaN.allList xs A) []
            [formulaSubstTerms (formulaSubstN A t x) xs ts] hFree)
          tPrem

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): every generated fresh
variable lies strictly above the formula, every old binder, and every
instantiating term. -/
theorem captureSafeFreshVars_gt {L : Language}
    (A : FormulaN L) (vars : List Nat) (ts : List (Term L))
    (z : Nat) (hz : z ∈ captureSafeFreshVars A vars ts) :
    formulaAllMaxVar A < z ∧
      (∀ x ∈ vars, x < z) ∧
      (∀ t ∈ ts, termMaxVar t < z) := by
  rw [captureSafeFreshVars] at hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  have hBase :
      Nat.max (formulaAllMaxVar A)
          (Nat.max (vars.foldl Nat.max 0) (listTermMaxVar ts)) <
        captureSafeFreshBase A vars ts := by
    simp [captureSafeFreshBase]
  have hBaseLe :
      captureSafeFreshBase A vars ts ≤
        captureSafeFreshBase A vars ts + i := Nat.le_add_right ..
  have hMaxLt :
      Nat.max (formulaAllMaxVar A)
          (Nat.max (vars.foldl Nat.max 0) (listTermMaxVar ts)) <
        captureSafeFreshBase A vars ts + i :=
    Nat.lt_of_lt_of_le hBase hBaseLe
  constructor
  · exact Nat.lt_of_le_of_lt (Nat.le_max_left ..) hMaxLt
  constructor
  · intro x hx
    have hxMax : x ≤ vars.foldl Nat.max 0 :=
      foldl_max_mem_le vars 0 x hx
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hxMax
        (Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)))
      hMaxLt
  · intro t ht
    have htMem : termMaxVar t ∈ ts.map termMaxVar :=
      List.mem_map.mpr ⟨t, ht, rfl⟩
    have htMax : termMaxVar t ≤ listTermMaxVar ts := by
      exact foldl_max_mem_le (ts.map termMaxVar) 0 _ htMem
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans htMax
        (Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)))
      hMaxLt

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): the generated fresh
list has exactly one entry per old binder. -/
@[simp]
theorem captureSafeFreshVars_length {L : Language}
    (A : FormulaN L) (vars : List Nat) (ts : List (Term L)) :
    (captureSafeFreshVars A vars ts).length = vars.length := by
  simp [captureSafeFreshVars]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): generated fresh
variables are pairwise distinct. -/
theorem captureSafeFreshVars_nodup {L : Language}
    (A : FormulaN L) (vars : List Nat) (ts : List (Term L)) :
    (captureSafeFreshVars A vars ts).Nodup := by
  rw [captureSafeFreshVars]
  exact List.Pairwise.map
    (fun i => captureSafeFreshBase A vars ts + i)
    (by
      intro i j hij hEq
      exact hij (Nat.add_left_cancel hEq))
    (List.nodup_range (n := vars.length))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Proof of Lemma 6.5.3 (capture-safe helper): automatic
alpha-renaming followed by direct instantiation derives an arbitrary
n-ary instance without any capture restriction on the requested
terms. -/
theorem folkProvable_captureSafeAllListInstantiation {L : Language}
    (A : FormulaN L) (vars : List Nat) (ts : List (Term L))
    (hLen : vars.length = ts.length)
    (hVars : vars.Nodup)
    (hOpen : formulaBVN A = ∅) :
    folkProvable
      (Sequent.mk [FormulaN.allList vars A]
        [captureSafeAllListInstance A vars ts]) := by
  let fresh := captureSafeFreshVars A vars ts
  let alphaBody := formulaSubstVars A vars fresh
  have hFreshLen : vars.length = fresh.length := by
    simp [fresh]
  have hFreshNodup : fresh.Nodup := by
    exact captureSafeFreshVars_nodup A vars ts
  have hDisjoint : ∀ z ∈ fresh, z ∉ vars := by
    intro z hz hzVars
    have hgt := (captureSafeFreshVars_gt A vars ts z hz).2.1 z hzVars
    omega
  have hAbsent : ∀ z ∈ fresh,
      z ∉ formulaFVN A ∧ z ∉ formulaBVN A := by
    intro z hz
    have hgt := (captureSafeFreshVars_gt A vars ts z hz).1
    exact
      ⟨formulaAllMaxVar_gt_no_fv A z hgt,
       formulaAllMaxVar_gt_no_bv A z hgt⟩
  have hAlpha :
      folkProvable
        (Sequent.mk [FormulaN.allList vars A]
          [FormulaN.allList fresh alphaBody]) := by
    exact folkProvable_alphaRenameAllList A vars fresh hFreshLen
      hVars hFreshNodup hDisjoint hAbsent
  have hAlphaOpen : formulaBVN alphaBody = ∅ := by
    dsimp [alphaBody]
    rw [formulaBV_formulaSubstVars, hOpen]
  have hTermFresh :
      ∀ t ∈ ts, ∀ z ∈ fresh, z ∉ termFV t := by
    intro t ht z hz
    exact termFV_gt_maxVar t z
      ((captureSafeFreshVars_gt A vars ts z hz).2.2 t ht)
  have hInstantiate :
      folkProvable
        (Sequent.mk [FormulaN.allList fresh alphaBody]
          [formulaSubstTerms alphaBody fresh ts]) := by
    exact folkProvable_instantiateAllList alphaBody fresh ts
      (by simpa [fresh] using hLen) hFreshNodup hAlphaOpen hTermFresh
  simpa [captureSafeAllListInstance, fresh, alphaBody] using
    folkProvable_cut
      (FormulaN.allList fresh alphaBody)
      [FormulaN.allList vars A] [] [] [formulaSubstTerms alphaBody fresh ts]
      hAlpha hInstantiate

-- ATTACH-BLOCKER: unsupported untagged example
/-- Regression for the capture obstruction handled above: directly
instantiating the outer binder `1` by `var 0` is not free for the
remaining inner binder `0`. -/
example {L : Language} (hL : L.hasEquality = true) :
    ¬ isFreeForN (.var 0) 1
      (FormulaN.all 0
        (FormulaN.eq_ hL (.var 1) (.var 0))) := by
  simp only [isFreeForN]
  rintro (h | h)
  · omega
  · exact h.1 rfl

-- ATTACH-BLOCKER: unsupported untagged example
/-- Regression for the same obstruction: alpha-renaming first derives
the intended simultaneous swap, rather than the captured result of
substituting directly through the original binder sequence. -/
example {L : Language} (hL : L.hasEquality = true) :
    folkProvable
      (Sequent.mk
        [FormulaN.allList [1, 0]
          (FormulaN.eq_ hL (.var 1) (.var 0))]
        [FormulaN.eq_ hL (.var 0) (.var 1)]) := by
  simpa [captureSafeAllListInstance, captureSafeFreshVars,
    captureSafeFreshBase, listTermMaxVar, formulaSubstVars,
    formulaSubstTerms, formulaAllMaxVar, termMaxVar, formulaSubstN,
    termSubst, List.range, List.range.loop] using
    folkProvable_captureSafeAllListInstantiation
      (FormulaN.eq_ hL (.var 1) (.var 0))
      [1, 0] [.var 0, .var 1]
      (hLen := by rfl) (hVars := by simp) (hOpen := by rfl)







end LCS.CutElim.Interpolation.Equality
end

