import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import Attach
import LCS.CutElim.Interpolation.Equality.ClosedAxioms.ProofsStamp

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
-- Helper: foldr all is valid if inner is valid under all assignments
-- ===================================================================

theorem foldr_all_valid {L : Language} (M : Structure L) (s : Assignment M)
    (start count : Nat) (inner : FormulaN L)
    (h : ∀ (s' : Assignment M), formulaEvalN M inner s') :
    formulaEvalN M ((List.range count).foldr (fun i acc => FormulaN.all (start + i) acc) inner) s := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => simp [List.range]; exact h s
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    apply ih; intro s'; simp [formulaEvalN]; intro a
    exact h (assignUpdate s' (start + n) a)

-- ===================================================================
-- Helper: right-nested conjunction member evaluates to true
-- ===================================================================

theorem conjoin_mem_eval {L : Language} (M : Structure L) (s : Assignment M)
    (hd : FormulaN L) (tl : List (FormulaN L))
    (h : formulaEvalN M (conjoinFormulae hd (hd :: tl)) s) :
    ∀ A ∈ hd :: tl, formulaEvalN M A s := by
  exact conjoinFormulaeEval h

-- ===================================================================
-- Helper: map_finRange_nil
-- ===================================================================

theorem map_finRange_nil {n : Nat} {α : Type} (f : Fin n → α)
    (h : (List.finRange n).map f = []) : n = 0 := by
-- BEGIN PROOF
  cases n with
  | zero => rfl
  | succ k => simp [List.finRange] at h

-- ===================================================================
-- Helper: closedFunCongAxiom is universally valid
-- ===================================================================

set_option maxHeartbeats 1600000 in
theorem closedFunCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedFunCongAxiom hL f) s := by
-- BEGIN PROOF
  unfold closedFunCongAxiom; simp only []
  apply foldr_all_valid; intro s1; apply foldr_all_valid; intro s2
  generalize hep : (List.finRange (L.funArity f)).map
    (fun (i : Fin (L.funArity f)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
      (Term.var (L.funArity f + (i : Nat)))) = eqPairs
  cases eqPairs with
  | nil =>
    simp [formulaEvalN, termEval]
    congr 1; funext i; exact absurd i.isLt (by
      have := map_finRange_nil _ hep; omega)
  | cons hd tl =>
    simp only [formulaEvalN, termEval]
    intro hAnte
    congr 1; funext i
    have hMem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
        (Term.var (L.funArity f + (i : Nat))) ∈ hd :: tl := by
      rw [← hep]; exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hEq := conjoin_mem_eval M s2 hd tl hAnte _ hMem
    simp [formulaEvalN, termEval] at hEq
    exact hEq

-- ===================================================================
-- Helper: closedPredCongAxiom is universally valid
-- ===================================================================

set_option maxHeartbeats 1600000 in
theorem closedPredCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedPredCongAxiom hL P) s := by
-- BEGIN PROOF
  unfold closedPredCongAxiom; simp only []
  apply foldr_all_valid; intro s1; apply foldr_all_valid; intro s2
  generalize hprem : (List.finRange (L.predArity P)).map
    (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
      (Term.var (L.predArity P + (i : Nat)))) ++
    [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] = premises
  cases premises with
  | nil =>
    exfalso
    have hmem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈
        (List.finRange (L.predArity P)).map
          (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
            (Term.var (L.predArity P + (i : Nat)))) ++
        [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
      List.mem_append_right _ (List.Mem.head ..)
    rw [hprem] at hmem; simp at hmem
  | cons hd tl =>
    simp only [formulaEvalN, termEval]
    intro hAnte
    have hAllMem := conjoin_mem_eval M s2 hd tl hAnte
    have hPredMem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈ hd :: tl := by
      have hmem : FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat)) ∈
          (List.finRange (L.predArity P)).map
            (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
              (Term.var (L.predArity P + (i : Nat)))) ++
          [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
        List.mem_append_right _ (List.Mem.head ..)
      rw [hprem] at hmem; exact hmem
    have hPred := hAllMem _ hPredMem
    simp only [formulaEvalN, termEval] at hPred
    have hEqs : ∀ (i : Fin (L.predArity P)), s2 i.val = s2 (L.predArity P + i.val) := by
      intro i
      have hEqMem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
          (Term.var (L.predArity P + (i : Nat))) ∈ hd :: tl := by
        have hmem : FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
            (Term.var (L.predArity P + (i : Nat))) ∈
            (List.finRange (L.predArity P)).map
              (fun (i : Fin (L.predArity P)) => FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
                (Term.var (L.predArity P + (i : Nat)))) ++
            [FormulaN.predN P (fun (i : Fin (L.predArity P)) => Term.var (i : Nat))] :=
          List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
        rw [hprem] at hmem; exact hmem
      have := hAllMem _ hEqMem
      simp only [formulaEvalN, termEval] at this; exact this
    have : (fun i : Fin (L.predArity P) => s2 (L.predArity P + i.val)) =
        (fun i : Fin (L.predArity P) => s2 i.val) :=
      funext (fun i => (hEqs i).symm)
    rw [this]; exact hPred

-- ===================================================================
-- Helper: closedEqCongAxiom is universally valid
-- ===================================================================

theorem closedEqCongAxiom_eval {L : Language} (hL : L.hasEquality = true)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (closedEqCongAxiom hL) s := by
-- BEGIN PROOF
  simp only [closedEqCongAxiom, FormulaN.allList, List.foldr_cons,
    List.foldr_nil, formulaEvalN]
  rintro a0 a1 a2 a3 ⟨h1, h2, h3⟩
  simp only [formulaEvalN] at h1 h2 h3 ⊢
  rw [← h1, h3, h2]

-- ===================================================================
-- Helper: every formula in closedEqualityAxioms is universally valid
-- ===================================================================

theorem closedEqualityAxioms_universally_valid {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (A : FormulaN L)
    (hA : A ∈ closedEqualityAxioms hL S) :
    ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s := by
-- BEGIN PROOF
  simp only [closedEqualityAxioms] at hA
  rcases List.mem_append.mp hA with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      intro M s; simp [closedReflAxiom, formulaEvalN, termEval, assignUpdate]
    · rw [List.mem_map] at hFun
      obtain ⟨f, _, hfEq⟩ := hFun; subst hfEq
      exact closedFunCongAxiom_eval hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, _, hPEq⟩ := hPred; subst hPEq
      exact closedPredCongAxiom_eval hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_eval hL

end LCS.CutElim.Interpolation.Equality
end
