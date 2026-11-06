import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Substitution
import LCS.Propositional.Syntax
import LCS.Propositional.Semantics
import LCS.FirstOrder.Semantics.Subformulae.RectifiedFormulae
import Attach
import LCS.FirstOrder.Semantics.Subformulae.Rectification.ProofsStamp

section
namespace LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

-- ===================================================================
-- Example 5.3.3: Non-rectified and rectified formulae
-- ===================================================================

/-- Example 5.3.3 (companion): Predicate symbols for the example language. -/
@[blueprint "chap5__example_5_3_3"]
inductive ExPred_5_3_3 : Type where
  | R : ExPred_5_3_3
  | P : ExPred_5_3_3

/-- Example 5.3.3 (companion): The example language with binary R and unary P. -/
@[blueprint "chap5__example_5_3_3"]
def exampleLang_5_3_3 : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPred_5_3_3
  predArity := fun
    | .R => 2
    | .P => 1

/-- Example 5.3.3: The non-rectified formula A = (forall x(R x y supset P
x) and forall y(neg R x y and forall x P x)), using the language with binary R and unary P, where x=0, y=1. A is not rectified because x and y each appear both free and bound, and x is bound by two distinct quantifiers. -/
@[blueprint "chap5__example_5_3_3"]
def exampleNonRectified_5_3_3 : FormulaN exampleLang_5_3_3 :=
  FormulaN.conj
    (FormulaN.all 0
      (FormulaN.impl
        (FormulaN.predN ExPred_5_3_3.R
          (vec2 (Term.var 0) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P
          (fun _ => Term.var 0))))
    (FormulaN.all 1
      (FormulaN.conj
        (FormulaN.neg
          (FormulaN.predN ExPred_5_3_3.R
            (vec2 (Term.var 0) (Term.var 1))))
        (FormulaN.all 0
          (FormulaN.predN ExPred_5_3_3.P
            (fun _ => Term.var 0)))))

/-- Example 5.3.3: The rectified formula B = (forall u(R u y supset P u)
and forall v(neg R x v and forall z P z)), where u=2, v=3, z=4 as fresh variable indices. B is rectified: each quantifier binds a unique variable not free elsewhere. -/
@[blueprint "chap5__example_5_3_3"]
def exampleRectified_5_3_3 : FormulaN exampleLang_5_3_3 :=
  FormulaN.conj
    (FormulaN.all 2
      (FormulaN.impl
        (FormulaN.predN ExPred_5_3_3.R
          (vec2 (Term.var 2) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P
          (fun _ => Term.var 2))))
    (FormulaN.all 3
      (FormulaN.conj
        (FormulaN.neg
          (FormulaN.predN ExPred_5_3_3.R
            (vec2 (Term.var 0) (Term.var 3))))
        (FormulaN.all 4
          (FormulaN.predN ExPred_5_3_3.P
            (fun _ => Term.var 4)))))

/-- Example 5.3.3: The displayed formula A is logically equivalent to
its rectified counterpart B under every structure and assignment. -/
@[blueprint "chap5__example_5_3_3" (main := true)]
theorem exampleRectified_5_3_3_equiv :
    universallyValidN (FormulaN.equiv exampleNonRectified_5_3_3
      exampleRectified_5_3_3) 

end LCS.FirstOrder.Semantics.Subformulae

namespace LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics

/-- Lemma 5.3.4 (companion): Apply a variable renaming to a term. -/
def termVarMap {L : Language} (sigma : Nat → Nat) : Term L → Term L
  | .var i => .var (sigma i)
  | .const c => .const c
  | .func f ts => .func f (fun j => termVarMap sigma (ts j))

/-- Lemma 5.3.4 (companion): Update a function at a single point. -/
def funUpdate (f : Nat → Nat) (i : Nat) (v : Nat) : Nat → Nat :=
  fun x => if x = i then v else f x

/-- Lemma 5.3.4 (required helper): rectifyAux A sigma n traverses
formula A, renaming each quantifier-bound variable to a fresh counter
starting from n, using sigma to track the accumulated renaming.
Returns (rectified formula, next counter). -/
@[blueprint "chap5__lemma_5_3_4"]
def rectifyAux {L : Language} : FormulaN L → (Nat → Nat) → Nat → FormulaN L × Nat
  | .predN P ts, sigma, n => (.predN P (fun j => termVarMap sigma (ts j)), n)
  | .eq_ hL t1 t2, sigma, n => (.eq_ hL (termVarMap sigma t1) (termVarMap sigma t2), n)
  | .neg A, sigma, n => let (A', n') := rectifyAux A sigma n; (.neg A', n')
  | .conj A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.conj A' B', n'')
  | .disj A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.disj A' B', n'')
  | .impl A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.impl A' B', n'')
  | .all i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAux A sigma' (n + 1)
    (.all n A', n')
  | .ex i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAux A sigma' (n + 1)
    (.ex n A', n')

/-- Lemma 5.3.4 (companion): max over a finite function. -/
def finMax (n : Nat) (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => Nat.max (f ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩)
    (finMax n (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ n)⟩))

/-- Lemma 5.3.4 (companion): Maximum variable index in a term (0 if no
variables). -/
def termMaxVar {L : Language} : Term L → Nat
  | .var i => i
  | .const _ => 0
  | .func f ts => finMax (L.funArity f) (fun j => termMaxVar (ts j))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts, LCS.Herbrand.PrenexForm.Part1
/-- Lemma 5.3.4 (companion): Maximum variable index appearing anywhere
in a formula. -/
def formulaMaxVarN {L : Language} : FormulaN L → Nat
  | .predN P ts => finMax (L.predArity P) (fun j => termMaxVar (ts j))
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .neg A => formulaMaxVarN A
  | .conj A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .disj A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .impl A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .all i A => Nat.max i (formulaMaxVarN A)
  | .ex i A => Nat.max i (formulaMaxVarN A)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.FOResolution.ClauseForm, LCS.Herbrand.HerbrandTheorem.Part2, LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.4 (companion): A recursive function that produces a
rectified formula A' from A by systematically renaming bound variables
to fresh names, avoiding clashes with free variables and previously
used bound variables. -/
def rectify {L : Language} (A : FormulaN L) : FormulaN L :=
  (rectifyAux A id (formulaMaxVarN A + 1)).1

-- ===================================================================
-- Helper lemmas for rectify correctness
-- ===================================================================

-- retained: used by LCS.Herbrand.PrenexForm.Part1
theorem finMax_ge (n : Nat) (f : Fin n → Nat) (j : Fin n) :
    f j ≤ finMax n f := by
-- BEGIN PROOF
  induction n with
  | zero => exact absurd j.isLt (Nat.not_lt_zero _)
  | succ n ih =>
    unfold finMax
    by_cases hjn : j.val = n
    · have hj : j = ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩ := by
        ext; exact hjn
      rw [hj]; exact Nat.le_max_left _ _
    · have hlt : j.val < n :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) hjn
      have := ih (fun i => f ⟨i.val,
        Nat.lt_of_lt_of_le i.isLt (Nat.le_succ n)⟩) ⟨j.val, hlt⟩
      exact Nat.le_trans this (Nat.le_max_right _ _)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem termFV_le_maxVar {L : Language} (t : Term L) :
    ∀ x, x ∈ termFV t → x ≤ termMaxVar t := by
-- BEGIN PROOF
  induction t with
  | var i =>
    intro x hx; unfold termFV at hx; exact Nat.le_of_eq hx
  | const _ => intro x hx; exact absurd hx id
  | func f ts ih =>
    intro x hx; unfold termFV at hx
    obtain ⟨j, hj⟩ := hx
    unfold termMaxVar
    exact Nat.le_trans (ih j x hj)
      (finMax_ge _ (fun j => termMaxVar (ts j)) j)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem formulaFVN_le_maxVarN {L : Language} (A : FormulaN L) :
    ∀ x, x ∈ formulaFVN A → x ≤ formulaMaxVarN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro x hx; simp only [formulaFVN] at hx
    obtain ⟨j, hj⟩ := hx
    unfold formulaMaxVarN
    exact Nat.le_trans (termFV_le_maxVar (ts j) x hj)
      (finMax_ge _ (fun j => termMaxVar (ts j)) j)
  | eq_ _ t1 t2 =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with h1 | h2
    · exact Nat.le_trans (termFV_le_maxVar t1 x h1)
        (Nat.le_max_left _ _)
    · exact Nat.le_trans (termFV_le_maxVar t2 x h2)
        (Nat.le_max_right _ _)
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | disj A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | all i A ih =>
    intro x hx; simp only [formulaFVN] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)
  | ex i A ih =>
    intro x hx; simp only [formulaFVN] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)

-- ===================================================================
-- Lemma 5.3.4: Rectification of full first-order formulae
-- ===================================================================

/-- Lemma 5.3.4 (companion): A counter-based traversal of a full first-order formula,
renaming each quantifier to a fresh index and returning the next unused counter. -/
def rectifyAuxF {L : Language} : Formula L → (Nat → Nat) → Nat → Formula L × Nat
  | .falsum, _, n => (.falsum, n)
  | .pred0 P hP, _, n => (.pred0 P hP, n)
  | .predN P hP ts, sigma, n => (.predN P hP (fun j => termVarMap sigma (ts j)), n)
  | .eq_ hL t1 t2, sigma, n => (.eq_ hL (termVarMap sigma t1) (termVarMap sigma t2), n)
  | .neg A, sigma, n => let (A', n') := rectifyAuxF A sigma n; (.neg A', n')
  | .conj A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.conj A' B', n'')
  | .disj A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.disj A' B', n'')
  | .impl A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.impl A' B', n'')
  | .equiv_ A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.equiv_ A' B', n'')
  | .all i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxF A sigma' (n + 1)
    (.all n A', n')
  | .ex i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxF A sigma' (n + 1)
    (.ex n A', n')

/-- Lemma 5.3.4 (companion): Maximum variable index appearing in a full first-order formula,
including quantifier indices; zero for falsum and rank-zero predicates. -/
def formulaMaxVarF {L : Language} : Formula L → Nat
  | .falsum | .pred0 _ _ => 0
  | .predN P _ ts => finMax (L.predArity P) (fun j => termMaxVar (ts j))
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .neg A => formulaMaxVarF A
  | .conj A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .disj A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .impl A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .equiv_ A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .all i A => Nat.max i (formulaMaxVarF A)
  | .ex i A => Nat.max i (formulaMaxVarF A)

/-- Lemma 5.3.4 (companion): Compute a rectified full first-order formula by starting fresh
quantifier indices above every variable index in the input. -/
@[blueprint "chap5__lemma_5_3_4"]
def rectifyF {L : Language} (A : Formula L) : Formula L :=
  (rectifyAuxF A id (formulaMaxVarF A + 1)).1

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
/-- Evaluating a term after variable renaming is the same as evaluating
the original term under the composed assignment. -/
theorem termVarMap_eval {L : Language} (M : Structure L)
    (s : Assignment M) (sigma : Nat → Nat) (t : Term L) :
    termEval M s (termVarMap sigma t) =
    termEval M (fun x => s (sigma x)) t := by
-- BEGIN PROOF
  induction t with
  | var i => simp [termVarMap, termEval]
  | const c => simp [termVarMap, termEval]
  | func f ts ih =>
    simp only [termVarMap, termEval]
    congr 1; funext j; exact ih j

/-- Lemma 5.3.4(ii): Every full first-order formula is semantically
equivalent to the rectified formula computed by rectifyF. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem rectifyF_equiv {L : Language} (A : Formula L) :
    universallyValid (Formula.equiv_ A (rectifyF A)) 

end LCS.FirstOrder.Semantics.Subformulae
end
