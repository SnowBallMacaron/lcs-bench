import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Equality
import LCS.CutElim.LK
import LCS.CutElim.LKe
import LCS.CutElim.LKe.Equivalence
import Attach
import LCS.Herbrand.SharpenedHauptsatz.ProofsStamp

/-! # Herbrand.SharpenedHauptsatz
    Formalization of Chapter 7, Section 3.1: Pure Variable Proofs
    and the atomic axiom reduction infrastructure.

    Covers Definition 7.3.1, Lemmas 7.3.1-7.3.2, Examples 7.3.1-7.3.2.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.SharpenedHauptsatz

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Equality
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence

/-- An open LK deduction over an explicit list of permitted boundary sequents.
The conclusion is indexed, ordinary axioms require their axiom certificate,
and internal nodes use the legal indexed LK inference constructors. -/
@[blueprint "chap7__example_7_1_1"]
inductive LKOpenDeductionTree {L : Language} (boundary : List (Sequent L)) :
    Sequent L → Type where
  | openLeaf (s : Sequent L) (h : s ∈ boundary) : LKOpenDeductionTree boundary s
  | axiom_ (s : Sequent L) (h : isFOLKAxiom s) : LKOpenDeductionTree boundary s
  | onePremise {p c : Sequent L} (rule : FOLKStep1 p c)
      (sub : LKOpenDeductionTree boundary p) : LKOpenDeductionTree boundary c
  | twoPremise {p q c : Sequent L} (rule : FOLKStep2 p q c)
      (left : LKOpenDeductionTree boundary p)
      (right : LKOpenDeductionTree boundary q) : LKOpenDeductionTree boundary c

/-- Example 7.1.1 (companion): The equality-free language of the PDF fragment.
The unary function symbols false/true denote f/g, the unary predicate symbols
false/true denote P/Q, and the sole constant denotes a. -/
@[blueprint "chap7__example_7_1_1"]
def openExampleLang_7_1_1 : Language where
  funSymbols := Bool
  funArity := fun _ => 1
  constSymbols := Unit
  predSymbols := Bool
  predArity := fun _ => 1
  hasEquality := false

/-- Example 7.1.1 (companion): The nonidentity left boundary P(a) → Q(f(g(a)))
of the complete PDF deduction. It is an open premise of the fragment. -/
@[blueprint "chap7__example_7_1_1"]
def openBoundary_7_1_1 : Sequent openExampleLang_7_1_1 :=
  let a : Term openExampleLang_7_1_1 := .const ()
  let ga : Term openExampleLang_7_1_1 := .func true (fun _ => a)
  let fga : Term openExampleLang_7_1_1 := .func false (fun _ => ga)
  ⟨[.predN false (fun _ => a)], [.predN true (fun _ => fga)]⟩

/-- Example 7.1.1 (companion): The term g(a) substituted for x. -/
@[blueprint "chap7__example_7_1_1"]
def openExampleGa_7_1_1 : Term openExampleLang_7_1_1 :=
  .func true (fun _ => .const ())

/-- Example 7.1.1 (companion): The atomic left boundary formula P(a). -/
@[blueprint "chap7__example_7_1_1"]
def openExamplePa_7_1_1 : FormulaN openExampleLang_7_1_1 :=
  .predN false (fun _ => .const ())

/-- Example 7.1.1 (companion): The matrix Q(f(x)), with x represented by 0. -/
@[blueprint "chap7__example_7_1_1"]
def openExampleQfx_7_1_1 : FormulaN openExampleLang_7_1_1 :=
  .predN true (fun _ => .func false (fun _ => .var 0))

/-- Example 7.1.1 (companion): The instance Q(f(g(a))). -/
@[blueprint "chap7__example_7_1_1"]
def openExampleQfga_7_1_1 : FormulaN openExampleLang_7_1_1 :=
  .predN true (fun _ => .func false (fun _ => openExampleGa_7_1_1))

/-- Example 7.1.1 (companion): The right identity boundary. -/
@[blueprint "chap7__example_7_1_1"]
def openRightBoundary_7_1_1 : Sequent openExampleLang_7_1_1 :=
  ⟨[openExampleQfga_7_1_1], [openExampleQfga_7_1_1]⟩

/-- Example 7.1.1 (companion): The printed end sequent
P(a) ∨ ∀x Q(f(x)) → Q(f(g(a))). -/
@[blueprint "chap7__example_7_1_1"]
def openConclusion_7_1_1 : Sequent openExampleLang_7_1_1 :=
  ⟨[.disj openExamplePa_7_1_1 (.all 0 openExampleQfx_7_1_1)],
    [openExampleQfga_7_1_1]⟩

/-- Example 7.1.1: The complete PDF open deduction. Its left leaf is the
open premise P(a) → Q(f(g(a))); its right identity leaf feeds all-left with
g(a) for x in Q(f(x)); or-left combines the branches at the printed end sequent. -/
@[blueprint "chap7__example_7_1_1" (main := true)]
def openDeductionExample_7_1_1 :
    LKOpenDeductionTree [openBoundary_7_1_1] openConclusion_7_1_1 :=
  .twoPremise (.orLeft openExamplePa_7_1_1 (.all 0 openExampleQfx_7_1_1)
      [] [openExampleQfga_7_1_1])
    (.openLeaf openBoundary_7_1_1 (by simp))
    (.onePremise (.allLeft openExampleGa_7_1_1 0 openExampleQfx_7_1_1
        [] [openExampleQfga_7_1_1] True.intro)
      (.axiom_ openRightBoundary_7_1_1 ⟨openExampleQfga_7_1_1, rfl, rfl⟩))



/-- Example 7.1.1 (companion): Applying or-left first to the two original
boundary sequents yields this attempted-exchange intermediate sequent. -/
@[blueprint "chap7__example_7_1_1"]
def openSwapBoundary_7_1_1 : Sequent openExampleLang_7_1_1 :=
  ⟨[.disj openExamplePa_7_1_1 openExampleQfga_7_1_1], [openExampleQfga_7_1_1]⟩



/-- Example 7.1.1 (companion): Boundary conditions for an ordinary all-left
rule to finish the attempted local exchange. The substitution must be free-for,
its premise must be the or-left-first output, and its conclusion must be the
original end sequent. These are candidate-rule data, not a deduction constructor. -/
@[blueprint "chap7__example_7_1_1"]
def openSwapAllLeftFits_7_1_1 : Prop :=
  ∃ (t : Term openExampleLang_7_1_1) (x : Nat)
    (A : FormulaN openExampleLang_7_1_1) (Γ Δ : List (FormulaN openExampleLang_7_1_1)),
    isFreeForN t x A ∧
    openSwapBoundary_7_1_1 = ⟨formulaSubstN A t x :: Γ, Δ⟩ ∧
    openConclusion_7_1_1 = ⟨.all x A :: Γ, Δ⟩

/-- Example 7.1.1 (companion theorem): The attempted boundary-preserving
exchange cannot finish with ordinary all-left: the end antecedent has a
whole disjunction, whereas all-left concludes with a whole universal formula. -/
@[blueprint "chap7__example_7_1_1"]
theorem failedLocalExchange_7_1_1 : ¬ openSwapAllLeftFits_7_1_1 

/-- Example 7.1.1 (companion theorem): The wanted universal formula is a
proper right subformula of the end disjunction, rather than a whole antecedent
formula on which ordinary all-left can act. -/
@[blueprint "chap7__example_7_1_1"]
theorem openExample_properSubformula_7_1_1 :
    FirstOrder.Semantics.Subformulae.IsSubformula
      (.all 0 openExampleQfx_7_1_1)
      (.disj openExamplePa_7_1_1 (.all 0 openExampleQfx_7_1_1)) ∧
    (FormulaN.all 0 openExampleQfx_7_1_1) ≠
      (FormulaN.disj openExamplePa_7_1_1 (.all 0 openExampleQfx_7_1_1)) 

-- ===================================================================
-- Example 7.3.1 (companion type): ExViolationPred
-- ===================================================================

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Example 7.3.1 (companion type): Predicate symbols for the eigenvariable violation example. P is a unary predicate, Q is a unary predicate (standing in for the propositional symbol Q in the textbook, since FormulaN lacks zero-arity pred0 constructors), and R is a unary predicate. These are used to construct the proof tree Gamma -> P(y), Q(z0) by forall-right yielding Gamma -> forall x P(x), Q(z0), combined with and-right to produce Gamma -> forall x P(x), Q(z0) /\ R(y), which demonstrates the eigenvariable condition violation when one attempts to permute and-right above forall-right. -/
inductive ExViolationPred : Type where
  /-- Unary predicate P -/
  | P : ExViolationPred
  /-- Unary predicate Q (textbook uses propositional Q, but FormulaN
      requires predicates to have at least one argument) -/
  | Q : ExViolationPred
  /-- Unary predicate R -/
  | R : ExViolationPred

-- ===================================================================
-- Example 7.3.1 (companion def): exViolationLang
-- ===================================================================



-- ===================================================================
-- Example 7.3.1 (companion def): eigenvariableViolationConclusionSeq
-- ===================================================================



-- ===================================================================
-- Example 7.3.1: eigenvariableViolationTree
-- ===================================================================

/-- Example 7.3.1 (companion): The two schematic open premises. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableExamplePremises {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) : List (Sequent L) :=
  [⟨Γ, [formulaSubstN P (.var y) x, Q]⟩, ⟨Γ, [.all x P, R]⟩]

/-- Example 7.3.1 (companion): The common end sequent of the two diagrams. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableExampleConclusion {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x : Nat) : Sequent L :=
  ⟨Γ, [.all x P, .conj Q R]⟩

/-- Example 7.3.1: The original legal open fragment for every schematic
instantiation satisfying the actual all-right side conditions. Exchanges put
the selected formula last for all-right, then restore the printed order before
and-right. The two printed premises remain open. -/
@[blueprint "chap7__example_7_3_1" (main := true)]
def eigenvariableViolationTree {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat)
    (hfree : isFreeForN (.var y) x P)
    (hfresh : ∀ F ∈ Γ ++ [Q, .all x P], y ∉ formulaFVN F) :
    LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x y)
      (eigenvariableExampleConclusion Γ P Q R x) :=
  .twoPremise (.andRight Q R Γ [.all x P])
    (.onePremise (.exchangeRight Γ [] Q (.all x P) [])
      (.onePremise (.allRight y x P Γ [Q] hfresh hfree)
        (.onePremise (.exchangeRight Γ [] (formulaSubstN P (.var y) x) Q [])
          (.openLeaf ⟨Γ, [formulaSubstN P (.var y) x, Q]⟩
            (by simp [eigenvariableExamplePremises])))))
    (.openLeaf ⟨Γ, [.all x P, R]⟩ (by simp [eigenvariableExamplePremises]))

/-- Example 7.3.1 (companion): The legal upper part of the attempted swap.
Both open premises are retained. Weakening and exchanges yield the printed
branches Γ → P(y), ∀xP(x), Q and Γ → P(y), ∀xP(x), R(y), then and-right. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableSwapUpper {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) :
    LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x y)
      ⟨Γ, [formulaSubstN P (.var y) x, .all x P, .conj Q R]⟩ :=
  let Py := formulaSubstN P (.var y) x
  let All := FormulaN.all x P
  .twoPremise (.andRight Q R Γ [Py, All])
    (.onePremise (.exchangeRight Γ [Py] Q All [])
      (.onePremise (.weakenRight All Γ [Py, Q])
        (.openLeaf ⟨Γ, [Py, Q]⟩ (by simp [eigenvariableExamplePremises, Py]))))
    (.onePremise (.exchangeRight Γ [] All Py [R])
      (.onePremise (.exchangeRight Γ [All] R Py [])
        (.onePremise (.weakenRight Py Γ [All, R])
          (.openLeaf ⟨Γ, [All, R]⟩ (by simp [eigenvariableExamplePremises, All])))))

/-- Example 7.3.1 (companion): Explicit exchanges place P(y) last, as required
by the indexed all-right constructor at the attempted lower inference. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableSwapBeforeForall {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) :
    LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x y)
      ⟨Γ, [.all x P, .conj Q R, formulaSubstN P (.var y) x]⟩ :=
  .onePremise (.exchangeRight Γ [.all x P] (formulaSubstN P (.var y) x) (.conj Q R) [])
    (.onePremise (.exchangeRight Γ [] (formulaSubstN P (.var y) x) (.all x P) [.conj Q R])
      (eigenvariableSwapUpper Γ P Q R x y))

/-- Example 7.3.1 (companion): The candidate lower all-right conclusion,
with its principal formula last. Exchange displays it as ∀xP(x), ∀xP(x), Q∧R(y). -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableSwapAfterForall {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x : Nat) : Sequent L :=
  ⟨Γ, [.all x P, .conj Q R, .all x P]⟩

/-- Example 7.3.1 (companion): The legal contraction tail, conditional on
its displayed open boundary. Exchanges expose the duplicated universal formula
at the end for contraction and restore the original printed conclusion. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableSwapTail {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x : Nat) :
    LKOpenDeductionTree [eigenvariableSwapAfterForall Γ P Q R x]
      (eigenvariableExampleConclusion Γ P Q R x) :=
  let All := FormulaN.all x P
  let C := FormulaN.conj Q R
  let printed : LKOpenDeductionTree [eigenvariableSwapAfterForall Γ P Q R x]
      ⟨Γ, [All, All, C]⟩ :=
    .onePremise (.exchangeRight Γ [All] C All [])
      (.openLeaf (eigenvariableSwapAfterForall Γ P Q R x) (by simp))
  .onePremise (.exchangeRight Γ [] C All [])
    (.onePremise (.contractRight All Γ [C])
      (.onePremise (.exchangeRight Γ [] All C [All])
        (.onePremise (.exchangeRight Γ [All] All C []) printed)))

/-- Example 7.3.1 (companion theorem): The lower all-right eigenvariable
condition fails: y occurs in the retained R(y) inside Q∧R(y) in its conclusion. -/
@[blueprint "chap7__example_7_3_1" (main := true)]
theorem eigenvariableSwapFreshnessFails {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) (hyR : y ∈ formulaFVN R) :
    ¬ (∀ F ∈ Γ ++ ([.all x P, .conj Q R] ++ [.all x P]), y ∉ formulaFVN F) 

/-- Example 7.3.1 (companion data): The attempted printed fragment stores
its legal upper part and contraction tail around the candidate all-right step.
The endpoints are precisely the premise/conclusion of allRight y x P Γ
[∀xP, Q∧R]; free-for holds but freshness is refuted. It is not a legal deduction
constructor across that missing inference. -/
@[blueprint "chap7__example_7_3_1"]
structure EigenvariableSwapAttempt {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) where
  beforeQuantifier : LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x y)
    ⟨Γ, [.all x P, .conj Q R, formulaSubstN P (.var y) x]⟩
  afterQuantifier : LKOpenDeductionTree [eigenvariableSwapAfterForall Γ P Q R x]
    (eigenvariableExampleConclusion Γ P Q R x)
  freeFor : isFreeForN (.var y) x P
  freshnessFails :
    ¬ (∀ F ∈ Γ ++ ([.all x P, .conj Q R] ++ [.all x P]), y ∉ formulaFVN F)

/-- Example 7.3.1 (companion): The complete attempted swap as boundary/rule
parameters and concrete legal pieces, together with the failed side condition. -/
@[blueprint "chap7__example_7_3_1"]
def eigenvariableIllegalSwap {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x y : Nat) (hfree : isFreeForN (.var y) x P)
    (hyR : y ∈ formulaFVN R) : EigenvariableSwapAttempt Γ P Q R x y where
  beforeQuantifier := eigenvariableSwapBeforeForall Γ P Q R x y
  afterQuantifier := eigenvariableSwapTail Γ P Q R x
  freeFor := hfree
  freshnessFails := eigenvariableSwapFreshnessFails Γ P Q R x y hyR





-- ===================================================================
-- Example 7.3.2: pureVariableRenamedTree
-- ===================================================================

/-- Example 7.3.2: Rename the eigenvariable in the P branch to z.
The open premises are Γ → P(z), Q and the unchanged Γ → ∀xP(x), R(y),
where R is the fixed formula R(y). The end sequent is unchanged. -/
@[blueprint "chap7__example_7_3_2"]
def pureVariableRenamedTree {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x z : Nat)
    (hfree : isFreeForN (.var z) x P)
    (hfresh : ∀ F ∈ Γ ++ [Q, .all x P], z ∉ formulaFVN F) :
    LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x z)
      (eigenvariableExampleConclusion Γ P Q R x) :=
  eigenvariableViolationTree Γ P Q R x z hfree hfresh

/-- Example 7.3.2 (companion): The lawful swapped fragment, with conjunction
above all-right. The original R(y) is retained; z is fresh also in Q∧R(y).
Weakening, exchange and contraction implement the suppressed structural rules. -/
@[blueprint "chap7__example_7_3_2" (main := true)]
def permutedLegalTree {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x z : Nat)
    (hfree : isFreeForN (.var z) x P)
    (hfresh : ∀ F ∈ Γ ++ ([.all x P, .conj Q R] ++ [.all x P]),
      z ∉ formulaFVN F) :
    LKOpenDeductionTree (eigenvariableExamplePremises Γ P Q R x z)
      (eigenvariableExampleConclusion Γ P Q R x) :=
  let All := FormulaN.all x P
  let C := FormulaN.conj Q R
  let quantified := LKOpenDeductionTree.onePremise
    (.allRight z x P Γ [All, C] hfresh hfree)
    (eigenvariableSwapBeforeForall Γ P Q R x z)
  let printed := LKOpenDeductionTree.onePremise
    (.exchangeRight Γ [All] C All []) quantified
  .onePremise (.exchangeRight Γ [] C All [])
    (.onePremise (.contractRight All Γ [C])
      (.onePremise (.exchangeRight Γ [] All C [All])
        (.onePremise (.exchangeRight Γ [All] All C []) printed)))

-- ===================================================================
-- Definition 7.3.1 (companion def): proofTreeFormulae
-- ===================================================================

/-- Definition 7.3.1 (companion def): Collects all formulae appearing in all sequents of the LK proof tree (both antecedents and succedents at every node). Under the indexed `FOLKProofTree`, the conclusion of a node is its type index, so we pair the index `s` with the tree when recursing. -/
@[blueprint "chap7__definition_7_3_1"]
def proofTreeFormulae {L : Language} :
    {s : Sequent L} → FOLKProofTree s → List (FormulaN L)
  | s, .axiom_ _ _ => s.antecedent ++ s.succedent
  | s, .onePremise _ t =>
    (s.antecedent ++ s.succedent) ++ proofTreeFormulae t
  | s, .twoPremise _ t1 t2 =>
    (s.antecedent ++ s.succedent) ++
      proofTreeFormulae t1 ++ proofTreeFormulae t2

-- ===================================================================
-- Definition 7.3.1 (companion def): termVariables
-- ===================================================================

/-- Definition 7.3.1 (companion def): The set of all variables (free or bound) occurring in a term. Since terms have no binders, all variables in a term are free. -/
@[blueprint "chap7__definition_7_3_1"]
def termVariables {L : Language} : Term L → Set Nat
  | .var i => Set.singleton i
  | .const _ => ∅
  | .func f ts =>
    Set.iUnion (fun (j : Fin (L.funArity f)) => termVariables (ts j))

-- ===================================================================
-- Definition 7.3.1 (companion def): formulaAllVariables
-- ===================================================================

/-- Definition 7.3.1 (companion def): The set of all variables (free and bound) occurring in a FormulaN. Unlike formulaFVN, this includes bound variables from quantifiers. -/
@[blueprint "chap7__definition_7_3_1"]
def formulaAllVariables {L : Language} : FormulaN L → Set Nat
  | .predN P ts =>
    Set.iUnion (fun (j : Fin (L.predArity P)) => termVariables (ts j))
  | .eq_ _ t1 t2 => termVariables t1 ∪ termVariables t2
  | .neg A => formulaAllVariables A
  | .conj A B => formulaAllVariables A ∪ formulaAllVariables B
  | .disj A B => formulaAllVariables A ∪ formulaAllVariables B
  | .impl A B => formulaAllVariables A ∪ formulaAllVariables B
  | .all i A => Set.singleton i ∪ formulaAllVariables A
  | .ex i A => Set.singleton i ∪ formulaAllVariables A

/-- Actual nodes of an open deduction, with unary/left edge 0 and right edge 1.
The eigenvariable label belongs to its introducing inference. -/
@[blueprint "chap7__definition_7_3_1"]
def LKOpenDeductionTree.nodes {L : Language} {boundary : List (Sequent L)} :
    {s : Sequent L} → LKOpenDeductionTree boundary s → List Nat →
      List (List Nat × Sequent L × Option Nat)
  | s, .openLeaf _ _, a => [(a, s, none)]
  | s, .axiom_ _ _, a => [(a, s, none)]
  | s, .onePremise rule sub, a =>
    (a, s, match rule with
      | .allRight y _ _ _ _ _ _ => some y
      | .exLeft y _ _ _ _ _ _ => some y
      | _ => none) :: sub.nodes (a ++ [0])
  | s, .twoPremise _ left right, a =>
    (a, s, none) :: (left.nodes (a ++ [0]) ++ right.nodes (a ++ [1]))

/-- The two clauses of pure-variable proofs on actual open-fragment nodes:
per-formula free/bound separation and all-occurrence premise-subtree locality. -/
@[blueprint "chap7__definition_7_3_1"]
def LKOpenDeductionTree.IsPure {L : Language} {boundary : List (Sequent L)}
    {s : Sequent L} (t : LKOpenDeductionTree boundary s) : Prop :=
  ∀ a seq y, (a, seq, some y) ∈ t.nodes [] →
    (∀ b q e, (b, q, e) ∈ t.nodes [] → ∀ F ∈ q.antecedent ++ q.succedent,
      ¬ (y ∈ formulaFVN F ∧ y ∈ formulaBVN F)) ∧
    (∀ b q e, (b, q, e) ∈ t.nodes [] → ∀ F ∈ q.antecedent ++ q.succedent,
      y ∈ formulaAllVariables F → ∃ suffix, b = a ++ [0] ++ suffix)

/-- Example 7.3.2 (companion theorem): Fresh z has no free or bound occurrence
in the original matrix or retained context. Both displayed fragments then
satisfy the actual-node pure-variable condition, including the open leaves.
The two free-occurrence conditions are precisely those used by their legal
all-right constructors; R remains fixed throughout. -/
@[attach_debt, blueprint "chap7__example_7_3_2" (main := true)]
theorem renamedAndPermutedPure {L : Language} (Γ : List (FormulaN L))
    (P Q R : FormulaN L) (x z : Nat) (hfree : isFreeForN (.var z) x P)
    (hbefore : ∀ F ∈ Γ ++ [Q, .all x P], z ∉ formulaFVN F)
    (hafter : ∀ F ∈ Γ ++ ([.all x P, .conj Q R] ++ [.all x P]),
      z ∉ formulaFVN F)
    (hfresh : ∀ F ∈ Γ ++ [P, Q, R, .all x P], z ∉ formulaAllVariables F) :
    (pureVariableRenamedTree Γ P Q R x z hfree hbefore).IsPure ∧
    (permutedLegalTree Γ P Q R x z hfree hafter).IsPure 



-- ===================================================================
-- Definition 7.3.1 (companion def): proofTreeVariables
-- ===================================================================



/-- Definition 7.3.1 (companion def): The sequent at an actual proof-node
address and the eigenvariable introduced there, if any. Unary/left edges are
0 and right edges are 1. An embedded G root is the same sequent occurrence
in G=; equality premises retain the canonical appended-last frames. -/
@[blueprint "chap7__definition_7_3_1"]
def lkPurityNodeAt {L : Language} :
    {s : Sequent L} → FOLKProofTree s → List Nat → Option (Sequent L × Option Nat)
  | s, .axiom_ _ _, [] => some (s, none)
  | s, .onePremise rule _, [] =>
    some (s, match rule with
      | .allRight y _ _ _ _ _ _ => some y
      | .exLeft y _ _ _ _ _ _ => some y
      | _ => none)
  | s, .twoPremise _ _ _, [] => some (s, none)
  | _, .onePremise _ t, 0 :: p => lkPurityNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkPurityNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkPurityNodeAt t p
  | _, _, _ => none

/-- Definition 7.3.1 (companion def): A free or bound occurrence of `y`
at a specified node, witnessed by a formula position in that node's sequent.
Equal formula values at different nodes remain separate occurrences. -/
@[blueprint "chap7__definition_7_3_1"]
def lkVariableOccursAt {L : Language} {s : Sequent L}
    (outer : FOLKProofTree s) (y : Nat) (address : List Nat) : Prop :=
  ∃ seq eigen, lkPurityNodeAt outer address = some (seq, eigen) ∧
    ∃ i : Fin (seq.antecedent ++ seq.succedent).length,
      Membership.mem (formulaAllVariables ((seq.antecedent ++ seq.succedent).get i)) y

/-- Definition 7.3.1 (companion def): The sequent at an actual proof-node
address and the eigenvariable introduced there, if any. Unary/left edges are
0 and right edges are 1. An embedded G root is the same sequent occurrence
in G=; equality premises retain the canonical appended-last frames. -/
@[blueprint "chap7__definition_7_3_1"]
def gPurityNodeAt {L : Language} :
    {s : Sequent L} → GProofTreeExt s → List Nat → Option (Sequent L × Option Nat)
  | s, .axiom_ _ _, [] => some (s, none)
  | s, .onePremise rule _, [] =>
    some (s, match rule with
      | .allRight y _ _ _ _ _ _ _ => some y
      | .exLeft y _ _ _ _ _ _ _ => some y
      | _ => none)
  | s, .twoPremise _ _ _, [] => some (s, none)
  | _, .onePremise _ t, 0 :: p => gPurityNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => gPurityNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gPurityNodeAt t p
  | _, _, _ => none

/-- Definition 7.3.1 (companion def): A free or bound occurrence of `y`
at a specified node, witnessed by a formula position in that node's sequent.
Equal formula values at different nodes remain separate occurrences. -/
@[blueprint "chap7__definition_7_3_1"]
def gVariableOccursAt {L : Language} {s : Sequent L}
    (outer : GProofTreeExt s) (y : Nat) (address : List Nat) : Prop :=
  ∃ seq eigen, gPurityNodeAt outer address = some (seq, eigen) ∧
    ∃ i : Fin (seq.antecedent ++ seq.succedent).length,
      Membership.mem (formulaAllVariables ((seq.antecedent ++ seq.succedent).get i)) y

/-- Definition 7.3.1 (companion def): The sequent at an actual proof-node
address and the eigenvariable introduced there, if any. Unary/left edges are
0 and right edges are 1. An embedded G root is the same sequent occurrence
in G=; equality premises retain the canonical appended-last frames. -/
@[blueprint "chap7__definition_7_3_1"]
def lkePurityNodeAt {L : Language} :
    {s : Sequent L} → LKeProofTree s → List Nat → Option (Sequent L × Option Nat)
  | s, .axiom_ _ _, [] => some (s, none)
  | _, .eqAxiom hL ax, [] => some (ax.toSequent hL, none)
  | s, .onePremise rule _, [] =>
    some (s, match rule with
      | .allRight y _ _ _ _ _ _ => some y
      | .exLeft y _ _ _ _ _ _ => some y
      | _ => none)
  | s, .twoPremise _ _ _, [] => some (s, none)
  | _, .onePremise _ t, 0 :: p => lkePurityNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkePurityNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkePurityNodeAt t p
  | _, _, _ => none

/-- Definition 7.3.1 (companion def): A free or bound occurrence of `y`
at a specified node, witnessed by a formula position in that node's sequent.
Equal formula values at different nodes remain separate occurrences. -/
@[blueprint "chap7__definition_7_3_1"]
def lkeVariableOccursAt {L : Language} {s : Sequent L}
    (outer : LKeProofTree s) (y : Nat) (address : List Nat) : Prop :=
  ∃ seq eigen, lkePurityNodeAt outer address = some (seq, eigen) ∧
    ∃ i : Fin (seq.antecedent ++ seq.succedent).length,
      Membership.mem (formulaAllVariables ((seq.antecedent ++ seq.succedent).get i)) y

/-- Definition 7.3.1 (companion def): The sequent at an actual proof-node
address and the eigenvariable introduced there, if any. Unary/left edges are
0 and right edges are 1. An embedded G root is the same sequent occurrence
in G=; equality premises retain the canonical appended-last frames. -/
@[blueprint "chap7__definition_7_3_1"]
def gEqPurityNodeAt {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → List Nat → Option (Sequent L × Option Nat)
  | _, .base g, p => gPurityNodeAt g p
  | s, .axiom_ _ _, [] => some (s, none)
  | s, .onePremise rule _, [] =>
    some (s, match rule with
      | .allRight y _ _ _ _ _ _ _ => some y
      | .exLeft y _ _ _ _ _ _ _ => some y
      | _ => none)
  | s, .twoPremise _ _ _, [] => some (s, none)
  | _, .onePremise _ t, 0 :: p => gEqPurityNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => gEqPurityNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gEqPurityNodeAt t p
  | s, .eqRefl _ _ _ _, [] => some (s, none)
  | _, .eqRefl _ _ _ sub, 0 :: p => gEqPurityNodeAt sub p
  | s, .eqFuncCong _ _ _ _ _ _, [] => some (s, none)
  | _, .eqFuncCong _ _ _ _ _ sub, 0 :: p => gEqPurityNodeAt sub p
  | s, .eqPredCong _ _ _ _ _ _, [] => some (s, none)
  | _, .eqPredCong _ _ _ _ _ sub, 0 :: p => gEqPurityNodeAt sub p
  | s, .eqGeneral _ _ _ _ _ _, [] => some (s, none)
  | _, .eqGeneral _ _ _ _ _ sub, 0 :: p => gEqPurityNodeAt sub p
  | _, _, _ => none

/-- Definition 7.3.1 (companion def): A free or bound occurrence of `y`
at a specified node, witnessed by a formula position in that node's sequent.
Equal formula values at different nodes remain separate occurrences. -/
@[blueprint "chap7__definition_7_3_1"]
def gEqVariableOccursAt {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (outer : GEqProofTree hL s) (y : Nat) (address : List Nat) : Prop :=
  ∃ seq eigen, gEqPurityNodeAt outer address = some (seq, eigen) ∧
    ∃ i : Fin (seq.antecedent ++ seq.succedent).length,
      Membership.mem (formulaAllVariables ((seq.antecedent ++ seq.succedent).get i)) y

-- ===================================================================
-- Definition 7.3.1 (companion def): eigenvariableOccursOnlyInSubtree
-- ===================================================================

/-- Definition 7.3.1 (companion def): At the specified introducing inference, all free and bound occurrences of its eigenvariable lie in the upper subtree. Addresses distinguish repeated formula values and repeated subtrees in the fixed proof. -/
@[blueprint "chap7__definition_7_3_1"]
def eigenvariableOccursOnlyInSubtree {L : Language}
    {s : Sequent L} (y : Nat) (introAddress : List Nat)
    (fullTree : FOLKProofTree s) : Prop :=
  (∃ seq, lkPurityNodeAt fullTree introAddress = some (seq, some y)) ∧
  ∀ address, lkVariableOccursAt fullTree y address →
    ∃ suffix, address = introAddress ++ [0] ++ suffix

-- ===================================================================
-- Definition 7.3.1 (companion def): noFreeBoundOverlap
-- ===================================================================

/-- Definition 7.3.1 (companion def): Predicate asserting that variable y does not occur both free and bound in any single formula in the LK proof tree. -/
@[blueprint "chap7__definition_7_3_1"]
def noFreeBoundOverlap {L : Language}
    {s : Sequent L} (y : Nat) (tree : FOLKProofTree s) : Prop :=
  ∀ (f : FormulaN L),
    f ∈ proofTreeFormulae tree →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

-- ===================================================================
-- Definition 7.3.1: IsPureVariableProofLK
-- ===================================================================

/-- Definition 7.3.1 (companion helper): Classify introducing inferences below an address, retaining the whole outer proof for both purity clauses. Embedded G proofs retain their location in the outer G= proof; equality premises retain their canonical sequents. -/
@[blueprint "chap7__definition_7_3_1"]
def isPureVariableProofLKAux {L : Language}
    {root : Sequent L} (outer : FOLKProofTree root) (address : List Nat) : Prop :=
  ∀ suffix seq y,
    lkPurityNodeAt outer (address ++ suffix) = some (seq, some y) →
    noFreeBoundOverlap y outer ∧
    eigenvariableOccursOnlyInSubtree y (address ++ suffix) outer

/-- Definition 7.3.1: Pure-variable proofs in LK. Every actual eigenvariable inference satisfies per-formula free/bound separation throughout the proof, and every free or bound occurrence is at a node in its premise subtree. The fixed outer proof is classified from its root address; embedded G nodes remain part of the enclosing G= proof. -/
@[blueprint "chap7__definition_7_3_1" (main := true)]
def IsPureVariableProofLK {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) : Prop :=
  isPureVariableProofLKAux T []

-- ===================================================================
-- Definition 7.3.1 (companion def): IsPureVariableProofG
-- ===================================================================

/-- Definition 7.3.1 (companion def): Collects all formulae appearing
    in all sequents of an indexed G proof tree. -/
@[blueprint "chap7__definition_7_3_1"]
def gProofTreeFormulae {L : Language} :
    {s : Sequent L} → GProofTreeExt s → List (FormulaN L)
  | s, .axiom_ _ _ => s.antecedent ++ s.succedent
  | s, .onePremise _ t =>
    (s.antecedent ++ s.succedent) ++ gProofTreeFormulae t
  | s, .twoPremise _ t1 t2 =>
    (s.antecedent ++ s.succedent) ++
      gProofTreeFormulae t1 ++ gProofTreeFormulae t2

/-- Definition 7.3.1 (companion def): Helper predicate for checking the no-free-bound-overlap condition on a list of formulae from a G proof tree. -/
@[blueprint "chap7__definition_7_3_1"]
def gNoFreeBoundOverlap {L : Language}
    {s : Sequent L} (y : Nat) (tree : GProofTreeExt s) : Prop :=
  ∀ (f : FormulaN L),
    f ∈ gProofTreeFormulae tree →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

/-- Definition 7.3.1 (companion def): At the specified introducing inference, all free and bound occurrences of its eigenvariable lie in the upper subtree. Addresses distinguish repeated formula values and repeated subtrees in the fixed proof. -/
@[blueprint "chap7__definition_7_3_1"]
def gEigenvariableOccursOnlyInSubtree {L : Language}
    {s : Sequent L} (y : Nat) (introAddress : List Nat)
    (fullTree : GProofTreeExt s) : Prop :=
  (∃ seq, gPurityNodeAt fullTree introAddress = some (seq, some y)) ∧
  ∀ address, gVariableOccursAt fullTree y address →
    ∃ suffix, address = introAddress ++ [0] ++ suffix

/-- Definition 7.3.1 (companion helper): Classify introducing inferences below an address, retaining the whole outer proof for both purity clauses. Embedded G proofs retain their location in the outer G= proof; equality premises retain their canonical sequents. -/
@[blueprint "chap7__definition_7_3_1"]
def isPureVariableProofGAux {L : Language}
    {root : Sequent L} (outer : GProofTreeExt root) (address : List Nat) : Prop :=
  ∀ suffix seq y,
    gPurityNodeAt outer (address ++ suffix) = some (seq, some y) →
    gNoFreeBoundOverlap y outer ∧
    gEigenvariableOccursOnlyInSubtree y (address ++ suffix) outer

/-- Definition 7.3.1: Pure-variable proofs in G. Every actual eigenvariable inference satisfies per-formula free/bound separation throughout the proof, and every free or bound occurrence is at a node in its premise subtree. The fixed outer proof is classified from its root address; embedded G nodes remain part of the enclosing G= proof. -/
@[blueprint "chap7__definition_7_3_1" (main := true)]
def IsPureVariableProofG {L : Language} {s : Sequent L}
    (T : GProofTreeExt s) : Prop :=
  isPureVariableProofGAux T []


-- ===================================================================
-- Definition 7.3.1 (companion def): IsPureVariableProofGEq
-- ===================================================================

/-- Definition 7.3.1 (companion def): Collects all formulae appearing
    in all sequents of an indexed G_= proof tree. -/
@[blueprint "chap7__definition_7_3_1"]
def gEqProofTreeFormulae {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → List (FormulaN L)
  | s, .base g => s.antecedent ++ s.succedent ++ gProofTreeFormulae g
  | s, .axiom_ _ _ => s.antecedent ++ s.succedent
  | s, .onePremise _ sub =>
    (s.antecedent ++ s.succedent) ++ gEqProofTreeFormulae sub
  | s, .twoPremise _ sub1 sub2 =>
    (s.antecedent ++ s.succedent) ++
      gEqProofTreeFormulae sub1 ++ gEqProofTreeFormulae sub2
  | _, .eqRefl _ Γ Δ sub =>
    (Γ ++ Δ) ++ gEqProofTreeFormulae sub
  | _, .eqFuncCong _ _ _ Γ Δ sub =>
    (Γ ++ Δ) ++ gEqProofTreeFormulae sub
  | _, .eqPredCong _ _ _ Γ Δ sub =>
    (Γ ++ Δ) ++ gEqProofTreeFormulae sub
  | _, .eqGeneral _ _ _ Γ Δ sub =>
    (Γ ++ Δ) ++ gEqProofTreeFormulae sub

/-- Definition 7.3.1 (companion def): Helper predicate for checking the no-free-bound-overlap condition on a list of formulae from a G_= proof tree. Mirrors `gNoFreeBoundOverlap` but operates on `gEqProofTreeFormulae`. -/
@[blueprint "chap7__definition_7_3_1"]
def gEqNoFreeBoundOverlap {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} (y : Nat) (tree : GEqProofTree hL s) : Prop :=
  ∀ (f : FormulaN L),
    f ∈ gEqProofTreeFormulae tree →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

/-- Definition 7.3.1 (companion def): At the specified introducing inference, all free and bound occurrences of its eigenvariable lie in the upper subtree. Addresses distinguish repeated formula values and repeated subtrees in the fixed proof. -/
@[blueprint "chap7__definition_7_3_1"]
def gEqEigenvariableOccursOnlyInSubtree {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} (y : Nat) (introAddress : List Nat)
    (fullTree : GEqProofTree hL s) : Prop :=
  (∃ seq, gEqPurityNodeAt fullTree introAddress = some (seq, some y)) ∧
  ∀ address, gEqVariableOccursAt fullTree y address →
    ∃ suffix, address = introAddress ++ [0] ++ suffix

/-- Definition 7.3.1 (companion helper): Classify introducing inferences below an address, retaining the whole outer proof for both purity clauses. Embedded G proofs retain their location in the outer G= proof; equality premises retain their canonical sequents. -/
@[blueprint "chap7__definition_7_3_1"]
def isPureVariableProofGEqAux {L : Language} {hL : L.hasEquality = true}
    {root : Sequent L} (outer : GEqProofTree hL root) (address : List Nat) : Prop :=
  ∀ suffix seq y,
    gEqPurityNodeAt outer (address ++ suffix) = some (seq, some y) →
    gEqNoFreeBoundOverlap y outer ∧
    gEqEigenvariableOccursOnlyInSubtree y (address ++ suffix) outer

/-- Definition 7.3.1: Pure-variable proofs in GEq. Every actual eigenvariable inference satisfies per-formula free/bound separation throughout the proof, and every free or bound occurrence is at a node in its premise subtree. The fixed outer proof is classified from its root address; embedded G nodes remain part of the enclosing G= proof. -/
@[blueprint "chap7__definition_7_3_1" (main := true)]
def IsPureVariableProofGEq {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L}
    (T : GEqProofTree hL s) : Prop :=
  isPureVariableProofGEqAux T []

-- ===================================================================
-- Definition 7.3.1 (companion def): lkeProofTreeFormulae
-- ===================================================================

/-- Definition 7.3.1 (companion def): Collects all formulae appearing in all sequents of an LKe proof tree. Ordinary axiom leaves emit their indexed sequent, one- and two-premise nodes prepend their indexed conclusion before recursively collecting their sub-proofs, and equality-axiom leaves emit the sequent given by `LKeEqualityAxiom.toSequent` (including built-in equality congruence). -/
@[blueprint "chap7__definition_7_3_1"]
def lkeProofTreeFormulae {L : Language} :
    {s : Sequent L} → LKeProofTree s → List (FormulaN L)
  | s, .axiom_ _ _ => s.antecedent ++ s.succedent
  | _, .eqAxiom hL ax =>
    (ax.toSequent hL).antecedent ++ (ax.toSequent hL).succedent
  | s, .onePremise _ t =>
    (s.antecedent ++ s.succedent) ++ lkeProofTreeFormulae t
  | s, .twoPremise _ t1 t2 =>
    (s.antecedent ++ s.succedent) ++
      lkeProofTreeFormulae t1 ++ lkeProofTreeFormulae t2

-- ===================================================================
-- Definition 7.3.1 (companion def): lkeNoFreeBoundOverlap
-- ===================================================================

/-- Definition 7.3.1 (companion def): Predicate asserting that variable y does not occur both free and bound in any single formula of the LKe proof tree, checked globally over the entire tree via `lkeProofTreeFormulae`. -/
@[blueprint "chap7__definition_7_3_1"]
def lkeNoFreeBoundOverlap {L : Language}
    {s : Sequent L} (y : Nat) (tree : LKeProofTree s) : Prop :=
  ∀ (f : FormulaN L),
    f ∈ lkeProofTreeFormulae tree →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

-- ===================================================================
-- Definition 7.3.1 (companion def): lkeEigenvariableOccursOnlyInSubtree
-- ===================================================================

/-- Definition 7.3.1 (companion def): At the specified introducing inference, all free and bound occurrences of its eigenvariable lie in the upper subtree. Addresses distinguish repeated formula values and repeated subtrees in the fixed proof. -/
@[blueprint "chap7__definition_7_3_1"]
def lkeEigenvariableOccursOnlyInSubtree {L : Language}
    {s : Sequent L} (y : Nat) (introAddress : List Nat)
    (fullTree : LKeProofTree s) : Prop :=
  (∃ seq, lkePurityNodeAt fullTree introAddress = some (seq, some y)) ∧
  ∀ address, lkeVariableOccursAt fullTree y address →
    ∃ suffix, address = introAddress ++ [0] ++ suffix

-- ===================================================================
-- Definition 7.3.1 (companion def): IsPureVariableProofLKe
-- ===================================================================

/-- Definition 7.3.1 (companion helper): Classify introducing inferences below an address, retaining the whole outer proof for both purity clauses. Embedded G proofs retain their location in the outer G= proof; equality premises retain their canonical sequents. -/
@[blueprint "chap7__definition_7_3_1"]
def isPureVariableProofLKeAux {L : Language}
    {root : Sequent L} (outer : LKeProofTree root) (address : List Nat) : Prop :=
  ∀ suffix seq y,
    lkePurityNodeAt outer (address ++ suffix) = some (seq, some y) →
    lkeNoFreeBoundOverlap y outer ∧
    lkeEigenvariableOccursOnlyInSubtree y (address ++ suffix) outer

/-- Definition 7.3.1: Pure-variable proofs in LKe. Every actual eigenvariable inference satisfies per-formula free/bound separation throughout the proof, and every free or bound occurrence is at a node in its premise subtree. The fixed outer proof is classified from its root address; embedded G nodes remain part of the enclosing G= proof. -/
@[blueprint "chap7__definition_7_3_1" (main := true)]
def IsPureVariableProofLKe {L : Language}
    {s : Sequent L} (T : LKeProofTree s) : Prop :=
  isPureVariableProofLKeAux T []

-- ===================================================================
-- Lemma 7.3.2 (required def): hasOnlyAtomicAxioms
-- ===================================================================

/-- Lemma 7.3.2 (required def): Predicate that every axiom leaf in the LK proof tree is of the form A -> A where A is atomic (A.isAtomic holds). -/
@[blueprint "chap7__lemma_7_3_2"]
def hasOnlyAtomicAxioms {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | s, .axiom_ _ _ =>
    ∀ A : FormulaN L, s.antecedent = [A] ∧ s.succedent = [A] →
      A.isAtomic
  | _, .onePremise _ t => hasOnlyAtomicAxioms t
  | _, .twoPremise _ t1 t2 =>
    hasOnlyAtomicAxioms t1 ∧ hasOnlyAtomicAxioms t2

-- ===================================================================
-- Lemma 7.3.2 (companion def): hasOnlyAtomicOrEqAxioms
-- ===================================================================

/-- Lemma 7.3.2 (companion def): Predicate that every ordinary axiom leaf in the LKe proof tree is A -> A with A atomic, while every equality axiom (including built-in equality congruence) is permitted. One- and two-premise nodes recursively impose the condition on all sub-proofs. -/
@[blueprint "chap7__lemma_7_3_2"]
def hasOnlyAtomicOrEqAxioms {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | s, .axiom_ _ _ =>
    ∀ A : FormulaN L, s.antecedent = [A] ∧ s.succedent = [A] →
      A.isAtomic
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ t => hasOnlyAtomicOrEqAxioms t
  | _, .twoPremise _ t1 t2 =>
    hasOnlyAtomicOrEqAxioms t1 ∧ hasOnlyAtomicOrEqAxioms t2

/-- Lemma 7.3.1 (companion): Variable-only renaming of a term; every nonvariable symbol is fixed. -/
@[blueprint "chap7__lemma_7_3_1"]
def replacementTermMap {L : Language} (ρ : Nat → Nat) : Term L → Term L
  | .var x => .var (ρ x)
  | .const c => .const c
  | .func f ts => .func f (fun i => replacementTermMap ρ (ts i))

/-- Lemma 7.3.1 (companion): Capture-free replacement of formula variables. A binder may keep its name or take a fresh name; the body uses the corresponding updated assignment. The side condition prevents capture of every other free variable. -/
@[blueprint "chap7__lemma_7_3_1"]
inductive FormulaVariableReplacement {L : Language} (fresh : Nat → Prop) :
    (Nat → Nat) → FormulaN L → FormulaN L → Prop where
  | pred (ρ) (P) (ts) : FormulaVariableReplacement fresh ρ (.predN P ts)
      (.predN P (fun i => replacementTermMap ρ (ts i)))
  | eq (ρ) (hL) (t u) : FormulaVariableReplacement fresh ρ (.eq_ hL t u)
      (.eq_ hL (replacementTermMap ρ t) (replacementTermMap ρ u))
  | neg {ρ A B} : FormulaVariableReplacement fresh ρ A B →
      FormulaVariableReplacement fresh ρ (.neg A) (.neg B)
  | conj {ρ A B A' B'} : FormulaVariableReplacement fresh ρ A A' →
      FormulaVariableReplacement fresh ρ B B' →
      FormulaVariableReplacement fresh ρ (.conj A B) (.conj A' B')
  | disj {ρ A B A' B'} : FormulaVariableReplacement fresh ρ A A' →
      FormulaVariableReplacement fresh ρ B B' →
      FormulaVariableReplacement fresh ρ (.disj A B) (.disj A' B')
  | impl {ρ A B A' B'} : FormulaVariableReplacement fresh ρ A A' →
      FormulaVariableReplacement fresh ρ B B' →
      FormulaVariableReplacement fresh ρ (.impl A B) (.impl A' B')
  | all {ρ x y A B} (name : x = y ∨ fresh y)
      (safe : ∀ v, Membership.mem (formulaFVN A) v → v ≠ x → ρ v ≠ y)
      (body : FormulaVariableReplacement fresh (fun v => if v = x then y else ρ v) A B) :
      FormulaVariableReplacement fresh ρ (.all x A) (.all y B)
  | ex {ρ x y A B} (name : x = y ∨ fresh y)
      (safe : ∀ v, Membership.mem (formulaFVN A) v → v ≠ x → ρ v ≠ y)
      (body : FormulaVariableReplacement fresh (fun v => if v = x then y else ρ v) A B) :
      FormulaVariableReplacement fresh ρ (.ex x A) (.ex y B)

/-- Lemma 7.3.1 (companion): Ordered rule annotations for variable replacement. Distinct rule kinds and context blocks remain distinct; quantifier terms and names are retained even when absent from the conclusion. -/
@[blueprint "chap7__lemma_7_3_1"]
def lkStep1ReplacementData {L : Language} {p c : Sequent L} :
    FOLKStep1 p c → Nat × List (List (FormulaN L)) × List (Term L) × List Nat
  | .weakenLeft A Γ Δ => (10, [[A], Γ, Δ], [], [])
  | .weakenRight A Γ Δ => (11, [[A], Γ, Δ], [], [])
  | .contractLeft A Γ Δ => (12, [[A], Γ, Δ], [], [])
  | .contractRight A Γ Δ => (13, [[A], Γ, Δ], [], [])
  | .negLeft A Γ Δ => (14, [[A], Γ, Δ], [], [])
  | .negRight A Γ Δ => (15, [[A], Γ, Δ], [], [])
  | .exchangeLeft Γ A B Δ Λ => (16, [Γ, [A, B], Δ, Λ], [], [])
  | .exchangeRight Γ Δ A B Λ => (17, [Γ, Δ, [A, B], Λ], [], [])
  | .andLeftL A B Γ Δ => (18, [[A, B], Γ, Δ], [], [])
  | .andLeftR A B Γ Δ => (19, [[A, B], Γ, Δ], [], [])
  | .orRightL A B Γ Δ => (20, [[A, B], Γ, Δ], [], [])
  | .orRightR A B Γ Δ => (21, [[A, B], Γ, Δ], [], [])
  | .implRight A B Γ Δ => (22, [[A, B], Γ, Δ], [], [])
  | .allLeft t x A Γ Δ _ => (23, [[.all x A], Γ, Δ], [t], [x])
  | .exRight t x A Γ Δ _ => (24, [[.ex x A], Γ, Δ], [t], [x])
  | .allRight y x A Γ Δ _ _ => (25, [[.all x A], Γ, Δ], [.var y], [y, x])
  | .exLeft y x A Γ Δ _ _ => (26, [[.ex x A], Γ, Δ], [.var y], [y, x])

/-- Lemma 7.3.1 (companion): Ordered rule annotations for variable replacement. Distinct rule kinds and context blocks remain distinct; quantifier terms and names are retained even when absent from the conclusion. -/
@[blueprint "chap7__lemma_7_3_1"]
def lkStep2ReplacementData {L : Language} {p q c : Sequent L} :
    FOLKStep2 p q c → Nat × List (List (FormulaN L)) × List (Term L) × List Nat
  | .cut A Γ Δ Λ Θ => (30, [[A], Γ, Δ, Λ, Θ], [], [])
  | .andRight A B Γ Δ => (31, [[A, B], Γ, Δ], [], [])
  | .orLeft A B Γ Δ => (32, [[A, B], Γ, Δ], [], [])
  | .implLeft A B Γ Δ Λ Θ => (33, [[A, B], Γ, Δ, Λ, Θ], [], [])

/-- Lemma 7.3.1 (companion): Ordered rule annotations for variable replacement. Distinct rule kinds and context blocks remain distinct; quantifier terms and names are retained even when absent from the conclusion. -/
@[blueprint "chap7__lemma_7_3_1"]
def gStep1ReplacementData {L : Language} {p c : Sequent L} :
    GentzenStep1Ext p c → Nat × List (List (FormulaN L)) × List (Term L) × List Nat
  | .conjLeft Γ Δ Λ A B => (50, [Γ, Δ, Λ, [A, B]], [], [])
  | .disjRight Γ Δ Λ A B => (51, [Γ, Δ, Λ, [A, B]], [], [])
  | .implRight Γ Δ Λ A B => (52, [Γ, Δ, Λ, [A, B]], [], [])
  | .negLeft Γ Δ Λ A => (53, [Γ, Δ, Λ, [A]], [], [])
  | .negRight Γ Δ Λ A => (54, [Γ, Δ, Λ, [A]], [], [])
  | .allLeft ts Γ Δ Λ x A _ _ => (55, [Γ, Δ, Λ, [.all x A]], ts, [x])
  | .exRight ts Γ Δ Λ x A _ _ => (56, [Γ, Δ, Λ, [.ex x A]], ts, [x])
  | .allRight y Γ Δ Λ x A _ _ => (57, [Γ, Δ, Λ, [.all x A]], [.var y], [y, x])
  | .exLeft y Γ Δ Λ x A _ _ => (58, [Γ, Δ, Λ, [.ex x A]], [.var y], [y, x])

/-- Lemma 7.3.1 (companion): Ordered rule annotations for variable replacement. Distinct rule kinds and context blocks remain distinct; quantifier terms and names are retained even when absent from the conclusion. -/
@[blueprint "chap7__lemma_7_3_1"]
def gStep2ReplacementData {L : Language} {p q c : Sequent L} :
    GentzenStep2Ext p q c → Nat × List (List (FormulaN L)) × List (Term L) × List Nat
  | .conjRight Γ Δ Λ A B => (70, [Γ, Δ, Λ, [A, B]], [], [])
  | .disjLeft Γ Δ Λ A B => (71, [Γ, Δ, Λ, [A, B]], [], [])
  | .implLeft Γ Δ Λ A B => (72, [Γ, Δ, Λ, [A, B]], [], [])

/-- Lemma 7.3.1 (companion): The complete annotation at an ordered proof-tree address. Constructor kinds, context boundaries, hidden terms, and variable annotations are retained. Equality frames are read directly from their constructors. -/
@[blueprint "chap7__lemma_7_3_1"]
def lkReplacementNodeAt {L : Language} :
    {s : Sequent L} → FOLKProofTree s → List Nat → Option (Nat × List (List (FormulaN L)) × List (Term L) × List Nat)
  | s, .axiom_ _ _, [] => some (0, [s.antecedent, s.succedent], [], [])
  | s, .onePremise rule _, [] =>
    let d := lkStep1ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | s, .twoPremise rule _ _, [] =>
    let d := lkStep2ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | _, .onePremise _ t, 0 :: p => lkReplacementNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkReplacementNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkReplacementNodeAt t p
  | _, _, _ => none

/-- Lemma 7.3.1 (companion): The complete annotation at an ordered proof-tree address. Constructor kinds, context boundaries, hidden terms, and variable annotations are retained. Equality frames are read directly from their constructors. -/
@[blueprint "chap7__lemma_7_3_1"]
def lkeReplacementNodeAt {L : Language} :
    {s : Sequent L} → LKeProofTree s → List Nat → Option (Nat × List (List (FormulaN L)) × List (Term L) × List Nat)
  | s, .axiom_ _ _, [] => some (0, [s.antecedent, s.succedent], [], [])
  | _, .eqAxiom hL ax, [] =>
    let s := ax.toSequent hL
    let kind := match ax with
      | .refl _ => 80 | .funcCong .. => 81 | .predCong .. => 82 | .eqCong .. => 83
    some (kind, [s.antecedent, s.succedent], [], [])
  | s, .onePremise rule _, [] =>
    let d := lkStep1ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | s, .twoPremise rule _ _, [] =>
    let d := lkStep2ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | _, .onePremise _ t, 0 :: p => lkeReplacementNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => lkeReplacementNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => lkeReplacementNodeAt t p
  | _, _, _ => none

/-- Lemma 7.3.1 (companion): The complete annotation at an ordered proof-tree address. Constructor kinds, context boundaries, hidden terms, and variable annotations are retained. Equality frames are read directly from their constructors. -/
@[blueprint "chap7__lemma_7_3_1"]
def gReplacementNodeAt {L : Language} :
    {s : Sequent L} → GProofTreeExt s → List Nat → Option (Nat × List (List (FormulaN L)) × List (Term L) × List Nat)
  | s, .axiom_ _ _, [] => some (0, [s.antecedent, s.succedent], [], [])
  | s, .onePremise rule _, [] =>
    let d := gStep1ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | s, .twoPremise rule _ _, [] =>
    let d := gStep2ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | _, .onePremise _ t, 0 :: p => gReplacementNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => gReplacementNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gReplacementNodeAt t p
  | _, _, _ => none

/-- Lemma 7.3.1 (companion): The complete annotation at an ordered proof-tree address. Constructor kinds, context boundaries, hidden terms, and variable annotations are retained. Equality frames are read directly from their constructors. -/
@[blueprint "chap7__lemma_7_3_1"]
def gEqReplacementNodeAt {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → List Nat → Option (Nat × List (List (FormulaN L)) × List (Term L) × List Nat)
  | s, .axiom_ _ _, [] => some (0, [s.antecedent, s.succedent], [], [])
  | s, .onePremise rule _, [] =>
    let d := gStep1ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | s, .twoPremise rule _ _, [] =>
    let d := gStep2ReplacementData rule
    some (d.1, s.antecedent :: s.succedent :: d.2.1, d.2.2.1, d.2.2.2)
  | _, .onePremise _ t, 0 :: p => gEqReplacementNodeAt t p
  | _, .twoPremise _ t _, 0 :: p => gEqReplacementNodeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gEqReplacementNodeAt t p
  | s, .base _, [] => some (90, [s.antecedent, s.succedent], [], [])
  | _, .base g, 0 :: p => gReplacementNodeAt g p
  | _, .eqRefl t Γ Δ _, [] => some (91, [Γ, Δ], [t], [])
  | _, .eqRefl _ _ _ sub, 0 :: p => gEqReplacementNodeAt sub p
  | _, .eqFuncCong f ss ts Γ Δ _, [] => some (92, [Γ, Δ], [.func f ss, .func f ts], [])
  | _, .eqFuncCong _ _ _ _ _ sub, 0 :: p => gEqReplacementNodeAt sub p
  | _, .eqPredCong P ss ts Γ Δ _, [] => some (93, [Γ, Δ, [.predN P ss, .predN P ts]], [], [])
  | _, .eqPredCong _ _ _ _ _ sub, 0 :: p => gEqReplacementNodeAt sub p
  | _, .eqGeneral axs _ _ Γ Δ _, [] => some (94, [Γ, Δ, axs], [], [])
  | _, .eqGeneral _ _ _ _ _ sub, 0 :: p => gEqReplacementNodeAt sub p
  | _, _, _ => none

/-- Lemma 7.3.1 (companion): A fresh name is absent from every formula, term, and standalone variable annotation of the source proof node. -/
@[blueprint "chap7__lemma_7_3_1"]
def replacementNodeFresh {L : Language} (y : Nat)
    (d : Nat × List (List (FormulaN L)) × List (Term L) × List Nat) : Prop :=
  (∀ block ∈ d.2.1, ∀ A ∈ block, ¬ Membership.mem (formulaAllVariables A) y) ∧
  (∀ t ∈ d.2.2.1, ¬ Membership.mem (termVariables t) y) ∧ y ∉ d.2.2.2

/-- Lemma 7.3.1 (companion): A variable replacement preserves the rule kind and every ordered annotation position. One injective free-variable assignment serves all formula and term annotations at a node. Quantifier bodies are recorded under their binders, allowing binder names and eigenvariable names to be replaced independently and capture-free. -/
@[blueprint "chap7__lemma_7_3_1"]
def replacementNodeRelated {L : Language} (fresh : Nat → Prop)
    (a b : Nat × List (List (FormulaN L)) × List (Term L) × List Nat) : Prop :=
  a.1 = b.1 ∧ ∃ ρ : Nat → Nat,
    (∀ x y, ρ x = ρ y → x = y) ∧
    (∀ block ∈ a.2.1, ∀ A ∈ block, ∀ x,
      Membership.mem (formulaFVN A) x → ρ x = x ∨ fresh (ρ x)) ∧
    (∀ t ∈ a.2.2.1, ∀ x,
      Membership.mem (termVariables t) x → ρ x = x ∨ fresh (ρ x)) ∧
    a.2.1.length = b.2.1.length ∧
    (∀ blocks ∈ a.2.1.zip b.2.1,
      blocks.1.length = blocks.2.length ∧
      ∀ pair ∈ blocks.1.zip blocks.2, FormulaVariableReplacement fresh ρ pair.1 pair.2) ∧
    b.2.2.1 = a.2.2.1.map (replacementTermMap ρ) ∧
    a.2.2.2.length = b.2.2.2.length ∧
    (∀ pair ∈ a.2.2.2.zip b.2.2.2, pair.1 = pair.2 ∨ fresh pair.2)

/-- Lemma 7.3.1 (companion): Variable-only replacement of an ordered proof. Both address domains must agree. New names are fresh for the entire supplied source proof, including rule-only annotations. -/
@[blueprint "chap7__lemma_7_3_1"]
def proofNodeVariableReplacement {L : Language}
    (source target : List Nat → Option (Nat × List (List (FormulaN L)) × List (Term L) × List Nat)) : Prop :=
  let fresh := fun y => ∀ p d, source p = some d → replacementNodeFresh y d
  ∀ p, match source p, target p with
    | none, none => True
    | some a, some b => replacementNodeRelated fresh a b
    | _, _ => False

/-- Lemma 7.3.1 (companion): Same-calculus, same-end-sequent fresh capture-free variable replacement of the given proof; ordered tree shape, rule kinds and nonvariable symbols are preserved. -/
@[blueprint "chap7__lemma_7_3_1"]
def proofVariableReplacementLK {L : Language} {s : Sequent L}
    (source target : FOLKProofTree s) : Prop :=
  proofNodeVariableReplacement (lkReplacementNodeAt source) (lkReplacementNodeAt target)

/-- Lemma 7.3.1 (companion): Same-calculus, same-end-sequent fresh capture-free variable replacement of the given proof; ordered tree shape, rule kinds and nonvariable symbols are preserved. -/
@[blueprint "chap7__lemma_7_3_1"]
def proofVariableReplacementLKe {L : Language} {s : Sequent L}
    (source target : LKeProofTree s) : Prop :=
  proofNodeVariableReplacement (lkeReplacementNodeAt source) (lkeReplacementNodeAt target)

/-- Lemma 7.3.1 (companion): Same-calculus, same-end-sequent fresh capture-free variable replacement of the given proof; ordered tree shape, rule kinds and nonvariable symbols are preserved. -/
@[blueprint "chap7__lemma_7_3_1"]
def proofVariableReplacementG {L : Language} {s : Sequent L}
    (source target : GProofTreeExt s) : Prop :=
  proofNodeVariableReplacement (gReplacementNodeAt source) (gReplacementNodeAt target)

/-- Lemma 7.3.1 (companion): Same-calculus, same-end-sequent fresh capture-free variable replacement of the given proof; ordered tree shape, rule kinds and nonvariable symbols are preserved. -/
@[blueprint "chap7__lemma_7_3_1"]
def proofVariableReplacementGEq {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (source target : GEqProofTree hL s) : Prop :=
  proofNodeVariableReplacement (gEqReplacementNodeAt source) (gEqReplacementNodeAt target)

-- ===================================================================
-- Lemma 7.3.1: pureVariableConversion_LK
-- ===================================================================

/-- Lemma 7.3.1: Every supplied LK proof over an equality-free language
admits a pure proof of the identical sequent, obtained by fresh capture-free
variable replacement preserving its ordered rule tree and nonvariable symbols. -/
@[attach_debt, blueprint "chap7__lemma_7_3_1" (main := true)]
theorem pureVariableConversion_LK {L : Language}
    (_hL : L.withoutEquality) (seq : Sequent L) (T : FOLKProofTree seq) :
    ∃ t : FOLKProofTree seq, IsPureVariableProofLK t ∧ proofVariableReplacementLK T t 

/-- Lemma 7.3.1: Every supplied G proof over an equality-free language
admits a pure proof of the identical sequent, obtained by fresh capture-free
variable replacement preserving its ordered rule tree and nonvariable symbols. -/
@[attach_debt, blueprint "chap7__lemma_7_3_1" (main := true)]
theorem pureVariableConversion_G {L : Language}
    (_hL : L.withoutEquality) (seq : Sequent L) (T : GProofTreeExt seq) :
    ∃ t : GProofTreeExt seq, IsPureVariableProofG t ∧ proofVariableReplacementG T t 

/-- Lemma 7.3.1 (companion): Every supplied LKe proof admits a pure proof of the same sequent related by fresh capture-free variable replacement. -/
theorem pureVariableConversion_LKe_helper {L : Language} :
    ∀ {s : Sequent L} (T : LKeProofTree s),
    ∃ t : LKeProofTree s, IsPureVariableProofLKe t ∧ proofVariableReplacementLKe T t := by
  -- REPAIR(T7-36): proof pending
  sorry

/-- Lemma 7.3.1 (companion): The proof-consuming LKe conversion statement preserves the end sequent and certifies variable-only replacement. -/
@[blueprint "chap7__lemma_7_3_1" (main := true)]
theorem pureVariableConversion_LKe {L : Language}
    (seq : Sequent L) (T : LKeProofTree seq) :
    ∃ t : LKeProofTree seq, IsPureVariableProofLKe t ∧ proofVariableReplacementLKe T t 

/-- Lemma 7.3.1 (companion): Every supplied GEq proof admits a pure proof of the same sequent related by fresh capture-free variable replacement. -/
theorem pureVariableConversion_GEq_helper {L : Language} {hL : L.hasEquality = true} :
    ∀ {s : Sequent L} (T : GEqProofTree hL s),
    ∃ t : GEqProofTree hL s, IsPureVariableProofGEq t ∧ proofVariableReplacementGEq T t := by
  -- REPAIR(T7-36): proof pending
  sorry

/-- Lemma 7.3.1 (companion): The proof-consuming GEq conversion statement preserves the end sequent and certifies variable-only replacement. -/
@[blueprint "chap7__lemma_7_3_1" (main := true)]
theorem pureVariableConversion_GEq {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L) (T : GEqProofTree hL seq) :
    ∃ t : GEqProofTree hL seq, IsPureVariableProofGEq t ∧ proofVariableReplacementGEq T t 

-- ===================================================================
-- Lemma 7.3.2: atomicAxiomReduction_LK
-- ===================================================================

-- ATTACH-BLOCKER: private declaration
private theorem isFreeForN_var_self_local {L : Language}
    (A : FormulaN L) (x : Nat) :
    isFreeForN (.var x) x A := by
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      constructor
      · intro hy
        apply hxy
        change y = x at hy
        exact hy.symm
      · exact ih
  | ex y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      constructor
      · intro hy
        apply hxy
        change y = x at hy
        exact hy.symm
      · exact ih

theorem atomicIdentity_LK {L : Language} :
    ∀ A : FormulaN L,
      ∃ t : FOLKProofTree (Sequent.mk [A] [A]),
        hasOnlyAtomicAxioms t := by
  intro A
  induction A with
  | predN P ts =>
    refine ⟨.axiom_ _ ⟨.predN P ts, rfl, rfl⟩, ?_⟩
    simp [hasOnlyAtomicAxioms, FormulaN.isAtomic]
  | eq_ hL t₁ t₂ =>
    refine ⟨.axiom_ _ ⟨.eq_ hL t₁ t₂, rfl, rfl⟩, ?_⟩
    simp [hasOnlyAtomicAxioms, FormulaN.isAtomic]
  | neg A ih =>
    obtain ⟨tA, hA⟩ := ih
    let tNegLeft :
        FOLKProofTree (Sequent.mk [FormulaN.neg A, A] []) :=
      .onePremise (.negLeft A [A] []) tA
    let tExchange :
        FOLKProofTree (Sequent.mk [A, FormulaN.neg A] []) :=
      .onePremise
        (.exchangeLeft [] (FormulaN.neg A) A [] [])
        tNegLeft
    exact ⟨.onePremise (.negRight A [FormulaN.neg A] []) tExchange, hA⟩
  | conj A B ihA ihB =>
    obtain ⟨tA, hA⟩ := ihA
    obtain ⟨tB, hB⟩ := ihB
    let tLeft :
        FOLKProofTree (Sequent.mk [FormulaN.conj A B] [A]) :=
      .onePremise (.andLeftL A B [] [A]) tA
    let tRight :
        FOLKProofTree (Sequent.mk [FormulaN.conj A B] [B]) :=
      .onePremise (.andLeftR A B [] [B]) tB
    exact ⟨.twoPremise (.andRight A B [FormulaN.conj A B] [])
      tLeft tRight, ⟨hA, hB⟩⟩
  | disj A B ihA ihB =>
    obtain ⟨tA, hA⟩ := ihA
    obtain ⟨tB, hB⟩ := ihB
    let tLeft :
        FOLKProofTree (Sequent.mk [A] [FormulaN.disj A B]) :=
      .onePremise (.orRightL A B [A] []) tA
    let tRight :
        FOLKProofTree (Sequent.mk [B] [FormulaN.disj A B]) :=
      .onePremise (.orRightR A B [B] []) tB
    exact ⟨.twoPremise (.orLeft A B [] [FormulaN.disj A B])
      tLeft tRight, ⟨hA, hB⟩⟩
  | impl A B ihA ihB =>
    obtain ⟨tA, hA⟩ := ihA
    obtain ⟨tB, hB⟩ := ihB
    let tImplLeft :
        FOLKProofTree (Sequent.mk [FormulaN.impl A B, A] [B]) :=
      .twoPremise (.implLeft A B [A] [] [] [B]) tA tB
    let tExchange :
        FOLKProofTree (Sequent.mk [A, FormulaN.impl A B] [B]) :=
      .onePremise
        (.exchangeLeft [] (FormulaN.impl A B) A [] [B])
        tImplLeft
    exact ⟨.onePremise
      (.implRight A B [FormulaN.impl A B] [])
      tExchange, ⟨hA, hB⟩⟩
  | all x A ih =>
    obtain ⟨tA, hA⟩ := ih
    obtain ⟨tSub, hSub⟩ :
        ∃ t : FOLKProofTree
            (Sequent.mk [formulaSubstN A (Term.var x) x] [A]),
          hasOnlyAtomicAxioms t := by
      rw [formulaSubstN_var_self]
      exact ⟨tA, hA⟩
    let tAllLeft :
        FOLKProofTree (Sequent.mk [FormulaN.all x A] [A]) :=
      .onePremise
        (.allLeft (Term.var x) x A [] [A]
          (isFreeForN_var_self_local A x))
        tSub
    have hAllLeft : hasOnlyAtomicAxioms tAllLeft := hSub
    obtain ⟨tAllLeftSub, hAllLeftSub⟩ :
        ∃ t : FOLKProofTree
            (Sequent.mk [FormulaN.all x A]
              [formulaSubstN A (Term.var x) x]),
          hasOnlyAtomicAxioms t := by
      rw [formulaSubstN_var_self]
      exact ⟨tAllLeft, hAllLeft⟩
    have hfresh :
        ∀ F ∈
            (Sequent.mk [FormulaN.all x A]
              ([] ++ [FormulaN.all x A])).antecedent ++
            (Sequent.mk [FormulaN.all x A]
              ([] ++ [FormulaN.all x A])).succedent,
          x ∉ formulaFVN F := by
      intro F hF
      have hEq : F = FormulaN.all x A := by simpa using hF
      subst F
      intro hx
      exact hx.2 rfl
    exact ⟨.onePremise
      (.allRight x x A [FormulaN.all x A] [] hfresh
        (isFreeForN_var_self_local A x))
      tAllLeftSub, hAllLeftSub⟩
  | ex x A ih =>
    obtain ⟨tA, hA⟩ := ih
    obtain ⟨tSub, hSub⟩ :
        ∃ t : FOLKProofTree
            (Sequent.mk [A] [formulaSubstN A (Term.var x) x]),
          hasOnlyAtomicAxioms t := by
      rw [formulaSubstN_var_self]
      exact ⟨tA, hA⟩
    let tExRight :
        FOLKProofTree (Sequent.mk [A] [FormulaN.ex x A]) :=
      .onePremise
        (.exRight (Term.var x) x A [A] []
          (isFreeForN_var_self_local A x))
        tSub
    have hExRight : hasOnlyAtomicAxioms tExRight := hSub
    obtain ⟨tExRightSub, hExRightSub⟩ :
        ∃ t : FOLKProofTree
            (Sequent.mk [formulaSubstN A (Term.var x) x]
              [FormulaN.ex x A]),
          hasOnlyAtomicAxioms t := by
      rw [formulaSubstN_var_self]
      exact ⟨tExRight, hExRight⟩
    have hfresh :
        ∀ F ∈
            (Sequent.mk [FormulaN.ex x A]
              [FormulaN.ex x A]).antecedent ++
            (Sequent.mk [FormulaN.ex x A]
              [FormulaN.ex x A]).succedent,
          x ∉ formulaFVN F := by
      intro F hF
      have hEq : F = FormulaN.ex x A := by simpa using hF
      subst F
      intro hx
      exact hx.2 rfl
    exact ⟨.onePremise
      (.exLeft x x A [] [FormulaN.ex x A] hfresh
        (isFreeForN_var_self_local A x))
      tExRightSub, hExRightSub⟩

theorem atomicAxiomReduction_LK_helper {L : Language} :
    ∀ {s : Sequent L} (_ : FOLKProofTree s),
      ∃ T' : FOLKProofTree s, hasOnlyAtomicAxioms T' := by
  intro s T
  induction T with
  | axiom_ s hax =>
    obtain ⟨A, hAnt, hSucc⟩ := hax
    obtain ⟨tA, hA⟩ := atomicIdentity_LK A
    cases s with
    | mk Γ Δ =>
      simp only at hAnt hSucc
      subst Γ
      subst Δ
      exact ⟨tA, hA⟩
  | onePremise rule T ih =>
    obtain ⟨T', hT'⟩ := ih
    exact ⟨.onePremise rule T', hT'⟩
  | twoPremise rule T₁ T₂ ih₁ ih₂ =>
    obtain ⟨T₁', hT₁'⟩ := ih₁
    obtain ⟨T₂', hT₂'⟩ := ih₂
    exact ⟨.twoPremise rule T₁' T₂', ⟨hT₁', hT₂'⟩⟩

/-- Lemma 7.3.2: Over an equality-free language, every sequent provable in LK is provable with a proof in which all axioms are sequents A -> A where A is an atomic formula. The proof first constructs an atomic-axiom identity derivation for every formula by structural induction, then recursively replaces every axiom leaf of the input proof while replaying all inference rules unchanged. -/
@[blueprint "chap7__lemma_7_3_2" (main := true)]
theorem atomicAxiomReduction_LK {L : Language}
    (_hL : L.withoutEquality) (seq : Sequent L)
    (hprov : folkProvable seq) :
    ∃ t : FOLKProofTree seq, hasOnlyAtomicAxioms t

-- ===================================================================
-- Lemma 7.3.2 (companion theorem): atomicAxiomReduction_LKe
-- ===================================================================

theorem hasOnlyAtomicAxioms_lk {L : Language} :
    ∀ {s : Sequent L} (T : FOLKProofTree s),
      hasOnlyAtomicAxioms T →
      hasOnlyAtomicOrEqAxioms (LKeProofTree.lk T) := by
  intro s T hT
  induction T with
  | axiom_ s hax => exact hT
  | onePremise rule T ih => exact ih hT
  | twoPremise rule T₁ T₂ ih₁ ih₂ =>
    exact ⟨ih₁ hT.1, ih₂ hT.2⟩

/-- Lemma 7.3.2 Part (ii) (Atomic axiom reduction for LKe): Every sequent provable in LKe is provable with a proof in which the axioms are either sequents A -> A where A is atomic, or equality axioms. The proof recursively replaces ordinary axiom leaves by the LK atomic-identity construction, preserves equality-axiom leaves, and replays all inference rules unchanged. -/
@[blueprint "chap7__lemma_7_3_2" (main := true)]
theorem atomicAxiomReduction_LKe_helper {L : Language} :
    ∀ {s : Sequent L} (_ : LKeProofTree s),
    ∃ T' : LKeProofTree s, hasOnlyAtomicOrEqAxioms T'



end LCS.Herbrand.SharpenedHauptsatz
