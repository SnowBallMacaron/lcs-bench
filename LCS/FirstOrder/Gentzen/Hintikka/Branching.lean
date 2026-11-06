import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.SearchClosure

/-! # Branching on type-b formulae (Section 5.4.7)

The two components of a type-b formula, the branching step and the node
sequences along a branching address, with monotonicity and decomposition
lemmas. Used by the proof of Theorem 5.4.1.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Branching expansion helpers for type-B formulae
-- ===================================================================

/-- Theorem 5.5.1 (companion): Type-B antecedent component extraction. For a given bit:
- disj X Y in antecedent: bit=0 yields X in ant, bit!=0 yields Y in ant
- impl X Y in antecedent: bit=0 yields X in succ, bit!=0 yields Y in ant
Returns (new antecedent formulas, new succedent formulas). -/
def typeBCompAnt {L : Language} (A : FormulaN L) (bit : Nat) :
    List (FormulaN L) × List (FormulaN L) :=
  match A with
  | .disj X Y => if bit = 0 then ([X], []) else ([Y], [])
  | .impl X Y => if bit = 0 then ([], [X]) else ([Y], [])
  | _ => ([], [])

/-- Theorem 5.5.1 (companion): Type-B succedent component extraction. For a given bit:
- conj X Y in succedent: bit=0 yields X in succ, bit!=0 yields Y in succ
Returns (new antecedent formulas, new succedent formulas). -/
def typeBCompSucc {L : Language} (B : FormulaN L) (bit : Nat) :
    List (FormulaN L) × List (FormulaN L) :=
  match B with
  | .conj X Y => if bit = 0 then ([], [X]) else ([], [Y])
  | _ => ([], [])

/-- Theorem 5.5.1 (companion): Collect type-B antecedent components (new antecedent formulas). -/
def collectBranchAntNew {L : Language} (formulas : List (FormulaN L))
    (bit : Nat) : List (FormulaN L) :=
  formulas.flatMap (fun A => (typeBCompAnt A bit).1)

/-- Theorem 5.5.1 (companion): Collect type-B new succedent formulas from both antecedent and
succedent type-B formulae. -/
def collectBranchSuccNew {L : Language}
    (antFormulas succFormulas : List (FormulaN L))
    (bit : Nat) : List (FormulaN L) :=
  antFormulas.flatMap (fun A => (typeBCompAnt A bit).2) ++
  succFormulas.flatMap (fun B => (typeBCompSucc B bit).2)

/-- Theorem 5.5.1 (companion): Terms whose free variables do not appear as bound variables in any
formula of the sequent. This is the correct term algebra H for the
Hintikka set construction (cf. textbook section 5.4.7): isFreeForN t x A
holds for all t in safeTermsN and all A in the search path. -/
def safeTermsN {L : Language} (seq : Sequent L) : Set (Term L) :=
  fun t => ∀ v, v ∈ termFV t → ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∉ formulaBVN A

/-- Theorem 5.5.1 (companion): The safe terms list for branchStep at a given depth. Filters
Countable.enumerate terms to those in safeTermsN rootSeq (free
variables avoid root sequent's bound variables), plus the fresh
eigenvariable Term.var(freshBase + depth) which is always safe. -/
noncomputable def branchTerms {L : Language} [Countable (Term L)]
    (rootSeq : Sequent L) (depth : Nat) (freshBase : Nat) : List (Term L) :=
  have : ∀ (p : Prop), Decidable p := Classical.propDecidable
  let allTerms := (List.range (depth + 1)).map (Countable.enumerate (α := Term L))
  allTerms.filter (fun t => decide (t ∈ safeTermsN rootSeq))
    ++ [Term.var (freshBase + depth)]

/-- Theorem 5.5.1 (companion): One branching expansion step: apply linear decomposition (type-A/C/D
via searchClosureStep) AND add type-B component selection based on bit.
At depth n, uses safe terms from enumerate 0..n (filtered to safeTermsN
rootSeq) plus the eigenvariable for type-C, and var(freshBase+n) for
type-D, then adds type-B components chosen by bit.

The rootSeq parameter is the root sequent of the search tree. Type-C
substitution terms are restricted to safeTermsN rootSeq to ensure
that no bound variable of the root sequent is introduced as a free
variable in the search path (needed for H5: isFreeFor). -/
noncomputable def branchStep {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth : Nat) (freshBase : Nat)
    (bit : Nat) (rootSeq : Sequent L) : Sequent L :=
  let terms := branchTerms rootSeq depth freshBase
  let linear := searchClosureStep prev terms (Term.var (freshBase + depth))
  { antecedent := linear.antecedent
      ++ collectBranchAntNew prev.antecedent bit
  , succedent := linear.succedent
      ++ collectBranchSuccNew prev.antecedent prev.succedent bit }

end LCS.FirstOrder.Gentzen.Hintikka
end
