import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Search
import LCS.Propositional.Infinite.Semantics
import LCS.Propositional.Infinite.NonTerminatingSearchExample.ProofsStamp

/-! # Example 3.5.2: a search that does not terminate

The infinite rightmost branch, the sets U and V, the signed (Hintikka)
set they form, and its satisfying valuation.
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- Example 3.5.2 (companion type): The textbook informally introduces
    signed formulae in this example: "The pair (U, V) can be encoded as
    a single set if we prefix every proposition in U with the letter T
    (standing for true), and every proposition in V with the letter F
    (standing for false)." This is the informal version; the formal
    definition is Definition 3.5.3 in SignedFormulae.lean. -/
@[blueprint "chap3__example_3_5_2"]
inductive SignedFormula where
  | trueSign : PropFormulaNormalized → SignedFormula
  | falseSign : PropFormulaNormalized → SignedFormula
  deriving DecidableEq, Repr

open LCS.Propositional.Systems.G.Search

-- ========= Example 3.5.2: Non-Terminating Infinite Search =========

/-- Example 3.5.2: The infinite sequent with the same antecedent as
    Example 3.5.1 but succedent Delta_0 = <Q> only. The absence of P3
    in the succedent means the search does not terminate: the rightmost
    branch is infinite. -/
@[blueprint "chap3__example_3_5_2" (main := true)]
def exInfSearchNonTerminating : InfSequent :=
  { antecedent := fun n =>
      if n = 0 then some (.var 1)
      else some (.impl (.var n) (.var (n + 1)))
    succedent := fun n =>
      if n = 0 then some (.var 0)
      else none
    antecedent_noHoles := by
      intro n h
      cases n <;> simp at h
    succedent_noHoles := by
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
        cases n with
        | zero => simp_all
        | succ n => simp }

/-- Example 3.5.2 (companion): The set U of all propositions occurring
    as premises along the infinite rightmost branch:
    U = {P0, P1, P2, ...} ∪ {Pi ⇒ P(i+1) | i ∈ Nat}. -/

@[blueprint "chap3__example_3_5_2"]
def exInfBranchPremises : Set PropFormulaNormalized :=
  fun A => (∃ i : Nat, A = .var (i + 1)) ∨ (∃ i : Nat, A = .impl (.var (i + 1)) (.var (i + 2)))

/-- Example 3.5.2 (companion): The set V of all propositions occurring
    as conclusions along the infinite rightmost branch: V = {Q}. -/

@[blueprint "chap3__example_3_5_2"]
def exInfBranchConclusions : Set PropFormulaNormalized :=
  fun A => A = .var 0

/-- Example 3.5.2 (companion): The Hintikka set of signed formulae
    combining T-prefixed premises and F-prefixed conclusions:
    {T(P₀⊃P₁), ..., TP₀, TP₁, ..., FQ}. The textbook says: "The
    resulting set ... is a set having some remarkable properties, and
    called a Hintikka set." -/

@[blueprint "chap3__example_3_5_2"]
def exInfHintikkaSet : Set SignedFormula :=
  fun sf => match sf with
    | .trueSign A => exInfBranchPremises A
    | .falseSign A => exInfBranchConclusions A

/-- Example 3.5.2 (companion): The falsifying valuation v where
    v(Pi) = T for all i >= 0 and v(Q) = F (where Q = var 0).
    This valuation satisfies all premises and falsifies Q,
    thereby falsifying the original sequent. -/

@[blueprint "chap3__example_3_5_2"]
def exInfFalsifyingValuation : Valuation :=
  fun n => if n = 0 then BoolVal.F else BoolVal.T

/-- Atomic checkpoint antecedent Pₙ,…,P₀ on the rightmost branch. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostAtoms : Nat → List PropFormulaNormalized
  | 0 => [.var 1]
  | n + 1 => .var (n + 2) :: exInfRightmostAtoms n

@[blueprint "chap3__example_3_5_2"]
def exInfRightmostCheckpoint (n : Nat) : Sequent :=
  Sequent.mk (exInfRightmostAtoms n) [.var 0]

/-- The intermediate label obtained by introducing Pₙ⇒Pₙ₊₁. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostIntroduced (n : Nat) : Sequent :=
  Sequent.mk (exInfRightmostAtoms n ++ [.impl (.var (n + 1)) (.var (n + 2))]) [.var 0]

/-- The full rightmost path alternates introduction child 0 and implication child 1. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostAddress (n : Nat) : List Nat :=
  (List.range n).map (fun i => i % 2)

/-- Full labels include the intermediate implication-bearing sequents. -/
@[blueprint "chap3__example_3_5_2"]
def exInfRightmostLabel (n : Nat) : Sequent :=
  if n % 2 = 0 then exInfRightmostCheckpoint (n / 2)
  else exInfRightmostIntroduced (n / 2)

/-- Example 3.5.2's rightmost path is an infinite path of the tree actually built by search. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfRightmost_is_infinite_path :
    (infSearchTreeDomain exInfSearchNonTerminating).InfinitePath exInfRightmostAddress 

/-- The source's atomic displayed labels are exactly the even checkpoints.
Odd path positions retain the mandatory intermediate implication labels. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfRightmost_checkpoints (n : Nat) :
    infSearchLimit exInfSearchNonTerminating (exInfRightmostAddress (2 * n))
      (Sequent.mk (exInfRightmostAtoms n) [.var 0]) 

/-- The source's signed set is exactly the union along this actual full branch. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfHintikkaSet_actual_branch (sf : SignedFormula) :
    exInfHintikkaSet sf ↔
      match sf with
      | .trueSign A => ∃ n, A ∈ (exInfRightmostLabel n).antecedent
      | .falseSign A => ∃ n, A ∈ (exInfRightmostLabel n).succedent 

/-- The stated valuation satisfies every signed formula on the actual rightmost branch. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfHintikkaSet_satisfied (sf : SignedFormula) (h : exInfHintikkaSet sf) :
    match sf with
    | .trueSign A => evalExtN exInfFalsifyingValuation A = BoolVal.T
    | .falseSign A => evalExtN exInfFalsifyingValuation A = BoolVal.F 

/-- The explicit rightmost leaf stays unfinished at every stage. -/
@[blueprint "chap3__example_3_5_2"]
theorem exInfSearchNonTerminating_does_not_halt :
    ¬ infSearchHalts exInfSearchNonTerminating 

end LCS.Propositional.Infinite
end
