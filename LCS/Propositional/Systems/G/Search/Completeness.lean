import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Procedure
import LCS.Propositional.Systems.G.Search.FalsificationPropagation
import LCS.Propositional.Systems.G.Search.Completeness.ProofsStamp

/-! # Completeness of G' (Section 3.4.7: Theorem 3.4.1 and Corollary)

search builds a deduction tree whose leaves give all falsifying valuations;
every valid sequent is provable, and validity is decidable.
-/
section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

-- ========= Theorem 3.4.1: Helper definitions =========

/-- Theorem 3.4.1 (required helper): A deduction tree is a proof tree if
    all its leaves are axiom sequents (sequents where antecedent and
    succedent share a common proposition). -/
@[blueprint "chap3__theorem_3_4_1"]
def isProofTree {s : Sequent} (dt : DeductionTree s) : Prop :=
  ∀ s ∈ dt.leaves, isAxiom s

-- Helper: BoolVal.T and BoolVal.F are the only values


-- Helper: completeness by strong induction on complexity


/-- Theorem 3.4.1 (companion): Completeness of G'. Every valid sequent is
    provable in G'. This is the faithful formalization of the textbook's
    completeness theorem for G'. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem completeness_G (s : Sequent) (hv : sequentValid s) :
    sequentProvable s 

-- ========= Theorem 3.4.1: Decidability of sequent validity =========

/-- Theorem 3.4.1 (required helper): Collect all variable indices
    occurring in a formula. -/
@[blueprint "chap3__theorem_3_4_1"]
def formulaVarIndices : PropFormulaNormalized → List Nat
  | .var n => [n]
  | .neg A => formulaVarIndices A
  | .conj A B => formulaVarIndices A ++ formulaVarIndices B
  | .disj A B => formulaVarIndices A ++ formulaVarIndices B
  | .impl A B => formulaVarIndices A ++ formulaVarIndices B

/-- Theorem 3.4.1 (required helper): Collect all variable indices
    occurring in a sequent. -/
@[blueprint "chap3__theorem_3_4_1"]
def sequentVarIndices (s : Sequent) : List Nat :=
  ((s.antecedent ++ s.succedent).flatMap formulaVarIndices).eraseDups

/-- Theorem 3.4.1 (required helper): Generate all valuations over a
    given list of variable indices. Each valuation assigns T or F to
    the listed variables, and F to all others. -/
@[blueprint "chap3__theorem_3_4_1"]
def allValuations (vars : List Nat) : List Valuation :=
  match vars with
  | [] => [fun _ => BoolVal.F]
  | n :: ns =>
    let rest := allValuations ns
    rest.flatMap (fun v => [fun m => if m == n then BoolVal.T else v m,
                             fun m => if m == n then BoolVal.F else v m])

/-- Theorem 3.4.1 (required helper): Check whether a sequent is valid
    under a given valuation (returns Bool). -/
@[blueprint "chap3__theorem_3_4_1"]
def checkSequentValidFor (s : Sequent) (v : Valuation) : Bool :=
  if s.antecedent.all (fun A => evalExtN v A == BoolVal.T)
  then s.succedent.any (fun B => evalExtN v B == BoolVal.T)
  else true

/-- Theorem 3.4.1 (required helper): Check whether a sequent is valid
    by checking all valuations over its variable indices. -/
@[blueprint "chap3__theorem_3_4_1"]
def checkSequentValid (s : Sequent) : Bool :=
  (allValuations (sequentVarIndices s)).all (checkSequentValidFor s)

/-- Theorem 3.4.1 (companion): checkSequentValid is correct: it returns
    true if and only if the sequent is valid. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem checkSequentValid_correct (s : Sequent) :
    checkSequentValid s = true ↔ sequentValid s 

-- ========= Theorem 3.4.1: Constructive falsifying extraction =========

-- Helper: extract falsification evidence from checkSequentValidFor = false


/-- Theorem 3.4.1 (companion): A sequent that is not valid is falsifiable.
    If the sequent is not valid, there exists a valuation falsifying it.

    The falsifying valuation is extracted constructively from the truth-table
    enumeration: checkSequentValid enumerates all valuations over the sequent's
    variable indices, and from ¬sequentValid s we derive that the check fails,
    yielding a specific valuation in the enumeration where all antecedent
    formulas evaluate to T and all succedent formulas evaluate to F. This
    avoids the classical extraction pattern (Classical.not_forall /
    Classical.not_imp) used in the previous version; the witness comes
    from the computable enumeration, not from double-negation elimination. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem search_falsifying_extraction (s : Sequent)
    (hf : ¬sequentValid s) :
    sequentFalsifiable s 

-- ========= Path-finding infrastructure =========

-- Local definitions matching SignedFormulae.lean types, defined here to
-- avoid a circular import (SignedFormulae -> Infinite -> Search).

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A direction in a deduction tree: left or right at a two-premise node. -/
inductive PathDir' where
  | left : PathDir'
  | right : PathDir'
  deriving DecidableEq, Repr

  -- unreachable: sequentsAlongPath' is never empty

-- ========= Theorem 2: search_terminates =========



-- ========= Theorems 7-8: search_conclusion, search_wf =========





/-- The atomic stopping convention produces an atomically closed tree,
    including when the input is a compound axiom. -/
@[blueprint "chap3__definition_3_4_6"]
theorem searchStart_atomic_closed (s : Sequent) :
    ∀ leaf ∈ (searchStart .atomic s).leaves,
      ∀ A ∈ leaf.antecedent ++ leaf.succedent, isAtomicFormula A 

-- ========= Theorem 3.4.1: Main theorem and corollary =========

/-- Theorem 3.4.1: The procedure search terminates for every finite input
    sequent. If the input sequent Γ → Δ is valid, procedure search produces
    a proof tree for Γ → Δ; if Γ → Δ is falsifiable, search produces a tree
    from which all falsifying valuations can be found.

    Formally: let T = searchStart s. Then:
    (1) T is a finished deduction tree (all leaves are axioms or all-atomic).
    (2) If s is valid, T is a proof tree (all leaves are axioms).
    (3) If s is falsifiable, every falsifying valuation v for s also
        falsifies some non-axiom leaf of T. -/
@[blueprint "chap3__theorem_3_4_1" (main := true)]
theorem search_theorem_3_4_1 (s : Sequent) :
    let T := searchStart mode s
    isFinishedTree mode T ∧
    (sequentValid s → isProofTree T) ∧
    (¬sequentValid s → ∀ v, sequentFalsifiedBy s v →
      ∃ leaf ∈ nonAxiomLeaves T, sequentFalsifiedBy leaf v) 

end LCS.Propositional.Systems.G.Search
end
