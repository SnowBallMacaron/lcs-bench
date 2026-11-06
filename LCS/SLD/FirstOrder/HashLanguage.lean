import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import Attach
import LCS.SLD.FirstOrder.HashLanguage.ProofsStamp

/-! # The hash language

Section 9.4.2 (proof of Theorem 9.4.1): the language obtained by adding one fresh constant, the exact lift of terms, formulae, atoms and Horn clauses into it, and the transfer of satisfiability. -/

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ===================================================================
-- Hash-language infrastructure for the §9.4 semantic reduction
-- ===================================================================

/-- The sole fresh hash symbol has rank zero and is represented as a constant. -/
def hashSkolemRank (_ : Fin 1) : Nat := 0

/-- The language obtained by adding one fresh nullary hash symbol to `L`.
    This is the existing §7.6 Skolem-language extension specialized to
    one rank-zero symbol, not a second language-extension mechanism. -/
@[blueprint "chap9__theorem_9_4_1"]
abbrev HashLanguage (L : Language) : Language :=
  LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) 1 hashSkolemRank

/-- Exact embedding of base-language terms into the hash language. -/
abbrev hashLiftTerm {L : Language} : Term L → Term (HashLanguage L) :=
  LCS.Herbrand.SHGTheorem.liftTermSkolem
    (skolemRank := hashSkolemRank)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Exact structural embedding of base-language atoms into the hash
    language. -/
def hashLiftAtom {L : Language} (hNoEq : L.withoutEquality) :
    FOAtom L hNoEq → FOAtom (HashLanguage L) hNoEq
  | .predN P args =>
      .predN P (fun i => hashLiftTerm (args i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (hashLiftTerm lhs) (hashLiftTerm rhs)

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding
/-- Exact structural lift of a PROLOG-notation Horn clause. -/
def hashLiftHornClause {L : Language} (hNoEq : L.withoutEquality) :
    FOHornClause L hNoEq → FOHornClause (HashLanguage L) (by all_goals exact hNoEq)
  | FOHornClauseCore.rule head body =>
      FOHornClauseCore.rule ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) head) (body.image (hashLiftAtom (hNoEq := by all_goals exact hNoEq)))
  | FOHornClauseCore.fact head => FOHornClauseCore.fact ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) head)
  | FOHornClauseCore.goal body => FOHornClauseCore.goal (body.image (hashLiftAtom (hNoEq := by all_goals exact hNoEq)))

end LCS.SLD.FirstOrder
end
