import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness
import Attach
import LCS.SLD.LogicProgramming.Completeness.ProofsStamp

/-! # SLD.LogicProgramming.Completeness
    Formalization of Chapter 9, Section 9.5.4.
    Completeness of SLD-resolution as a computational procedure.
-/

attribute [local instance] Classical.propDecidable
namespace LCS.SLD.LogicProgramming.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.SLD.FirstOrder
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.Method.Soundness
open LCS.SLD.LogicProgramming
open LCS.SLD.LogicProgramming.Correctness

-- ===================================================================
-- Theorem 9.5.2 (required): Helper definitions
-- ===================================================================

/-- Theorem 9.5.2 (required): A predicate asserting that a sequence
    of clauses <C_1, ..., C_p> used in the SLD-refutation has the
    property that the universal closure of each C_i is a member of
    the program P. -/
@[blueprint "chap9__theorem_9_5_2"]
def clauseSequenceInP {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (P : List (FOHornClause L hNoEq)) : Prop :=
  clauseSeqAux d P
where
  clauseSeqAux :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → List (FOHornClause L hNoEq) → Prop
    | _, .init _ _, _ => True
    | _, .step prev clause _ _ _ _ _ _ _ _ _ _, P =>
      clause ∈ P ∧ clauseSeqAux prev P

/-- Theorem 9.5.2 (required): Restriction of a substitution to a
    given list of variables. The restriction of sigma circ eta to
    z_1,...,z_q yields the substitution that maps z_i to
    (sigma circ eta)(z_i) and is the identity elsewhere. -/
@[blueprint "chap9__theorem_9_5_2"]
def substRestrict {L : Language}
    (sigma : Nat → Term L) (vars : List Nat) :
    Nat → Term L :=
  fun n =>
    if vars.contains n then sigma n
    else Term.var n

-- ===================================================================
-- Theorem 9.5.2 (required): Supporting theorems
-- ===================================================================

/-- Theorem 9.5.2 (required): A ground-term invariance lemma
    asserting that applying any substitution to a ground term yields
    the same term. Since ground terms contain no variables,
    substitution has no effect. Used in the proof to justify that
    theta_1'((neg B_1 lor ... lor neg B_n)[t_1/z_1,...,t_q/z_q])
    = (neg B_1 lor ... lor neg B_n)[t_1/z_1,...,t_q/z_q], because
    the terms t_1,...,t_q are ground terms and so the negated goal
    clause is preserved under the grounding step. -/
@[blueprint "chap9__theorem_9_5_2"]
theorem groundTermSubstInvariant {L : Language}
    (t : GroundTerm L) (sigma : Nat → Term L) :
    termSubstAll t.val sigma = t.val 

/-- Theorem 9.5.2 (required): The intermediate step showing that
    P wedge (neg B_1 lor ... lor neg B_n)[t_1/z_1,...,t_q/z_q] is
    unsatisfiable when (t_1,...,t_q) is in M(P,G). This is because
    the answer tuple makes P supset B true in every free structure,
    so P union {neg B[t/z]} is unsatisfiable.

    The hypothesis hEntails captures the semantic content of
    (t_1,...,t_q) in M(P,G): in every Herbrand structure, if all
    clauses in P hold at every assignment then negGoalClause (the negation of
    the goal body under the answer substitution) is not satisfied.
    For a goal clause (neg B_1 lor ... lor neg B_n)[t/z], this means
    B_1 and ... and B_n all hold under the answer substitution, which
    is precisely |= P supset B[t/z]. -/
@[blueprint "chap9__theorem_9_5_2"]
theorem unsatisfiableGroundInstance {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (P : List (FOHornClause L hNoEq))
    (_hDef : ∀ c ∈ P, (FOHornClause.isDefinite (hNoEq := hNoEq)) c)
    (negGoalClause : FOHornClause L hNoEq)
    (_hNeg : ¬ (negGoalClause.isDefinite (hNoEq := hNoEq)))
    -- L has at least one constant (for Herbrand universe construction)
    (hConst : Nonempty L.constSymbols)
    -- Clause formulas are well-formed for Herbrand transfer:
    -- NNF, universal-only, no equality. These hold when all atoms
    -- in the Horn clauses are predN applications (standard for
    -- logic programs without equality).
    (hClauseWF : ∀ c ∈ P ++ [negGoalClause],
      formulaIsNNF ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))) ∧
      formulaUniversalOnly ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))) ∧
      formulaNoEq ((clauseToFormula (hNoEq := hNoEq)) Afalsum (c.toFOClause (hNoEq := hNoEq))))
    -- P entails the positive goal body: in every Herbrand structure
    -- that satisfies P, negGoalClause is not satisfied.
    -- This is the semantic content of (t_1,...,t_q) in M(P,G).
    (hEntails : ∀ (H : HerbrandStructure L hNoEq),
      (∀ (s : Nat → GroundTerm L) c, c ∈ P →
        (FOHornClause.evalInHerbrand (hNoEq := hNoEq)) H c s) →
      ∀ assign : Nat → GroundTerm L, ¬ (FOHornClause.evalInHerbrand (hNoEq := hNoEq)) H negGoalClause assign) :
    (FOHornClauseSet.isUnsatisfiable (hNoEq := hNoEq)) Afalsum (P ++ [negGoalClause])

/-- Theorem 9.5.2 (required): The structural observation that
    (neg B_1 lor ... lor neg B_n)[t_1/z_1,...,t_q/z_q] is the only
    negative clause in the clause set, since all clauses in P are
    definite (each has exactly one positive literal). This enables
    application of Lemma 9.5.3. -/
@[blueprint "chap9__theorem_9_5_2"]
theorem uniqueNegativeClause {L : Language} (hNoEq : L.withoutEquality)
    (P : List (FOHornClause L hNoEq))
    (hDef : ∀ c ∈ P, (FOHornClause.isDefinite (hNoEq := hNoEq)) c)
    (negGoalClause : FOHornClause L hNoEq)
    (hNeg : ¬ (negGoalClause.isDefinite (hNoEq := hNoEq)))
    (clauseSet : List (FOHornClause L hNoEq))
    (hSet : clauseSet = P ++ [negGoalClause]) :
    ∀ c ∈ clauseSet, ¬ (c.isDefinite (hNoEq := hNoEq)) → c = negGoalClause 

/-- Theorem 9.5.2: Every singleton answer in the definite semantics is a
    common ground instance of the result of an SLD-refutation of the original
    negative query. The arbitrary program is represented in the refutation by
    a finite subtheory (SQ30, SQ35).

    The source composition σ ◦ η applies σ first and then η; hence it is
    `SubstitutionCore.substCompose eta R.resultSubstitution`. One finite-support
    η grounds all relevant result images together (SQ37, SQ39). The output
    coordinates are exactly the query's matrix variables (SQ31). -/
@[attach_debt, blueprint "chap9__theorem_9_5_2" (main := true)]
theorem sldResolution_complete {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq)
    (hDef : ∀ c ∈ lp.prog, FOHornClause.isDefinite hNoEq c)
    (hGoal : lp.qry.length = 1)
    (hAtomic : ∀ a ∈ lp.qry, a.negLiteral = none)
    (hConst : Nonempty L.constSymbols)
    (answerTuple : GroundAnswerTuple L (lp.outputVarList hNoEq).length)
    (hInSemantics : singletonAnswer answerTuple ∈
      programSemantics.isDefiniteSemantics hNoEq lp hConst ⟨hDef, hGoal, hAtomic⟩) :
    let queryAH : AntiHornClause L hNoEq :=
      lp.qry.head (fun hNil => by rw [hNil] at hGoal; simp at hGoal)
    let negGoalClause : FOHornClause L hNoEq :=
      FOHornClause.goal (hNoEq := hNoEq) (LCS.Finset.ofList queryAH.posLiterals)
    ∃ (D : List (FOHornClause L hNoEq)), (∀ c ∈ D, c ∈ lp.prog) ∧
    ∃ (cg : LCS.Finset (FOAtom L hNoEq))
      (R : FOSLDDerivation hNoEq (fun c => c ∈ D) [negGoalClause] cg),
      R.isRefutation hNoEq ∧ clauseSequenceInP hNoEq R D ∧
      ∃ (eta : Nat → Term L),
        (∃ support : List Nat, ∀ v, v ∉ support → eta v = Term.var v) ∧
        (∀ z ∈ lp.outputVarList hNoEq,
          Term.isClosed (termSubstAll (R.resultSubstitution hNoEq z) eta)) ∧
        (∀ i : Fin (lp.outputVarList hNoEq).length,
          substRestrict (SubstitutionCore.substCompose eta (R.resultSubstitution hNoEq))
            (lp.outputVarList hNoEq) ((lp.outputVarList hNoEq).get i) =
          (answerTuple i).val)

end LCS.SLD.LogicProgramming.Completeness
