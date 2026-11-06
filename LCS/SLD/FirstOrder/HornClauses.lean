import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.SLDDerivations
import Attach
import LCS.SLD.FirstOrder.HornClauses.ProofsStamp

/-! # Horn clauses in PROLOG notation (Definition 9.4.1)

Section 9.4.1: rules, facts and goals over an equality-free language, their translation to first-order clauses, simultaneous substitution on formulae, unsatisfiability of a Horn clause set and its encoding as one sentence. -/

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

/-- Definition 9.4.1: Horn clauses in an equality-free language.
    Bodies are extensional finite sets; empty goals are allowed (SQ16/SQ17). -/
@[blueprint "chap9__definition_9_4_1" (main := true)]
abbrev FOHornClause (L : Language) (_hNoEq : L.withoutEquality) := FOHornClauseCore L

namespace FOHornClause

/-- The source rule constructor, with its equality-free language boundary. -/
@[simp, blueprint "chap9__definition_9_4_1"]
def rule {L : Language} (head : FOAtomCore L) (body : LCS.Finset (FOAtomCore L))
    (hNoEq : L.withoutEquality) : FOHornClause L hNoEq := FOHornClauseCore.rule head body

/-- The source fact constructor. -/
@[simp, blueprint "chap9__definition_9_4_1"]
def fact {L : Language} (head : FOAtomCore L)
    (hNoEq : L.withoutEquality) : FOHornClause L hNoEq := FOHornClauseCore.fact head

/-- The source goal constructor; its finite body may be empty (SQ17). -/
@[simp, blueprint "chap9__definition_9_4_1"]
def goal {L : Language} (body : LCS.Finset (FOAtomCore L))
    (hNoEq : L.withoutEquality) : FOHornClause L hNoEq := FOHornClauseCore.goal body

end FOHornClause

-- ===================================================================
-- Helper: simultaneous formula substitution (all variables at once)
-- ===================================================================

/-- Definition 9.4.1 (companion): Apply a simultaneous substitution to
    all terms in a formula using the homomorphic extension termSubstAll.
    This is the formula-level analogue of termSubstAll from Unification. -/
@[blueprint "chap9__definition_9_4_1"]
def formulaSubstAll {L : Language} :
    FormulaN L → (Nat → Term L) → FormulaN L
  | .predN P args, sigma => .predN P (fun i => termSubstAll (args i) sigma)
  | .eq_ hL t1 t2, sigma => .eq_ hL (termSubstAll t1 sigma) (termSubstAll t2 sigma)
  | .conj A B, sigma => .conj (formulaSubstAll A sigma) (formulaSubstAll B sigma)
  | .disj A B, sigma => .disj (formulaSubstAll A sigma) (formulaSubstAll B sigma)
  | .impl A B, sigma => .impl (formulaSubstAll A sigma) (formulaSubstAll B sigma)
  | .neg A, sigma => .neg (formulaSubstAll A sigma)
  | .all i A, sigma => .all i (formulaSubstAll A sigma)
  | .ex i A, sigma => .ex i (formulaSubstAll A sigma)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.GroundSemantics
/-- Identity substitution is the identity on terms: applying the
    identity substitution `Term.var` leaves every term unchanged. -/
theorem termSubstAll_id_term {L : Language} (t : Term L) :
    termSubstAll t Term.var = t := by
-- BEGIN PROOF
  induction t with
  | var n => rfl
  | const c => rfl
  | func f args ih =>
    show Term.func f _ = Term.func f _
    congr 1
    funext i
    exact ih i

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.GroundSemantics
/-- Identity substitution is the identity on formulas: applying
    `Term.var` leaves every formula unchanged. This holds unconditionally
    (no groundness assumption needed) because `Term.var n = Term.var n`
    by reflexivity for every variable index `n`. -/
theorem formulaSubstAll_id {L : Language} (A : FormulaN L) :
    formulaSubstAll A Term.var = A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    show FormulaN.predN P _ = FormulaN.predN P _
    congr 1
    funext i
    exact termSubstAll_id_term (ts i)
  | eq_ hL t1 t2 =>
    show FormulaN.eq_ hL _ _ = FormulaN.eq_ hL _ _
    rw [termSubstAll_id_term t1, termSubstAll_id_term t2]
  | conj A B ihA ihB =>
    show FormulaN.conj _ _ = FormulaN.conj _ _
    rw [ihA, ihB]
  | disj A B ihA ihB =>
    show FormulaN.disj _ _ = FormulaN.disj _ _
    rw [ihA, ihB]
  | impl A B ihA ihB =>
    show FormulaN.impl _ _ = FormulaN.impl _ _
    rw [ihA, ihB]
  | neg A ih =>
    show FormulaN.neg _ = FormulaN.neg _
    rw [ih]
  | all x A ih =>
    show FormulaN.all x _ = FormulaN.all x _
    rw [ih]
  | ex x A ih =>
    show FormulaN.ex x _ = FormulaN.ex x _
    rw [ih]

-- retained: used by LCS.Examples.PrologAppend, LCS.Examples.PrologArithmetic, LCS.Examples.PrologMember, LCS.Examples.PrologPath, LCS.Examples.PrologReverse.Refutation, LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Completeness, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Structural atom substitution agrees with ambient formula
    substitution after embedding the atom. -/
theorem atomSubst_toFormula_formulaSubstAll {L : Language} (hNoEq : L.withoutEquality)
    (atom : FOAtom L hNoEq) (sigma : Nat → Term L) :
    ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma atom)).toFormula =
      formulaSubstAll atom.toFormula sigma := by
  cases atom <;> rfl

-- retained: used by LCS.Examples.PrologAppend, LCS.Examples.PrologArithmetic, LCS.Examples.PrologMember, LCS.Examples.PrologPath, LCS.Examples.PrologReverse.Program, LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- The identity substitution leaves an atomic carrier unchanged. -/
theorem atomSubst_id {L : Language} (hNoEq : L.withoutEquality)  (atom : FOAtom L hNoEq) :
    (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var atom) = atom := by
  apply FOAtomCore.toFormula_injective
  rw [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)), formulaSubstAll_id]

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.PropositionalEncoding, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness, LCS.SLD.LogicProgramming.Correctness.RefutationExamples
/-- Mapping the identity substitution over atomic carriers is the
    identity. -/
theorem map_atomSubst_id {L : Language} (hNoEq : L.withoutEquality)  (atoms : List (FOAtom L hNoEq)) :
    atoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)) = atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [List.map]
      rw [(atomSubst_id (hNoEq := by all_goals exact hNoEq)), ih]

namespace FOHornClause
open FOHornClause

/-- Definition 9.4.1 (companion): A Horn clause is definite iff it is
    a rule or a fact (has exactly one head atom). Returns True for rule
    and fact constructors, False for goal. -/
@[blueprint "chap9__definition_9_4_1"]
def isDefinite {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Prop :=
  FOHornClauseCore.isDefinite

/-- Structural head view. Unlike `headAtom`, this exposes the
    type-level atomic carrier used by the constructors. -/
@[blueprint "chap9__definition_9_4_2"]
def headFOAtom {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Option (FOAtom L hNoEq) :=
  FOHornClauseCore.headFOAtom

/-- An enumeration of the finite body, exposing its atomic carriers.
    Clause equality is independent of this enumeration (SQ16). -/
@[blueprint "chap9__definition_9_4_2"]
def bodyFOAtoms {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → List (FOAtom L hNoEq) :=
  FOHornClauseCore.bodyFOAtoms

/-- Definition 9.4.1 (companion): Translates a Horn clause in PROLOG
    notation to standard logic clause notation (as a list of FOLiterals).
    rule B:-A_1,...,A_m maps to [neg A_1,...,neg A_m, pos B];
    fact B maps to [pos B];
    goal :-A_1,...,A_m maps to [neg A_1,...,neg A_m]. -/
@[blueprint "chap9__definition_9_4_1"]
def toFOClause {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → FOClause L hNoEq :=
  FOHornClauseCore.toFOClause

-- retained: used by LCS.SLD.FirstOrder.GroundSemantics, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Completeness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem atomToFormulaQF {L : Language} (hNoEq : L.withoutEquality)  (atom : FOAtom L hNoEq) :
    isQuantifierFree atom.toFormula := by
  cases atom <;> trivial

end FOHornClause

/-- Companion helper: `clauseFV` depends only on membership of the
    underlying list, so two lists of literals with identical membership
    yield the same `clauseFV`. Used to bridge between
    `(Finset.ofList l).toList.map neg` and `l.map neg` in Ex 9.4.1. -/
theorem clauseFV_map_neg_mem_congr {L : Language} (hNoEq : L.withoutEquality)
    (l₁ l₂ : List (FOAtom L hNoEq)) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) :
    (clauseFV (L := L) (hNoEq := by all_goals exact hNoEq)) (l₁.map FOLiteralCore.neg) =
    (clauseFV (L := L) (hNoEq := by all_goals exact hNoEq)) (l₂.map FOLiteralCore.neg) := by
  funext x
  apply propext
  constructor
  · rintro ⟨lit, hLit, hV⟩
    rw [List.mem_map] at hLit
    obtain ⟨a, ha, rfl⟩ := hLit
    exact ⟨FOLiteralCore.neg a, List.mem_map.mpr ⟨a, (h a).mp ha, rfl⟩, hV⟩
  · rintro ⟨lit, hLit, hV⟩
    rw [List.mem_map] at hLit
    obtain ⟨a, ha, rfl⟩ := hLit
    exact ⟨FOLiteralCore.neg a, List.mem_map.mpr ⟨a, (h a).mpr ha, rfl⟩, hV⟩

namespace FOHornClauseSet

/-- Definition 9.4.1 (companion): A set of Horn clauses is unsatisfiable iff
    the set of their standard-logic translations (via toFOClause) is
    unsatisfiable. The formula argument `A` is retained for the chapter 9
    call sites; since the chapter 8 repair T8-56 clause-set unsatisfiability
    is formula-free (`FOClauseSet.isUnsatisfiable hNoEq S`). -/
@[blueprint "chap9__definition_9_4_1"]
def isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (S : List (FOHornClause L hNoEq)) : Prop :=
  (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) (fun c => ∃ h ∈ S, (h.toFOClause (hNoEq := by all_goals exact hNoEq)) = c)

end FOHornClauseSet

open LCS.FirstOrder.SyntaxN.Variables in
/-- Exactly the free variables of the translated clause matrix (SQ25).
    The auxiliary contradiction contributes variables only for an empty clause. -/
@[blueprint "chap9__definition_9_4_1"]
def hornClauseVarsList {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (h : FOHornClause L hNoEq) : List Nat := by
  classical
  let matrix := clauseToFormula hNoEq Afalsum h.toFOClause
  exact ((formulaVarsList matrix).filter (fun n => decide (formulaFVN matrix n))).eraseDups

/-- Definition 9.4.1 (companion): Encode a list of Horn clauses as a
    single FormulaN sentence. Each clause is mapped to the universal
    closure of its standard-logic translation (via `toFOClause` and
    `FOClause.universalClosure`); the resulting formulae are conjoined.
    The empty-list case evaluates to the universal closure of the
    `Afalsum` placeholder to stay within the NNF grammar — the SLD
    completeness pipeline only instantiates this encoding when the
    Horn-clause set is non-empty (`goals ≠ []`). -/
@[blueprint "chap9__definition_9_4_1"]
def hornClauses_to_formulaN {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) : List (FOHornClause L hNoEq) → FormulaN L
  | [] => Afalsum
  | [h] => (FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)
  | h :: rest =>
    FormulaN.conj
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h))
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum rest)

end LCS.SLD.FirstOrder
end
