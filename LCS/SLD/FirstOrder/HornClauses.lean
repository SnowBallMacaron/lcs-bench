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

end LCS.SLD.FirstOrder
end

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
namespace FOHornClause
open FOHornClause

/-- Definition 9.4.1 (companion): A Horn clause is definite iff it is
    a rule or a fact (has exactly one head atom). Returns True for rule
    and fact constructors, False for goal. -/
@[blueprint "chap9__definition_9_4_1"]
def isDefinite {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Prop :=
  FOHornClauseCore.isDefinite

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Structural head view. Unlike `headAtom`, this exposes the
    type-level atomic carrier used by the constructors. -/
@[blueprint "chap9__definition_9_4_2"]
def headFOAtom {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Option (FOAtom L hNoEq) :=
  FOHornClauseCore.headFOAtom

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An enumeration of the finite body, exposing its atomic carriers.
    Clause equality is independent of this enumeration (SQ16). -/
@[blueprint "chap9__definition_9_4_2"]
def bodyFOAtoms {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → List (FOAtom L hNoEq) :=
  FOHornClauseCore.bodyFOAtoms

/-- Definition 9.4.1 (companion): Extracts the head atom B from a rule
    or fact clause as an ambient formula. Returns some B for rule and
    fact, none for goal. -/
@[blueprint "chap9__definition_9_4_1"]
def headAtom {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Option (FormulaN L)
  | c => c.headFOAtom.map FOAtomCore.toFormula

/-- Definition 9.4.1 (companion): Extracts the body atoms A_1,...,A_m.
    Returns their ambient-formula embeddings for rule and goal, and []
    for fact. -/
@[blueprint "chap9__definition_9_4_1"]
def bodyAtoms {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → List (FormulaN L)
  | c => c.bodyFOAtoms.map FOAtomCore.toFormula

/-- Definition 9.4.1 (companion): Translates a Horn clause in PROLOG
    notation to standard logic clause notation (as a list of FOLiterals).
    rule B:-A_1,...,A_m maps to [neg A_1,...,neg A_m, pos B];
    fact B maps to [pos B];
    goal :-A_1,...,A_m maps to [neg A_1,...,neg A_m]. -/
@[blueprint "chap9__definition_9_4_1"]
def toFOClause {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → FOClause L hNoEq :=
  FOHornClauseCore.toFOClause

/-- Definition 9.4.1 (companion): The translation of a rule clause
    B:-A_1,...,A_m to the standard logic clause
    [neg A_1, ..., neg A_m, pos B]. -/
@[blueprint "chap9__definition_9_4_1"]
theorem ruleTranslation {L : Language} (hNoEq : L.withoutEquality)
    (B : FOAtom L hNoEq) (body : LCS.Finset (FOAtom L hNoEq)) :
    (FOHornClause.toFOClause (hNoEq := by all_goals exact hNoEq) (FOHornClause.rule (hNoEq := by all_goals exact hNoEq) B body)) =
      body.toList.map FOLiteralCore.neg ++ [FOLiteralCore.pos B]

/-- Definition 9.4.1 (companion): The translation of a fact clause B
    to the singleton clause [pos B]. -/
@[blueprint "chap9__definition_9_4_1"]
theorem factTranslation {L : Language} (hNoEq : L.withoutEquality)
    (B : FOAtom L hNoEq) :
    (FOHornClause.toFOClause (hNoEq := by all_goals exact hNoEq) (FOHornClause.fact (hNoEq := by all_goals exact hNoEq) B)) = [FOLiteralCore.pos B]

/-- Definition 9.4.1 (companion): The translation of a goal clause
    :-A_1,...,A_m to the clause [neg A_1, ..., neg A_m]. -/
@[blueprint "chap9__definition_9_4_1"]
theorem goalTranslation {L : Language} (hNoEq : L.withoutEquality)
    (body : LCS.Finset (FOAtom L hNoEq)) :
    (FOHornClause.toFOClause (hNoEq := by all_goals exact hNoEq) (FOHornClause.goal (hNoEq := by all_goals exact hNoEq) body)) = body.toList.map FOLiteralCore.neg

/-- Lemma 9.4.1 (required helper): All atoms (head and body) in the
    Horn clause are quantifier-free. This holds for all SLD clause-form
    formulas (atoms are predN or eq_). Used as a hypothesis in the
    soundness statement. -/
@[blueprint "chap9__lemma_9_4_1"]
def allAtomsQF {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Prop
  | FOHornClauseCore.rule head body =>
      isQuantifierFree head.toFormula ∧
        ∀ a ∈ body, isQuantifierFree a.toFormula
  | FOHornClauseCore.fact head => isQuantifierFree head.toFormula
  | FOHornClauseCore.goal body => ∀ a ∈ body, isQuantifierFree a.toFormula

-- retained: used by LCS.SLD.FirstOrder.GroundSemantics, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Completeness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem atomToFormulaQF {L : Language} (hNoEq : L.withoutEquality)  (atom : FOAtom L hNoEq) :
    isQuantifierFree atom.toFormula := by
  cases atom <;> trivial

-- retained: used by LCS.Examples.PrologAppend, LCS.Examples.PrologArithmetic, LCS.Examples.PrologMember, LCS.Examples.PrologPath, LCS.Examples.PrologReverse.Program
theorem allAtomsQF_derived {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq) :
    (c.allAtomsQF (hNoEq := by all_goals exact hNoEq)) := by
  cases c with
  | rule head body =>
      exact ⟨(atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) head, fun atom _ => (atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) atom⟩
  | fact head =>
      exact (atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) head
  | goal body =>
      exact fun atom _ => (atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) atom





-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- All atoms (head and body) in the Horn clause are atomic (predicate
    application or equality). Stronger than `allAtomsQF`: atomic means
    the formula is `.predN` or `.eq_` rather than just quantifier-free.
    Required by the §7.6 Skolemization bridge, which needs `source.isNNF`
    on the Horn-clause universal-closure encoding — non-atomic Horn
    atoms would introduce embedded connectives that break NNF. -/
def allAtomsAtomic {L : Language} (hNoEq : L.withoutEquality) : FOHornClause L hNoEq → Prop
  | FOHornClauseCore.rule head body =>
    FormulaN.isAtomic head.toFormula = true ∧
      ∀ a ∈ body, FormulaN.isAtomic a.toFormula = true
  | FOHornClauseCore.fact head => FormulaN.isAtomic head.toFormula = true
  | FOHornClauseCore.goal body => ∀ a ∈ body, FormulaN.isAtomic a.toFormula = true

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.Soundness
/-- Atomicity is a projection of the structural carrier, not a
    caller-supplied side condition. -/
theorem allAtomsAtomic_derived {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq) :
    (c.allAtomsAtomic (hNoEq := by all_goals exact hNoEq)) := by
  cases c <;>
    simp [allAtomsAtomic, FOAtomCore.toFormula_isAtomic]

end FOHornClause
end LCS.SLD.FirstOrder
end

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
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

-- ===================================================================
-- Definition 9.4.2: First-order SLD-derivation
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The exact per-position MGU certificate for two predicate atoms.
    `atomUnifPairs?` rejects predicate mismatches and equality atoms
    visibly; on success, `IsPairwiseMGU` supplies the unifier,
    finite-support, and universal factorization conditions of §8.4. -/
@[blueprint "chap9__definition_9_4_2"]
def IsAtomMGU {L : Language} (hNoEq : L.withoutEquality)  (reference atom : FOAtom L hNoEq)
    (sigma : Nat → Term L) : Prop :=
  ∃ pairs : List (Term L × Term L),
    (atomUnifPairs? (hNoEq := by all_goals exact hNoEq)) reference atom = some pairs ∧
      IsPairwiseMGU sigma pairs

-- ATTACH-BLOCKER: private declaration
private theorem predN_subst_eq_of_isPairwiseUnifier {L : Language} (hNoEq : L.withoutEquality)
    (P : L.predSymbols)
    (referenceArgs args : Fin (L.predArity P) → Term L)
    (sigma : Nat → Term L)
    (hUnif : IsPairwiseUnifier sigma
      (List.ofFn (fun i => (referenceArgs i, args i)))) :
    (FOAtomCore.predN P referenceArgs).subst (hNoEq := by all_goals exact hNoEq) sigma =
      (FOAtomCore.predN P args).subst (hNoEq := by all_goals exact hNoEq) sigma := by
  show FOAtomCore.predN P _ = FOAtomCore.predN P _
  congr 1
  funext i
  exact hUnif _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A pairwise unifier of the exact equation system extracted from two
    atoms makes their substituted forms equal. -/
theorem atom_subst_eq_of_pairwise {L : Language} (hNoEq : L.withoutEquality)
    (reference atom : FOAtom L hNoEq) (sigma : Nat → Term L)
    {pairs : List (Term L × Term L)}
    (hPairs : (atomUnifPairs? (hNoEq := by all_goals exact hNoEq)) reference atom = some pairs)
    (hUnif : IsPairwiseUnifier sigma pairs) :
    (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma reference) = (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma atom) := by
  classical
  cases reference with
  | predN P referenceArgs =>
      cases atom with
      | predN Q args =>
          by_cases hPQ : P = Q
          · subst Q
            rw [(atomUnifPairs?_predN_same (hNoEq := by all_goals exact hNoEq))] at hPairs
            cases hPairs
            exact (predN_subst_eq_of_isPairwiseUnifier (hNoEq := by all_goals exact hNoEq))
              P referenceArgs args sigma hUnif
          · simp [atomUnifPairs?, hPQ] at hPairs
      | eq_ hL lhs rhs => simp [atomUnifPairs?] at hPairs
  | eq_ hL lhs rhs =>
      cases atom <;> simp [atomUnifPairs?] at hPairs

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The unification equality contained in an atom MGU certificate. -/
theorem IsAtomMGU.subst_eq {L : Language} (hNoEq : L.withoutEquality)
    {reference atom : FOAtom L hNoEq} {sigma : Nat → Term L}
    (h : (IsAtomMGU (hNoEq := by all_goals exact hNoEq)) reference atom sigma) :
    (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma reference) = (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma atom) := by
  rcases h with ⟨pairs, hPairs, hMGU⟩
  exact (atom_subst_eq_of_pairwise (hNoEq := by all_goals exact hNoEq)) reference atom sigma hPairs hMGU.1

-- ATTACH-BLOCKER: private declaration
private theorem identitySubst_isPairwiseMGU_refl_ofFn {L : Language}
    {n : Nat} (args : Fin n → Term L) :
    IsPairwiseMGU identitySubst
      (List.ofFn (fun i => (args i, args i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hPair
    rfl
  · intro x hSupport
    exact (hSupport rfl).elim
  · intro sigmaOther _
    refine ⟨sigmaOther, ?_⟩
    intro x
    rfl

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Identity is an MGU of a predicate atom with itself. -/
theorem identitySubst_isAtomMGU_predN {L : Language} (hNoEq : L.withoutEquality)
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L) :
    (IsAtomMGU (hNoEq := by all_goals exact hNoEq)) (.predN P args) (.predN P args) identitySubst := by
  refine ⟨List.ofFn (fun i => (args i, args i)), ?_, ?_⟩
  · exact (atomUnifPairs?_predN_same (hNoEq := by all_goals exact hNoEq)) P args args
  · exact identitySubst_isPairwiseMGU_refl_ofFn args

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- In a language without equality, identity is an MGU of equal atoms. -/
theorem identitySubst_isAtomMGU_of_eq_noEquality {L : Language} (hNoEq : L.withoutEquality)
     {reference atom : FOAtom L hNoEq}
    (hEq : reference = atom) :
    (IsAtomMGU (hNoEq := by all_goals exact hNoEq)) reference atom identitySubst := by
  subst atom
  cases reference with
  | predN P args => exact (identitySubst_isAtomMGU_predN (hNoEq := by all_goals exact hNoEq)) P args
  | eq_ hL lhs rhs =>
      rw [Language.withoutEquality] at hNoEq
      rw [hNoEq] at hL
      exact Bool.noConfusion hL

/-- Definition 9.4.2: An SLD-derivation for S = D ∪ {G_1,...,G_q} is a
    sequence <N_0,...,N_p> with N_0 a goal clause from S and each
    N_{i+1} an MGU-resolvent with a definite clause in D. This indexed
    inductive bakes the textbook side conditions into the constructor
    fields:
    (1) init: goal ∈ goals, and the index (currentGoal) is precisely
        the extracted body atoms of the chosen goal clause;
    (2) step: clause ∈ D, clause.isDefinite, the selected atom A_k
        is in prev's current goal, clause's head is some headA,
        sigma is an MGU of A_k and rho(headA), (Id, rho) is a separating
        pair for the current goal and the locally renamed input clause
        (SQ22/SQ23). The index of the resulting derivation is
        the current goal clause obtained by taking the union of
        prev's goal minus A_k with the rho-renamed body atoms of the
        definite clause and applying sigma (as a Finset, per Gallier
        §4.2.1 Def 4.2.1: clauses are SETS of literals). -/
@[blueprint "chap9__definition_9_4_2" (main := true)]
abbrev FOSLDDerivation {L : Language} (hNoEq : L.withoutEquality)
    (D : Set (FOHornClause L hNoEq)) (goals : List (FOHornClause L hNoEq)) :=
  FOSLDDerivationCore D goals

namespace FOSLDDerivation
export FOSLDDerivationCore (init step)
end FOSLDDerivation

end LCS.SLD.FirstOrder
end

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
namespace FOSLDDerivation

/-- Definition 9.4.2 (companion): The number of resolution steps in
    the derivation. init has length 0; step increments by 1. -/
@[blueprint "chap9__definition_9_4_2"]
def length {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → Nat
  | .init _ _ => 0
  | .step prev _ _ _ _ _ _ _ _ _ _ _ => (length (hNoEq := by all_goals exact hNoEq) prev) + 1

/-- Definition 9.4.2 (companion): An SLD-derivation is an
    SLD-refutation iff its current goal (the type index) is the empty
    Finset (N_p = square). -/
@[blueprint "chap9__definition_9_4_2"]
def isRefutation {L : Language} (hNoEq : L.withoutEquality)  {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)}
    (_ : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal) : Prop :=
  currentGoal = (∅ : LCS.Finset (FOAtom L hNoEq))

/-- Definition 9.4.2 (companion): For a step node, returns the atom
    A_k selected from the previous currentGoal. For init,
    returns none. -/
@[blueprint "chap9__definition_9_4_2"]
def selectedAtom {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → Option (FOAtom L hNoEq)
  | .init _ _ => none
  | .step _ _ _ _ Ak _ _ _ _ _ _ _ => some Ak

/-- The ordered original input occurrences N₀, C₁, …, Cₚ (SQ21).
    Repeated clause uses remain repeated; renamings belong to the steps. -/
@[blueprint "chap9__definition_9_4_2"]
def inputClauses {L : Language} (hNoEq : L.withoutEquality)
    {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    FOSLDDerivation hNoEq D goals currentGoal → List (FOHornClause L hNoEq)
  | .init goal _ => [goal]
  | .step prev clause _ _ _ _ _ _ _ _ _ _ => inputClauses hNoEq prev ++ [clause]

/-- All residual goals in order, including the initial and final goals (SQ20). -/
@[blueprint "chap9__definition_9_4_2"]
def goalSequence {L : Language} (hNoEq : L.withoutEquality)
    {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    FOSLDDerivation hNoEq D goals currentGoal → List (LCS.Finset (FOAtom L hNoEq))
  | .init goal _ => [LCS.Finset.ofList goal.bodyFOAtoms]
  | .step prev _ _ _ _ _ _ _ _ _ _ _ => goalSequence hNoEq prev ++ [currentGoal]

/-- Definition 9.4.2 (companion): The composition of all substitutions
    accumulated through the derivation. For init, returns the identity.
    For step, composes the current (rho, sigma) pair with the
    accumulated substitution from prev. -/
@[blueprint "chap9__definition_9_4_2"]
def resultSubstitution {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → (Nat → Term L)
  | .init _ _ => Term.var
  | .step prev _ _ _ _ _ _ _ rho sigma _ _ =>
    SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho) ((resultSubstitution (hNoEq := by all_goals exact hNoEq)) prev)

/-- Definition 9.4.2 (companion): The selected atom of the first
    resolution step in the derivation (the innermost step wrapping
    init). For init (no steps), returns none. For a single step,
    returns the selected atom at that step. For nested steps,
    recurses into the previous derivation. -/
@[blueprint "chap9__definition_9_4_2"]
def firstSelectedAtom {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → Option (FOAtom L hNoEq)
  | .init _ _ => none
  | .step prev _ _ _ Ak _ _ _ _ _ _ _ =>
    match prev with
    | .init _ _ => some Ak
    | .step .. => (firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) prev

end FOSLDDerivation
end LCS.SLD.FirstOrder
end

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

/-- Example 9.4.1 (companion type): Predicate symbols for the addition
    example: one ternary predicate add. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddPred : Type where
  | add : ExAddPred

/-- Example 9.4.1 (companion type): Function symbols for the addition
    example: one unary function succ. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddFunc : Type where
  | succ : ExAddFunc

/-- Example 9.4.1 (companion type): Constant symbols for the addition
    example: zero. -/
@[blueprint "chap9__example_9_4_1"]
inductive ExAddConst : Type where
  | zero : ExAddConst

/-- Example 9.4.1 (companion): The first-order language for the
    addition example with predicate add (rank 3), function succ
    (rank 1), constant zero, and no equality. -/
@[blueprint "chap9__example_9_4_1"]
def exAddLang : Language where
  funSymbols := ExAddFunc
  funArity := fun | .succ => 1
  constSymbols := ExAddConst
  predSymbols := ExAddPred
  predArity := fun | .add => 3
  hasEquality := false

/-- Example 9.4.1 (companion): build a Fin 3 -> alpha function from three values. -/
@[blueprint "chap9__example_9_4_1"]
def addVec3 (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- Example 9.4.1 (companion): build a Fin 1 -> alpha function from one value. -/
@[blueprint "chap9__example_9_4_1"]
def addVec1 (a : α) : Fin 1 → α
  | ⟨0, _⟩ => a

/-- Example 9.4.1 (companion): build the add(t1, t2, t3) atomic formula. -/
@[blueprint "chap9__example_9_4_1"]
def mkAdd (t1 t2 t3 : Term exAddLang) : FOAtom exAddLang rfl :=
  FOAtomCore.predN ExAddPred.add (addVec3 t1 t2 t3)

/-- Example 9.4.1 (companion): build succ(t). -/
@[blueprint "chap9__example_9_4_1"]
def mkSucc (t : Term exAddLang) : Term exAddLang :=
  Term.func ExAddFunc.succ (addVec1 t)

/-- Example 9.4.1 (companion): zero constant. -/
@[blueprint "chap9__example_9_4_1"]
def zeroTm : Term exAddLang :=
  Term.const ExAddConst.zero

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem termSubstAll_zeroTm (sigma : Nat → Term exAddLang) :
    termSubstAll zeroTm sigma = zeroTm := by
  rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): push structural atom
    substitution through `mkAdd`. -/
theorem formulaSubstAll_mkAdd (t1 t2 t3 : Term exAddLang)
    (σ : Nat → Term exAddLang) :
    (mkAdd t1 t2 t3).subst (hNoEq := by all_goals rfl) σ =
      mkAdd (termSubstAll t1 σ) (termSubstAll t2 σ) (termSubstAll t3 σ) := by
  -- BEGIN PROOF
  unfold mkAdd FOAtomCore.subst FOAtomCore.mapTerms
  change FOAtomCore.predN ExAddPred.add
      (fun i => termSubstAll (addVec3 t1 t2 t3 i) σ) =
    FOAtomCore.predN ExAddPred.add
      (addVec3 (termSubstAll t1 σ)
        (termSubstAll t2 σ) (termSubstAll t3 σ))
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): push `termSubstAll σ` through `mkSucc`. -/
theorem termSubstAll_mkSucc (t : Term exAddLang) (σ : Nat → Term exAddLang) :
    termSubstAll (mkSucc t) σ = mkSucc (termSubstAll t σ) := by
  -- BEGIN PROOF
  unfold mkSucc
  simp only [termSubstAll]
  apply congrArg
  funext i
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): FV of `mkAdd` = union of FVs. -/
theorem formulaVars_mkAdd (t1 t2 t3 : Term exAddLang) (n : Nat) :
    (mkAdd t1 t2 t3).vars n ↔
      termVars t1 n ∨ termVars t2 n ∨ termVars t3 n := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact Or.inl hi
    | 1, _ => exact Or.inr (Or.inl hi)
    | 2, _ => exact Or.inr (Or.inr hi)
  · rintro (h | h | h)
    · exact ⟨⟨0, by decide⟩, h⟩
    · exact ⟨⟨1, by decide⟩, h⟩
    · exact ⟨⟨2, by decide⟩, h⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): FV of `mkSucc` = FV of argument. -/
theorem termVars_mkSucc (t : Term exAddLang) (n : Nat) :
    termVars (mkSucc t) n ↔ termVars t n := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨i, hi2⟩
    match i, hi2 with
    | 0, _ => exact hi
  · intro h
    exact ⟨⟨0, by decide⟩, h⟩



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): s(0) is ground. -/
theorem termVars_mkSuccZero (x : Nat) : ¬ termVars (mkSucc zeroTm) x := by
  -- BEGIN PROOF
  rw [termVars_mkSucc]; exact id

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): termVars on `Term.var n`. -/
theorem termVars_var (n x : Nat) :
    termVars (L := exAddLang) (Term.var n) x ↔ x = n := Iff.rfl

-- retained: used by LCS.Examples.PrologArithmetic
/-- Example 9.4.1 (companion helper): termVars on `zeroTm`. -/
theorem termVars_zero_iff (x : Nat) : termVars zeroTm x ↔ False := Iff.rfl

/-- Example 9.4.1 (companion): The fact clause C_1: add(X, 0, X).
    Variables: X = var 0. Encoded as
    FOHornClause.fact (hNoEq := by all_goals rfl) (add(var 0, const zero, var 0)). -/
@[blueprint "chap9__example_9_4_1"]
def exAddClause_C1 : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.fact (hNoEq := by all_goals rfl) (mkAdd (Term.var 0) zeroTm (Term.var 0))

/-- Example 9.4.1 (companion): The rule clause C_2:
    add(X, succ(Y), succ(Z)) :- add(X, Y, Z).
    Variables: X = var 0, Y = var 1, Z = var 2.
    Encoded as FOHornClause.rule (hNoEq := by all_goals rfl)
      (add(var 0, succ(var 1), succ(var 2)))
      [add(var 0, var 1, var 2)]. -/
@[blueprint "chap9__example_9_4_1"]
def exAddClause_C2 : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.rule (hNoEq := by all_goals rfl)
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2)))
    (LCS.Finset.singleton (mkAdd (Term.var 0) (Term.var 1) (Term.var 2)))

/-- Example 9.4.1 (companion): The goal clause
    :- add(succ(0), V, succ(succ(0))).
    Variable: V = var 3.
    Encoded as FOHornClause.goal (hNoEq := by all_goals rfl)
      [add(succ(zero), var 3, succ(succ(zero)))]. -/
@[blueprint "chap9__example_9_4_1"]
def exAddGoal : FOHornClause exAddLang (by all_goals rfl) :=
  FOHornClause.goal (hNoEq := by all_goals rfl)
    (LCS.Finset.singleton (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV exAddClause_C2.toFOClause` ⊆ {0, 1, 2}. -/
theorem exAddClause_C2_FV_subset (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) x →
      x = 0 ∨ x = 1 ∨ x = 2 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty] at hMem
  rcases hMem with rfl | rfl
  · -- .neg (mkAdd (var 0) (var 1) (var 2))
    change FOAtomCore.vars (mkAdd (Term.var 0) (Term.var 1) (Term.var 2)) x at hV
    rw [formulaVars_mkAdd] at hV
    rcases hV with h | h | h <;> simp [termVars_var] at h <;> omega
  · -- .pos (mkAdd (var 0) (s (var 1)) (s (var 2)))
    change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) x at hV
    rw [formulaVars_mkAdd, termVars_mkSucc, termVars_mkSucc] at hV
    rcases hV with h | h | h <;> simp [termVars_var] at h <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV exAddClause_C1.toFOClause` ⊆ {0}. -/
theorem exAddClause_C1_FV_subset (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C1.toFOClause (hNoEq := by all_goals rfl)) x → x = 0 := by
  -- BEGIN PROOF
  rintro ⟨lit, hMem, hV⟩
  simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton] at hMem
  subst hMem
  change FOAtomCore.vars (mkAdd (Term.var 0) zeroTm (Term.var 0)) x at hV
  rw [formulaVars_mkAdd] at hV
  rcases hV with h | h | h
  · simp [termVars_var] at h; exact h
  · exact absurd h id
  · simp [termVars_var] at h; exact h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `0 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_0 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 0
    rw [formulaVars_mkAdd]; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `1 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_1 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 1 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 1
    rw [formulaVars_mkAdd]; right; left; rw [termVars_mkSucc]; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `2 ∈ clauseFV exAddClause_C2.toFOClause`. -/
theorem exAddClause_C2_FV_2 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C2.toFOClause (hNoEq := by all_goals rfl)) 2 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos
    (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty]
  · change FOAtomCore.vars
      (mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2))) 2
    rw [formulaVars_mkAdd]; right; right; rw [termVars_mkSucc]; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): `0 ∈ clauseFV exAddClause_C1.toFOClause`. -/
theorem exAddClause_C1_FV_0 :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl)) (exAddClause_C1.toFOClause (hNoEq := by all_goals rfl)) 0 := by
  -- BEGIN PROOF
  refine ⟨FOLiteralCore.pos (mkAdd (Term.var 0) zeroTm (Term.var 0)), ?_, ?_⟩
  · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.toFOClause, FOHornClauseCore.toFOClause, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton]
  · change FOAtomCore.vars (mkAdd (Term.var 0) zeroTm (Term.var 0)) 0
    rw [formulaVars_mkAdd]; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV (exAddGoal.bodyFOAtoms.map FOLiteral.neg) x ↔ x = 3`.
    The initial goal's clause-form FV is exactly {3}. -/
theorem exAddGoal_body_FV_eq_3 (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
        ([mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))].map
           FOLiteralCore.neg) x ↔ x = 3 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    change FOAtomCore.vars
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))) x at hV
    rw [formulaVars_mkAdd, termVars_mkSucc, termVars_mkSucc,
        termVars_mkSucc] at hV
    rcases hV with h | h | h
    · exact absurd h id
    · simpa [termVars_var] using h
    · exact absurd h id
  · rintro rfl
    refine ⟨FOLiteralCore.neg
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))) 3
      rw [formulaVars_mkAdd]; right; left; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper):
    `clauseFV ([mkAdd (s 0) (var 5) (s 0)].map FOLiteral.neg) x ↔ x = 5`.
    This is the current goal of `exAddSLDStep1` after all rho/sigma are
    applied, and is the `prev` goal feeding `exAddSLDStep2`. -/
theorem exAddStep1_goal_FV_eq_5 (x : Nat) :
    (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
        ([mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)].map
           FOLiteralCore.neg) x ↔ x = 5 := by
  -- BEGIN PROOF
  constructor
  · rintro ⟨lit, hMem, hV⟩
    simp at hMem
    subst hMem
    change FOAtomCore.vars
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)) x at hV
    rw [formulaVars_mkAdd] at hV
    rcases hV with h | h | h
    · exact absurd h (termVars_mkSuccZero _)
    · simpa [termVars_var] using h
    · exact absurd h (termVars_mkSuccZero _)
  · rintro rfl
    refine ⟨FOLiteralCore.neg
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)), ?_, ?_⟩
    · simp
    · change FOAtomCore.vars
        (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)) 5
      rw [formulaVars_mkAdd]; right; left; rfl

/-- Example 9.4.1: The logic program [C_1, C_2] axiomatizing addition
    of natural numbers. -/
@[blueprint "chap9__example_9_4_1" (main := true)]
def exAdditionProgram : List (FOHornClause exAddLang (by all_goals rfl)) :=
  [exAddClause_C1, exAddClause_C2]

/-- Example 9.4.1 (companion): The goal list for the addition example,
    containing the single goal clause to be refuted. -/
@[blueprint "chap9__example_9_4_1"]
def exAddGoals : List (FOHornClause exAddLang (by all_goals rfl)) :=
  [exAddGoal]

/-- Example 9.4.1 (companion): The initial derivation node N_0 for the
    goal :- add(succ(0), V, succ(succ(0))). Indexed by the body atoms of
    exAddGoal (a singleton list containing the add atom). -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep0 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
    (LCS.Finset.ofList
      [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]) := by
  have h := FOSLDDerivation.init (D := fun c => c ∈ exAdditionProgram) (goals := exAddGoals)
    exAddGoal (List.Mem.head _)
  simpa [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] using h

/-- Example 9.4.1 (companion): rho_1 renames C_2's variables apart.
    X=0 -> 4, Y=1 -> 5, Z=2 -> 6; identity elsewhere. -/
@[blueprint "chap9__example_9_4_1"]
def exAddRho1 : Nat → Term exAddLang
  | 0 => Term.var 4
  | 1 => Term.var 5
  | 2 => Term.var 6
  | n => Term.var n

/-- Example 9.4.1 (companion): sigma_1 = MGU of
    add(succ(0),V,succ(succ(0))) and rho_1(add(X,succ(Y),succ(Z))) =
    add(var4,succ(var5),succ(var6)).
    var 3 -> succ(var 5), var 4 -> succ(0), var 6 -> succ(0). -/
@[blueprint "chap9__example_9_4_1"]
def exAddSigma1 (n : Nat) : Term exAddLang :=
  if n = 3 then mkSucc (Term.var 5)
  else if n = 4 then mkSucc zeroTm
  else if n = 6 then mkSucc zeroTm
  else Term.var n

-- ATTACH-BLOCKER: private declaration
def exAddPairs1 : List (Term exAddLang × Term exAddLang) :=
  List.ofFn fun i : Fin 3 =>
    (addVec3 (mkSucc zeroTm) (Term.var 3)
      (mkSucc (mkSucc zeroTm)) i,
     addVec3 (Term.var 4) (mkSucc (Term.var 5))
      (mkSucc (Term.var 6)) i)

-- ATTACH-BLOCKER: private declaration
theorem exAddPairs1_eq :
    exAddPairs1 =
      [(mkSucc zeroTm, Term.var 4),
        (Term.var 3, mkSucc (Term.var 5)),
        (mkSucc (mkSucc zeroTm), mkSucc (Term.var 6))] := by
  unfold exAddPairs1
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

-- ATTACH-BLOCKER: private declaration
theorem exAddSigma1_isPairwiseMGU :
    IsPairwiseMGU exAddSigma1 exAddPairs1 := by
  rw [exAddPairs1_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_zeroTm,
        termSubstAll_mkSucc]
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_mkSucc]
    rcases List.mem_singleton.mp hPair with rfl
    simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll, termSubstAll_zeroTm,
      termSubstAll_mkSucc]
  · intro x hx
    by_cases h3 : x = 3
    · subst x
      refine ⟨(Term.var 3, mkSucc (Term.var 5)), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inl rfl
    by_cases h4 : x = 4
    · subst x
      refine ⟨(mkSucc zeroTm, Term.var 4), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inr rfl
    by_cases h6 : x = 6
    · subst x
      refine ⟨(mkSucc (mkSucc zeroTm), mkSucc (Term.var 6)),
        by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1], ?_⟩
      exact Or.inr ⟨⟨0, by decide⟩, rfl⟩
    exact (hx (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, h3, h4, h6])).elim
  · intro sigmaOther hOther
    refine ⟨sigmaOther, ?_⟩
    intro x
    have h1 := hOther (mkSucc zeroTm, Term.var 4)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    have h2 := hOther (Term.var 3, mkSucc (Term.var 5))
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    have h3 := hOther
      (mkSucc (mkSucc zeroTm), mkSucc (Term.var 6))
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs1])
    by_cases hx3 : x = 3
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_mkSucc] at h2
      simpa [SubstitutionCore.substCompose, exAddSigma1, termSubstAll,
        termSubstAll_mkSucc] using h2
    by_cases hx4 : x = 4
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h1
      simpa [SubstitutionCore.substCompose, exAddSigma1, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] using h1.symm
    by_cases hx6 : x = 6
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h3
      have hArgs := eq_of_heq (Term.func.inj h3).2
      have hArg := congrFun hArgs (0 : Fin 1)
      calc
        sigmaOther 6 = mkSucc zeroTm := by
          simpa [mkSucc, addVec1] using hArg.symm
        _ = termSubstAll (exAddSigma1 6) sigmaOther := by
          simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma1, termSubstAll_mkSucc,
            termSubstAll_zeroTm]
        _ = SubstitutionCore.substCompose sigmaOther exAddSigma1 6 := rfl
    simp [SubstitutionCore.substCompose, exAddSigma1, termSubstAll, hx3, hx4, hx6]

@[blueprint "chap9__example_9_4_1"]
theorem exAddSigma1_isAtomMGU :
    (IsAtomMGU (hNoEq := by all_goals rfl))
      (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))
      ((mkAdd (Term.var 0) (mkSucc (Term.var 1))
          (mkSucc (Term.var 2))).subst (hNoEq := by all_goals rfl) exAddRho1)
      exAddSigma1


/-- Example 9.4.1 (companion): First SLD step: resolve goal
    :- add(succ(0), V, succ(succ(0))) with C_2 using separating
    renaming rho_1 (renaming C_2 variables to fresh indices) and
    MGU sigma_1, yielding :- add(succ(0), Y_2, succ(0)).

    Built as a direct `FOSLDDerivation.step` onto `exAddSLDStep0`.
    The per-field side conditions are the MGU certificate and
    local separating-pair conditions for
    rho_1 (disjoint rename of 0..2 to 4..6). Each reduces by
    Fin-case decomposition / clauseFV enumeration and is left as a
    per-field `sorry`. The whole-value construction is NOT sorry —
    the derivation shape is a real `.step` term. -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep1 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
    (((
      (LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)) :=
  FOSLDDerivation.step
    (prev := exAddSLDStep0)
    (clause := exAddClause_C2)
    (hClause := by change exAddClause_C2 ∈ exAdditionProgram; simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAdditionProgram])
    (hDef := by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.isDefinite, FOHornClauseCore.isDefinite, FOHornClauseCore.body, finset_toList_empty])
    (rho := exAddRho1)
    (sigma := exAddSigma1)
    (Ak := mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))
    (headA := mkAdd (Term.var 0) (mkSucc (Term.var 1)) (mkSucc (Term.var 2)))
    (hAk := by simp [LCS.Finset.mem_ofList])
    (hHead := by rfl)
    (hMGU := exAddSigma1_isAtomMGU)
    (hSep := by
      -- prev goal (as Finset) = {add(s(0), V 3, s(s 0))}, FV = {3}.
      -- Clause = C_2, FV = {0, 1, 2}. rho = exAddRho1 renames to {4, 5, 6}.
      -- Reduce clauseFV of (Finset.ofList [atom]).toList via membership congr.
      have hCongr : (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
          ((LCS.Finset.ofList
            [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).toList.map
              FOLiteralCore.neg) =
          (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
          ([mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))].map
              FOLiteralCore.neg) := by
        apply (clauseFV_map_neg_mem_congr (hNoEq := by all_goals rfl))
        intro a
        rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      change IsSeparatingPair (L := exAddLang) (hNoEq := rfl) Term.var exAddRho1 _ _
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- substIsVarOnSet Term.var (FV prev)
        intro x _; exact ⟨x, rfl⟩
      · -- substIsVarOnSet exAddRho1 (FV C_2)
        intro x _
        rcases x with _ | _ | _ | n
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨n + 3, rfl⟩
      · -- injective for Term.var on prev: trivial
        intro x y _ _ h; cases h; rfl
      · -- injective for exAddRho1 on FV(C_2) ⊆ {0, 1, 2}
        intro x y hx hy h
        have hxmem := exAddClause_C2_FV_subset x hx
        have hymem := exAddClause_C2_FV_subset y hy
        rcases hxmem with rfl | rfl | rfl <;>
          rcases hymem with rfl | rfl | rfl <;>
            first | rfl | simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho1] at h
      · -- Range disjointness.
        -- Range of Term.var on FV(prev) = {3}.
        -- Range of exAddRho1 on FV(C_2) ⊆ {0,1,2} = {4,5,6}.
        funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          rw [exAddGoal_body_FV_eq_3] at hPrev
          subst hPrev
          have hn3 : n = 3 :=
            (Term.var.injEq (L := exAddLang) _ _).mp hEq₁ |>.symm
          subst hn3
          have hx₂mem := exAddClause_C2_FV_subset x₂ hClause
          rcases hx₂mem with rfl | rfl | rfl <;> simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho1] at hEq₂
        · intro h; exact absurd h id
      · -- Support of Term.var: identity everywhere.
        intro _ _; rfl
      · -- Support of exAddRho1: identity outside {0, 1, 2}.
        intro x hx
        rcases x with _ | _ | _ | n
        · exfalso; exact hx exAddClause_C2_FV_0
        · exfalso; exact hx exAddClause_C2_FV_1
        · exfalso; exact hx exAddClause_C2_FV_2
        · rfl)


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 9.4.1 (companion helper): The type index of `exAddSLDStep1`
    equals the Finset with the single atom
    `mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)` as its sole
    element. -/
theorem exAddStep1_currentGoal :
    (((
      (LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)) =
    LCS.Finset.ofList
      [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] := by
  -- BEGIN PROOF
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [LCS.Finset.mem_union] at hb
    rcases hb with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨a', ha', rfl⟩ := himg
      simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha'
      subst ha'
      unfold exAddRho1 exAddSigma1
      simp [formulaSubstAll_mkAdd, termSubstAll_mkSucc]
      rfl
  · intro h
    simp at h
    subst h
    refine ⟨(mkAdd (Term.var 0) (Term.var 1) (Term.var 2)).subst (hNoEq := by all_goals rfl)
      exAddRho1, ?_, ?_⟩
    · rw [LCS.Finset.mem_union]
      right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨mkAdd (Term.var 0) (Term.var 1) (Term.var 2), ?_, rfl⟩
      simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, finset_toList_singleton, exAddClause_C2, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty]
    · unfold exAddRho1 exAddSigma1
      simp [formulaSubstAll_mkAdd, termSubstAll_mkSucc]
      rfl

/-- Example 9.4.1 (companion): rho_2 renames C_1's variable X apart. -/
@[blueprint "chap9__example_9_4_1"]
def exAddRho2 : Nat → Term exAddLang
  | 0 => Term.var 7
  | n => Term.var n

/-- Example 9.4.1 (companion): sigma_2 = MGU of
    add(succ(0),Y_2,succ(0)) and rho_2(add(X,0,X)) = add(var7,0,var7).
    var 5 -> 0, var 7 -> succ(0). -/
@[blueprint "chap9__example_9_4_1"]
def exAddSigma2 (n : Nat) : Term exAddLang :=
  if n = 5 then zeroTm
  else if n = 7 then mkSucc zeroTm
  else Term.var n

-- ATTACH-BLOCKER: private declaration
def exAddPairs2 : List (Term exAddLang × Term exAddLang) :=
  List.ofFn fun i : Fin 3 =>
    (addVec3 (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm) i,
     addVec3 (Term.var 7) zeroTm (Term.var 7) i)

-- ATTACH-BLOCKER: private declaration
theorem exAddPairs2_eq :
    exAddPairs2 =
      [(mkSucc zeroTm, Term.var 7),
        (Term.var 5, zeroTm),
        (mkSucc zeroTm, Term.var 7)] := by
  unfold exAddPairs2
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

-- ATTACH-BLOCKER: private declaration
theorem exAddSigma2_isPairwiseMGU :
    IsPairwiseMGU exAddSigma2 exAddPairs2 := by
  rw [exAddPairs2_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm,
        termSubstAll_mkSucc]
    rcases List.mem_cons.mp hPair with rfl | hPair
    · simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm]
    rcases List.mem_singleton.mp hPair with rfl
    simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, termSubstAll, termSubstAll_zeroTm,
      termSubstAll_mkSucc]
  · intro x hx
    by_cases h5 : x = 5
    · subst x
      refine ⟨(Term.var 5, zeroTm), by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2], Or.inl rfl⟩
    by_cases h7 : x = 7
    · subst x
      refine ⟨(mkSucc zeroTm, Term.var 7),
        by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2], Or.inr rfl⟩
    exact (hx (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddSigma2, h5, h7])).elim
  · intro sigmaOther hOther
    refine ⟨sigmaOther, ?_⟩
    intro x
    have h1 := hOther (mkSucc zeroTm, Term.var 7)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2])
    have h2 := hOther (Term.var 5, zeroTm)
      (by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddPairs2])
    by_cases hx5 : x = 5
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm] at h2
      simpa [SubstitutionCore.substCompose, exAddSigma2, termSubstAll,
        termSubstAll_zeroTm] using h2
    by_cases hx7 : x = 7
    · subst x
      simp only [Prod.fst, Prod.snd, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] at h1
      simpa [SubstitutionCore.substCompose, exAddSigma2, termSubstAll,
        termSubstAll_zeroTm, termSubstAll_mkSucc] using h1.symm
    simp [SubstitutionCore.substCompose, exAddSigma2, termSubstAll, hx5, hx7]

@[blueprint "chap9__example_9_4_1"]
theorem exAddSigma2_isAtomMGU :
    (IsAtomMGU (hNoEq := by all_goals rfl))
      (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))
      ((mkAdd (Term.var 0) zeroTm (Term.var 0)).subst (hNoEq := by all_goals rfl) exAddRho2)
      exAddSigma2


/-- Example 9.4.1 (companion): The full SLD-refutation for the goal
    :- add(succ(0), V, succ(succ(0))), completing via C_1 with
    MGU sigma_2 mapping X->succ(0), Y_2->0, yielding the empty clause.
    Built as `.step` onto `exAddSLDStep1` with the base clause C_1.
    `exAddClause_C1.bodyFOAtoms = []` and `exAddSLDStep1` has a
    singleton current goal, so the output index `(prev.take 0 ++ []
    ++ prev.drop 1).map σ = [].map σ = []` reduces definitionally.
    Per-field obligations (hMGU, hSep, hAk) are left as
    `sorry` — the whole derivation value is a real `.step` term,
    not an axiom-equivalent sorry-def. -/
@[blueprint "chap9__example_9_4_1"]
noncomputable def exAddSLDStep2 : (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals ∅ := by
  -- The .step output index is
  --   ((step1.index.erase Ak).union (ofList (C_1.bodyFOAtoms.map rho_2))).image sigma_2
  -- which reduces to ∅ because step1.index = {atom_5}, erase atom_5 = ∅,
  -- C_1.bodyFOAtoms = [], and .image of ∅ = ∅.
  let step1Idx : LCS.Finset (FOAtom exAddLang rfl) :=
    (((LCS.Finset.ofList
        [mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm))]).erase
        (mkAdd (mkSucc zeroTm) (Term.var 3) (mkSucc (mkSucc zeroTm)))).union
      (LCS.Finset.ofList
        (exAddClause_C2.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho1)))
      ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma1)
  have step2raw :
      (FOSLDDerivation (hNoEq := by all_goals rfl)) (fun c => c ∈ exAdditionProgram) exAddGoals
        (((step1Idx.erase
            (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))).union
          (LCS.Finset.ofList
            (exAddClause_C1.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho2)))
          ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma2)) :=
    FOSLDDerivation.step
      (prev := exAddSLDStep1)
      (clause := exAddClause_C1)
      (hClause := by change exAddClause_C1 ∈ exAdditionProgram; simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAdditionProgram])
      (hDef := by simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.isDefinite, FOHornClauseCore.isDefinite, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton])
      (rho := exAddRho2)
      (sigma := exAddSigma2)
      (Ak := mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))
      (headA := mkAdd (Term.var 0) zeroTm (Term.var 0))
      (hAk := by
        rw [exAddStep1_currentGoal, LCS.Finset.mem_ofList]
        simp)
      (hHead := by rfl)
      (hMGU := exAddSigma2_isAtomMGU)
      (hSep := by
        -- prevGoal as Finset = {mkAdd (s 0) (var 5) (s 0)}; FV = {5}.
        -- FV(C_1) = {0}. rho = exAddRho2 renames 0 to 7.
        have hCongr : (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
            (step1Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := exAddLang) (hNoEq := by all_goals rfl))
            ([mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)].map
                FOLiteralCore.neg) := by
          apply (clauseFV_map_neg_mem_congr (hNoEq := by all_goals rfl))
          intro a
          rw [LCS.Finset.mem_toList]
          show a ∈ step1Idx ↔ _
          rw [show step1Idx = LCS.Finset.ofList
              [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] from
              exAddStep1_currentGoal, LCS.Finset.mem_ofList]
        change IsSeparatingPair (L := exAddLang) (hNoEq := rfl) Term.var exAddRho2 _ _
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | n
          · exact ⟨7, rfl⟩
          · exact ⟨n + 1, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy h
          have hxmem := exAddClause_C1_FV_subset x hx
          have hymem := exAddClause_C1_FV_subset y hy
          subst hxmem; subst hymem; rfl
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            rw [exAddStep1_goal_FV_eq_5] at hPrev
            subst hPrev
            have hn5 : n = 5 :=
              (Term.var.injEq (L := exAddLang) _ _).mp hEq₁ |>.symm
            subst hn5
            have hx₂0 := exAddClause_C1_FV_subset x₂ hClause
            subst hx₂0
            simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddRho2] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | n
          · exfalso; exact hx exAddClause_C1_FV_0
          · rfl)

  -- Cast step2raw's Finset index to ∅ via extensionality.
  have hIdx :
      (((step1Idx.erase
          (mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm))).union
        (LCS.Finset.ofList
          (exAddClause_C1.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddRho2)))
        ).image ((FOAtomCore.subst (hNoEq := by all_goals rfl)) exAddSigma2)) =
      (∅ : LCS.Finset (FOAtom exAddLang rfl)) := by
    apply LCS.Finset.ext
    intro a
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨b, hb, _⟩
      rw [LCS.Finset.mem_union] at hb
      rcases hb with herase | himg
      · rw [LCS.Finset.mem_erase,
            show step1Idx = LCS.Finset.ofList
                [mkAdd (mkSucc zeroTm) (Term.var 5) (mkSucc zeroTm)] from
                exAddStep1_currentGoal,
            LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [FOHornClause.rule, FOHornClause.fact, FOHornClause.goal, exAddClause_C1, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty, finset_toList_singleton] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  rw [hIdx] at step2raw
  exact step2raw

/-- Example 9.4.1 (companion): Proof that the two-step derivation
    terminates with the empty clause (is a refutation). Since
    `FOSLDDerivation.isRefutation d` reduces to `currentGoal = ∅`
    and exAddSLDStep2 has type `FOSLDDerivation D goals ∅`, this
    follows by `rfl`. -/
@[blueprint "chap9__example_9_4_1"]
theorem exAddRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := by all_goals rfl)) exAddSLDStep2 

/-- Example 9.4.1: The answer component: the value of V = succ(zero), meaning
    succ(0) + succ(0) = succ(succ(0)). -/
@[blueprint "chap9__example_9_4_1" (main := true)]
def exAddAnswerBinding : Term exAddLang :=
  mkSucc zeroTm

end LCS.SLD.FirstOrder
end

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
end LCS.SLD.FirstOrder
end

