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
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.Soundness
import LCS.SLD.FirstOrder.GroundLifting
import LCS.SLD.FirstOrder.GroundInstances
import LCS.SLD.FirstOrder.GroundSemantics
import Attach
import LCS.SLD.FirstOrder.PropositionalEncoding.ProofsStamp

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

/-- Theorem 9.4.1 (required helper): Transfer unsatisfiability from the
    SHG compound-instance witness to SOME ground Horn-clause set
    `D_g ++ goals`, where `D_g` is produced INSIDE the body.

    TEXTBOOK-FAITHFUL FRAMING. Gallier §9.4.1's proof sketch is: "by
    SHG there is a set S_g of ground instances of clauses in S which is
    unsatisfiable". The existence of `D_g` is ABSTRACT — the caller is
    given an existential, not a specific equation pinning `D_g` to any
    particular construction. This matches the textbook: `D_g` is the
    "some set of ground instances" witnessed by the SHG theorem applied
    to `ci.toFormula`.

    CONTENT. Given:
    - `hAllNe` — `D ++ goals ≠ []`;
    - a `SkolemSpec spec` with `spec.source = hornClauses_to_formulaN Afalsum (D ++ goals)`;
    - a WellFormed `CInstance` tree `ci` for `SK spec` whose extracted
      quantifier-free formula `C = ci.toFormula` is unsatisfiable (the
      SHG-half output, Theorem 7.6.1(a));
    - `hUnsat` — the original Horn clause set `D ++ goals` is unsatisfiable;
    THERE EXISTS a ground Horn clause list `D_g` such that:
    - `D_g ++ goals ≠ []`,
    - every `c_g ∈ D_g` is a ground substitution instance of some
      `c ∈ D` (with closed-form σ and groundness witness), and
    - `D_g ++ goals` is unsatisfiable.

    JUSTIFICATION. By Def 7.6.3 + Cor 7.6.1, `C = ci.toFormula` is the
    finite ground conjunction obtained by instantiating the universal
    quantifiers of each conjunct in `spec.source` (i.e., of each
    per-clause universal closure in `hornClauses_to_formulaN`) with the
    closed terms carried at the `forallInst` nodes of `ci`. The
    extraction routine `extractGroundClauses_from_cinstance` projects
    exactly those ground instances that arose from clauses in `D`,
    leaving the goal clauses unchanged since `goals ⊆ D ++ goals` already
    appear as top-level conjuncts of `C`. Consequently any model `M`
    of `D_g ++ goals` is a model of `C`; since `¬ satisfiableN C`, no
    such `M` can exist, i.e., `D_g ++ goals` is unsatisfiable.

    NOTE ON LANGUAGE. Horn clauses have no existential quantifiers, so
    `spec.n = 0` and `SkolemSpec.language` extends `L` only by the empty
    set of Skolem functions; `C` therefore lives in `spec.language` which
    is isomorphic to `L` as a language structure (by `Fin.elim0`). This
    trivial language-lift is absorbed into the semantic transfer below
    via `spec_trivial_expansion`.

    PROOF STATUS. Faithfully stated; body internally constructs `D_g`
    via `extractGroundClauses_from_cinstance`, then uses the SHG-half
    output `hCUnsat` together with the trivial expansion to derive
    unsatisfiability. A single narrow sub-sorry remains for the
    semantic-transfer step `∀ M ⊨ D_g ++ goals, (M ↑ spec.language) ⊨
    ci.toFormula`; closure requires the multi-path structural-induction
    infrastructure over `ci` (see the sorry's documentation below). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem unsat_transfer_dg_goals_via_cinstance {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (hGoalsNe : goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (hCUnsat : ¬ satisfiableN ci.toFormula)
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) :
    ∃ (D_g goals_g : List (FOHornClause L hNoEq)),
      (D_g ++ goals_g ≠ []) ∧
      (∀ c_g ∈ D_g, ∃ (c : FOHornClause L hNoEq) (_hMem : c ∈ D) (σ : Nat → Term L),
         c_g = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ ∧ (∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c_g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)) ∧
      (∀ g_g ∈ goals_g, ∃ (g : FOHornClause L hNoEq) (_hMem : g ∈ goals) (τ : Nat → Term L),
         g_g = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g τ ∧ (∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (g_g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)) ∧
      (goals_g ≠ []) ∧
      (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D_g ++ goals_g) 

-- ===================================================================
-- Atom-to-Nat reification infrastructure for Theorem 9.4.1
-- (ground Horn-clause set -> propositional SLD via countable atoms)
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Extract the structural atom carried by a first-order literal. -/
@[blueprint "chap9__theorem_9_4_1"]
def FOLiteral.foAtom {L : Language} (hNoEq : L.withoutEquality) : FOLiteral L hNoEq → FOAtom L hNoEq
  | .pos atom | .neg atom => atom

/-- Theorem 9.4.1 (required helper): Predicate asserting that a structural
    atom is a ground predicate application — `predN P args` with every `args i` having no
    free variables. -/
@[blueprint "chap9__theorem_9_4_1"]
def IsGroundAtom {L : Language} (hNoEq : L.withoutEquality)  (A : FOAtom L hNoEq) : Prop :=
  ∃ (P : L.predSymbols) (args : Fin (L.predArity P) → Term L),
    A = FOAtomCore.predN P args ∧ (∀ i x, ¬ termVars (args i) x)

/-- Theorem 9.4.1 (required helper): Collect the underlying atoms of every
    literal in every `c.toFOClause` for `c ∈ S`, deduplicated. Each
    literal's structural atom is extracted via `FOLiteral.foAtom`. The
    `eraseDups` ensures no duplicate atoms in the resulting list. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def groundAtomsOf {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOHornClause L hNoEq)) : List (FOAtom L hNoEq) :=
  (S.flatMap (fun c => c.toFOClause.map (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)))).eraseDups

/-- Theorem 9.4.1 (required helper): Encode a ground atom as a natural
    number by its position in a fixed list of atoms. When the atom is
    not in the list, returns `atoms.length` (a value outside the
    codomain); the `groundAtomEncode_injective` lemma only asserts
    injectivity on atoms actually in the list. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def groundAtomEncode {L : Language} (hNoEq : L.withoutEquality)
    (a : FOAtom L hNoEq) (atoms : List (FOAtom L hNoEq)) : Nat :=
  atoms.idxOf a

/-- Theorem 9.4.1 (required helper): `groundAtomEncode` is injective on
    atoms present in the list, provided the list has no duplicates. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem groundAtomEncode_injective {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (a b : FOAtom L hNoEq) (ha : a ∈ atoms) (hb : b ∈ atoms)
    (hEq : (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms) :
    a = b 

/-- Theorem 9.4.1 (required helper): Every literal atom of a clause
    `c ∈ S` appears in `groundAtomsOf S`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem groundAtomsOf_mem {L : Language} (hNoEq : L.withoutEquality)  (S : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ S)
    (lit : FOLiteral L hNoEq) (hlit : lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq))) :
    (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ (groundAtomsOf (hNoEq := by all_goals exact hNoEq)) S 

/-- Theorem 9.4.1 (required helper): `groundAtomsOf` produces a duplicate-
    free list, as `eraseDups` is applied at the outer level. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem groundAtomsOf_nodup {L : Language} (hNoEq : L.withoutEquality)  (S : List (FOHornClause L hNoEq)) :
    ((groundAtomsOf (hNoEq := by all_goals exact hNoEq)) S).Nodup 

/-- Theorem 9.4.1 (required helper): Translate a ground `FOLiteral L` to a
    propositional `LCS.Resolution.GCNF.Literal` via `groundAtomEncode`.
    `FOLiteral.pos a → Literal.pos (encode a)`, `FOLiteral.neg a →
    Literal.neg (encode a)`. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def foLiteralToPropLiteral {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) : FOLiteral L hNoEq → LCS.Resolution.GCNF.Literal
  | .pos a => LCS.Resolution.GCNF.Literal.pos ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms)
  | .neg a => LCS.Resolution.GCNF.Literal.neg ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms)

/-- Theorem 9.4.1 (required helper): Translate a `FOHornClause L` to a
    propositional `LCS.Resolution.GCNF.Clause` by translating each
    literal in `c.toFOClause` via `foLiteralToPropLiteral` and building
    the resulting `Clause.ofList`. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def foHornClauseToPropClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (atoms : List (FOAtom L hNoEq)) :
    LCS.Resolution.GCNF.Clause :=
  LCS.Resolution.GCNF.Clause.ofList
    (c.toFOClause.map ((foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms))

/-- Theorem 9.4.1 (required helper): Translate a list of FO Horn clauses
    to a `LCS.Resolution.GCNF.ClauseSequent` by translating each clause
    and collecting the results into a finset. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def foHornClausesToPropSequent {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOHornClause L hNoEq)) (atoms : List (FOAtom L hNoEq)) :
    LCS.Resolution.GCNF.ClauseSequent :=
  LCS.Finset.ofList (S.map (fun c => (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms))

/-- Theorem 9.4.1 (required helper): The propositional translation of any
    FO Horn clause `c` satisfies `isHornClause` (at most one positive
    literal): a rule has exactly one `pos head`, a fact has exactly one
    `pos head`, a goal has none. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem foHornClauseToPropClause_isHornClause {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (c : FOHornClause L hNoEq)
    (hMembers : ∀ lit ∈ c.toFOClause hNoEq, FOLiteral.foAtom hNoEq lit ∈ atoms) :
    LCS.SLD.SLDForm.isHornClause (foHornClauseToPropClause hNoEq c atoms)

/-- Theorem 9.4.1 (required helper): The propositional translation
    preserves `isDefinite`: a definite FO Horn clause maps to a
    definite propositional clause. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foHornClauseToPropClause_isDefinite {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (c : FOHornClause L hNoEq) (hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hMembers : ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)), (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms) :
    LCS.SLD.SLDForm.isDefiniteClause ((foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms) 

/-- Theorem 9.4.1 (required helper): The propositional translation
    preserves goal-clause shape: a non-definite FO Horn clause maps
    to a propositional goal clause. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foHornClauseToPropClause_isGoal {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (c : FOHornClause L hNoEq) (hGoal : ¬ (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hMembers : ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)), (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms) :
    LCS.SLD.SLDForm.isGoalClause ((foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms) 

/-- Theorem 9.4.1 (required helper): Every clause in the propositional
    sequent translation is a Horn clause. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foHornClausesToPropSequent_isHorn {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (S : List (FOHornClause L hNoEq))
    (hMembers : ∀ c ∈ S, ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)),
      (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms) :
    ∀ C ∈ (foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) S atoms,
      LCS.SLD.SLDForm.isHornClause C 

-- ===================================================================
-- Theorem 9.4.1 (required helper): FO-unsat → propositional GCNFProvable
-- Term-model structure construction + clause-by-clause semantic bridge.
-- ===================================================================

/-- Theorem 9.4.1 (required helper): The term-model FO structure induced by a
    propositional valuation `v` and a list of ground atoms. Carrier is
    `Term L`; function symbols and constants are interpreted as their own
    syntactic terms (Herbrand identity); a predicate `P` applied to term
    arguments `args` is interpreted as `v` evaluated at the atom-to-Nat
    encoding of the formula `predN P args` in the `atoms` list. For atoms
    not in `atoms` the encoding yields `atoms.length` (see
    `groundAtomEncode`), and `v` at that index is an arbitrary Bool — but
    the Thm 9.4.1 bridge only evaluates formulas whose atoms lie in
    `atoms`, so the out-of-list behaviour is immaterial to the proof. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def propValToFOStructure {L : Language} (hNoEq : L.withoutEquality)
    (v : Nat → Bool) (atoms : List (FOAtom L hNoEq)) : Structure L where
  carrier := Term L
  carrierNonempty := ⟨Term.var 0⟩
  interpFunc f args := Term.func f args
  interpConst c := Term.const c
  interpPred P args := v ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) (FOAtomCore.predN P args) atoms) = true

/-- Theorem 9.4.1 (required helper): In the term-model structure, evaluating
    a ground term yields the term itself. This Herbrand-identity property
    is the semantic counterpart to the reification: ground syntax IS the
    semantic value. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem termEval_propValToFOStructure_ground_id {L : Language} (hNoEq : L.withoutEquality)
    (v : Nat → Bool) (atoms : List (FOAtom L hNoEq))
    (s : Assignment ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms))
    (t : Term L) (hGround : ∀ x, ¬ termVars t x) :
    termEval ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms) s t = t 

/-- Theorem 9.4.1 (required helper): Semantic bridge at the atom level:
    evaluating a ground atom `predN P args` in the term-model structure
    equals the Boolean value of `v` at the atom's encoded index. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaEvalN_propValToFOStructure_groundAtom_iff {L : Language} (hNoEq : L.withoutEquality)
    (v : Nat → Bool) (atoms : List (FOAtom L hNoEq))
    (s : Assignment ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms))
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L)
    (hGround : ∀ i x, ¬ termVars (args i) x) :
    formulaEvalN ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms) (FormulaN.predN P args) s ↔
    v ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) (FOAtomCore.predN P args) atoms) = true 

/-- Theorem 9.4.1 (required helper): Term-level free-variable coincidence:
    `termFV t x ↔ termVars t x` for every term `t`. The two
    definitions agree pointwise, since terms have no quantifiers. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem termFV_iff_termVars {L : Language} (t : Term L) (x : Nat) :
    termFV t x ↔ termVars t x 

open LCS.FirstOrder.SyntaxN.Variables in
/-- Theorem 9.4.1 (required helper): For an atomic formula, the free-variable
    set (`formulaFVN`, used by Ch5–Ch8 semantics) coincides with the
    no-quantifier variable set (`formulaVars`, used by §8.2 clause
    semantics). Used to bridge `hDGGround`/`hGoalsGround`
    (phrased in `formulaVars`) to `clauseFV`-style hypotheses
    (phrased in `formulaFVN`). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem formulaFVN_iff_formulaVars_of_atomic {L : Language} (A : FormulaN L)
    (hAtomic : FormulaN.isAtomic A = true) (x : Nat) :
    formulaFVN A x ↔ formulaVars A x 

/-- Theorem 9.4.1 (required helper): Under `hNoEq`, every structural atom
    appearing in a Horn clause embeds as `predN` (the equality
    constructor is forbidden by the language-level no-equality
    assumption). Supplies the `predN` witness that `IsGroundAtom`
    requires. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem isAtomic_noEq_predN {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (hAtomic : FormulaN.isAtomic A = true)  :
    ∃ (P : L.predSymbols) (args : Fin (L.predArity P) → Term L),
      A = FormulaN.predN P args 

/-- Theorem 9.4.1 (required helper): Given a structural atom in an
    equality-free language with no variables, it is a ground predicate
    atom (a `predN` with no free variables in
    any argument). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem isGroundAtom_of_atomic_noEq_noVars {L : Language} (hNoEq : L.withoutEquality)
    (A : FOAtom L hNoEq)
    (hNoVars : ∀ x, ¬ A.vars x) :
    (IsGroundAtom (hNoEq := by all_goals exact hNoEq)) A 

/-- Theorem 9.4.1 (required helper): `Clause.satisfiedBy` distributes over
    cons: `ofList (L :: rest)` is satisfied iff `L` is satisfied or
    `ofList rest` is satisfied. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem Clause_satisfiedBy_cons
    (L : LCS.Resolution.GCNF.Literal) (rest : List LCS.Resolution.GCNF.Literal)
    (v : Nat → Bool) :
    LCS.Resolution.GCNF.Clause.satisfiedBy
      (LCS.Resolution.GCNF.Clause.ofList (L :: rest)) v ↔
    LCS.Resolution.GCNF.Literal.satisfiedBy L v ∨
    LCS.Resolution.GCNF.Clause.satisfiedBy
      (LCS.Resolution.GCNF.Clause.ofList rest) v 

/-- Theorem 9.4.1 (required helper): Semantic bridge at the literal level:
    evaluating `(clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit` in the term-model
    structure corresponds to the satisfaction of the propositional
    literal `foLiteralToPropLiteral atoms lit` under `v`, provided the
    literal's underlying formula is a ground atom. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem litToFormulaEvalN_propValToFOStructure_iff {L : Language} (hNoEq : L.withoutEquality)
    (v : Nat → Bool) (atoms : List (FOAtom L hNoEq))
    (s : Assignment ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms))
    (lit : FOLiteral L hNoEq)
    (hGround : (IsGroundAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit)) :
    formulaEvalN ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms) ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit) s ↔
    LCS.Resolution.GCNF.Literal.satisfiedBy ((foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms lit) v 

/-- Theorem 9.4.1 (required helper): Semantic bridge at the clause level:
    evaluating `clauseToFormula Afalsum C` in the term-model structure
    corresponds to the satisfaction of the propositional clause
    `foClauseToPropClause C atoms` under `v`, provided every literal in
    `C` has a ground atom as its underlying formula. Empty clause case:
    both sides are false (FO side is `FormulaN.falsum = A ∧ ¬A`, prop
    side is the empty clause, which has no satisfying literal). -/
@[blueprint "chap9__theorem_9_4_1"]
theorem clauseToFormulaEvalN_propValToFOStructure_iff {L : Language} (hNoEq : L.withoutEquality)
    (v : Nat → Bool) (atoms : List (FOAtom L hNoEq))
    (s : Assignment ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms))
    (Afalsum : FormulaN L)
    (C : FOClause L hNoEq)
    (hGround : ∀ lit ∈ C, (IsGroundAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit)) :
    formulaEvalN ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms) ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum C) s ↔
    LCS.Resolution.GCNF.Clause.satisfiedBy
      (LCS.Resolution.GCNF.Clause.ofList (C.map ((foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms))) v 

/-- Theorem 9.4.1 (required helper): Transfer first-order unsatisfiability of a ground Horn
    clause set `D_g ++ goals` to propositional GCNFProvable on the
    atom-reified translation. Used by the Thm 9.4.1 completeness chain
    to invoke `gcnf_completeness` on the propositional level, obtaining
    a propositional proof tree that is reflected back to first-order SLD
    via the lifting step.

    PROOF IDEA. Suffices to show the propositional sequent is valid
    (`ClauseSequent.isValid`). By contradiction, assume some
    `v : Nat → Bool` satisfies the sequent. Construct the term-model
    `Structure L` (`propValToFOStructure v atoms`) whose carrier is
    `Term L` and whose predicate interpretation reifies the valuation.
    Each clause `c ∈ D_g ++ goals` is ground and atomic, so every
    literal's underlying formula is a ground `predN` atom in
    `groundAtomsOf (D_g ++ goals)`. Apply the clause-level semantic
    bridge (`clauseToFormulaEvalN_propValToFOStructure_iff`) to reduce
    first-order evaluation to propositional satisfaction under `v`. Lift
    from `clauseToFormula` to `universalClosure` via
    `universalClosure_lift` (both sides are FV-independent by
    groundness). The resulting model satisfies all clauses'
    universal closures, contradicting `hDGUnsat`.

    The non-empty-body hypothesis `hBodiesNe` excludes `goal []` (empty
    body goals), which would translate to an empty propositional
    clause — `gcnf_completeness`'s required non-emptiness side condition
    then rules out that degenerate case. In the Thm 9.4.1 chain, empty
    initGoal bodies are handled separately by the caller
    (`foSLD_exists_refutation_from_unsat` takes the trivial empty-body
    path), so the non-degenerate branch into this helper always has
    non-empty goal bodies after the SHG cascade. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem groundUnsatToPropProvable {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D_g goals : List (FOHornClause L hNoEq))
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (hGoalsGround : ∀ c ∈ goals, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)

    (hBodiesNe : ∀ c ∈ D_g ++ goals, (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ≠ [])
    (hDGUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D_g ++ goals)) :
    LCS.Resolution.GCNF.GCNFProvable
      ((foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) (D_g ++ goals)
        ((groundAtomsOf (hNoEq := by all_goals exact hNoEq)) (D_g ++ goals))) 

-- ===================================================================
-- Theorem 9.4.1 (required helpers, sub-issue D):
-- Propositional SLD -> ground first-order SLD reflection infrastructure.
-- ===================================================================

/-- Theorem 9.4.1 (required helper): Decode a propositional atom index `n`
    back to the corresponding ground structural atom in `atoms`, as an
    `Option`. For `n < atoms.length`, returns `some atoms[n]`; otherwise
    `none`. The inverse of `groundAtomEncode` for atoms in the list. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def groundAtomDecode {L : Language} (hNoEq : L.withoutEquality)
    (n : Nat) (atoms : List (FOAtom L hNoEq)) : Option (FOAtom L hNoEq) :=
  atoms[n]?

/-- Theorem 9.4.1 (required helper): `groundAtomDecode` is a left inverse
    of `groundAtomEncode` on atoms present in the list. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem groundAtomDecode_encode {L : Language} (hNoEq : L.withoutEquality)  (a : FOAtom L hNoEq)
    (atoms : List (FOAtom L hNoEq)) (ha : a ∈ atoms) :
    (groundAtomDecode (hNoEq := by all_goals exact hNoEq)) ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms) atoms = some a 

/-- Theorem 9.4.1 (required helper): For any element `a` of `xs`,
    `xs[xs.idxOf a] = a`. A direct-access specialization of
    `List.getElem?_eq_some_iff`; used by `reflectOneStep` to discharge
    the `hAk : prevGoal[selectedIdx]? = some Ak` obligation when
    `selectedIdx = prevGoal.idxOf a` and `Ak = a ∈ prevGoal`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem List.getElem_idxOf_self {L : Language} (hNoEq : L.withoutEquality)  (a : FOAtom L hNoEq)
    (xs : List (FOAtom L hNoEq)) (ha : a ∈ xs) :
    xs[xs.idxOf a]'(List.idxOf_lt_length_iff.mpr ha) = a 

/-- Theorem 9.4.1 (required helper): Every propositional clause in the
    translation `foHornClausesToPropSequent S atoms` arises from some
    FO Horn clause `c ∈ S` via `foHornClauseToPropClause c atoms`. The
    inverse of the `flatMap`-based construction of
    `foHornClausesToPropSequent`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foHornClause_of_propClause_mem {L : Language} (hNoEq : L.withoutEquality)
    (S : List (FOHornClause L hNoEq)) (atoms : List (FOAtom L hNoEq))
    (C_prop : LCS.Resolution.GCNF.Clause)
    (hC_mem : C_prop ∈ (foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) S atoms) :
    ∃ c ∈ S, (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms = C_prop 

/-- Theorem 9.4.1 (required helper): A positive propositional literal
    `Literal.pos n` in the translation of an FO Horn clause `c` arises
    from some FO literal `FOLiteral.pos a` in `c.toFOClause` with
    `n = groundAtomEncode a atoms`. Inverse at the literal level. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foLiteralPos_reflect {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (atoms : List (FOAtom L hNoEq)) (n : Nat)
    (hMem : LCS.Resolution.GCNF.Literal.pos n ∈
      (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms) :
    ∃ a : FOAtom L hNoEq, FOLiteralCore.pos a ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ∧
      n = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms 

/-- Theorem 9.4.1 (required helper): A negative propositional literal
    `Literal.neg n` in the translation of an FO Horn clause `c` arises
    from some FO literal `FOLiteral.neg a` in `c.toFOClause` with
    `n = groundAtomEncode a atoms`. Inverse at the literal level. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem foLiteralNeg_reflect {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (atoms : List (FOAtom L hNoEq)) (n : Nat)
    (hMem : LCS.Resolution.GCNF.Literal.neg n ∈
      (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms) :
    ∃ a : FOAtom L hNoEq, FOLiteralCore.neg a ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ∧
      n = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms 

/-- Theorem 9.4.1 (required helper): A negative literal `Literal.neg n`
    in the propositional encoding of a ground `prevGoal` (mapped via
    `Literal.neg ∘ groundAtomEncode · atoms`) arises from some ground
    atom `a ∈ prevGoal` with `n = groundAtomEncode a atoms`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem prevProp_neg_reflect {L : Language} (hNoEq : L.withoutEquality)
    (prevGoal : List (FOAtom L hNoEq)) (atoms : List (FOAtom L hNoEq)) (n : Nat)
    (hMem : LCS.Resolution.GCNF.Literal.neg n ∈
      LCS.Resolution.GCNF.Clause.ofList (prevGoal.map
        (fun a => LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms)))) :
    ∃ a ∈ prevGoal, n = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms 

/-- Theorem 9.4.1 (required helper): For a definite Horn clause `c`, the
    only positive literal in `c.toFOClause` is the clause's head. Used
    by `reflectOneStep` to force the recovered FO atom (from the
    positive prop literal) to equal the clause's head. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem definite_pos_is_head {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq)
    (hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (a headA : FOAtom L hNoEq) (hHead : (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA)
    (haPos : FOLiteralCore.pos a ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq))) :
    a = headA 

/-- Theorem 9.4.1 (required helper): The core per-step reflector. Given a
    propositional `selectedAtomMatches` witness for a ground prev-goal's
    encoding (via `Literal.neg ∘ groundAtomEncode · atoms`) and a source
    prop clause that arises from some FO Horn clause `c ∈ D_g`, produce
    a `GroundSLDStep D_g prevGoal`.

    Strategy: use `foHornClause_of_propClause_mem` to extract the source
    FO clause `c`; use `prevProp_neg_reflect` to extract the ground atom
    `a ∈ prevGoal` decoding the selected prop atom `A_prop`; use
    `foLiteralPos_reflect` to recover the FO literal in `c.toFOClause`
    realizing `Literal.pos A_prop`; use `definite_pos_is_head` to force
    the recovered FO atom to be `c`'s head; and use
    `groundAtomEncode_injective` on the shared encoding `A_prop` and the
    `Nodup` of `atoms` to conclude the selected atom from `prevGoal`
    equals `c`'s head. The `selectedIdx` is `prevGoal.idxOf a`;
    `hAk` is discharged via `List.getElem_idxOf_self`; `hUnifGround`
    follows. `hGroundPrev`/`hGroundClause` transport the
    ground hypotheses. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def reflectOneStep {L : Language} (hNoEq : L.withoutEquality)
    (D_g : List (FOHornClause L hNoEq))
    (hDGDef : ∀ c ∈ D_g, (c.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (hDGGround : ∀ c ∈ D_g, ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x)
    (atoms : List (FOAtom L hNoEq))
    (hNodup : atoms.Nodup)
    (hAtomsCoverD : ∀ c ∈ D_g, ∀ lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)),
      (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit ∈ atoms)
    (prevGoal : LCS.Finset (FOAtom L hNoEq))
    (hPrevGround : ∀ a ∈ prevGoal, ∀ x, ¬ a.vars x)
    (hPrevInAtoms : ∀ a ∈ prevGoal, a ∈ atoms)
    (A_prop : Nat) (C_prop : LCS.Resolution.GCNF.Clause)
    (hCmem : C_prop ∈ (foHornClausesToPropSequent (hNoEq := by all_goals exact hNoEq)) D_g atoms)
    (hSAM : LCS.SLD.Propositional.selectedAtomMatches
      (LCS.Resolution.GCNF.Clause.ofList (prevGoal.toList.map
        (fun a => LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
      A_prop C_prop) :
    (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g prevGoal :=
-- BEGIN PROOF
  let cHyp : ∃ c ∈ D_g, (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms = C_prop :=
    (foHornClause_of_propClause_mem (hNoEq := by all_goals exact hNoEq)) D_g atoms C_prop hCmem
  let c : FOHornClause L hNoEq := cHyp.choose
  let hcMem : c ∈ D_g := cHyp.choose_spec.1
  let hCEq : (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms = C_prop := cHyp.choose_spec.2
  let hNegInPrev : LCS.Resolution.GCNF.Literal.neg A_prop ∈
      LCS.Resolution.GCNF.Clause.ofList (prevGoal.toList.map
        (fun a => LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) :=
    hSAM.1
  let aHyp : ∃ a ∈ prevGoal.toList,
      A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms :=
    (prevProp_neg_reflect (hNoEq := by all_goals exact hNoEq)) prevGoal.toList atoms A_prop hNegInPrev
  let a : FOAtom L hNoEq := aHyp.choose
  let haMemList : a ∈ prevGoal.toList := aHyp.choose_spec.1
  let haMem : a ∈ prevGoal := (LCS.Finset.mem_toList _ _).mp haMemList
  let hAEnc : A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms :=
    aHyp.choose_spec.2
  let hPosInC_prop : LCS.Resolution.GCNF.Literal.pos A_prop ∈ C_prop := hSAM.2
  let hPosInC : LCS.Resolution.GCNF.Literal.pos A_prop ∈
      (foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms :=
    hCEq ▸ hPosInC_prop
  let bHyp : ∃ b : FOAtom L hNoEq, FOLiteralCore.pos b ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ∧
      A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms :=
    (foLiteralPos_reflect (hNoEq := by all_goals exact hNoEq)) c atoms A_prop hPosInC
  let b : FOAtom L hNoEq := bHyp.choose
  let hbPos : FOLiteralCore.pos b ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) := bHyp.choose_spec.1
  let hBEnc : A_prop = (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms :=
    bHyp.choose_spec.2
  let hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq)) := hDGDef c hcMem
  let hHeadEx : ∃ headA : FOAtom L hNoEq, (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA := by
    match hC : c, hDef with
    | FOHornClauseCore.rule h _, _ => exact ⟨h, rfl⟩
    | FOHornClauseCore.fact h, _ => exact ⟨h, rfl⟩
    | FOHornClauseCore.goal _, hD => exact absurd hD (by simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
  let headA : FOAtom L hNoEq := hHeadEx.choose
  let hHead : (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA := hHeadEx.choose_spec
  let hBH : b = headA := (definite_pos_is_head (hNoEq := by all_goals exact hNoEq)) c hDef b headA hHead hbPos
  let haInAtoms : a ∈ atoms := hPrevInAtoms a haMem
  let hbInAtoms : b ∈ atoms := by
    have := hAtomsCoverD c hcMem (FOLiteralCore.pos b) hbPos
    simpa [FOLiteral.foAtom] using this
  let hAB : a = b :=
    (groundAtomEncode_injective (hNoEq := by all_goals exact hNoEq)) atoms hNodup
      a b haInAtoms hbInAtoms
        (by rw [← hAEnc, ← hBEnc])
  let hAeqH : a = headA := hAB.trans hBH
  let hGroundClause : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := hDGGround c hcMem
  { clause := c
    hClause := hcMem
    hDef := hDef
    Ak := a
    headA := headA
    hAk := haMem
    hHead := hHead
    hUnifGround := hAeqH
    hGroundPrev := hPrevGround
    hGroundClause := hGroundClause }

-- ===================================================================
-- Theorem 9.4.1 (required helpers, sub-issue D part 2):
-- Full recursive prop-SLD sequence -> ground first-order transcript reflector.
-- ===================================================================

/-- Theorem 9.4.1 (required helper): Filtering a propositional Horn-clause
    translation by the `isNeg` predicate yields precisely the propositional
    encoding of the source clause's body atoms as negative literals. The
    positive-head literal (for `rule`/`fact` constructors) is filtered out;
    for `goal` constructors every literal is negative. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem negFilter_foHornClauseToPropClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (atoms : List (FOAtom L hNoEq)) :
    LCS.Finset.filter
        (fun l => match l with
          | LCS.Resolution.GCNF.Literal.neg a => true
          | LCS.Resolution.GCNF.Literal.pos a => false)
        ((foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) c atoms) =
      LCS.Resolution.GCNF.Clause.ofList
        (c.bodyFOAtoms.map
          (fun a => LCS.Resolution.GCNF.Literal.neg
            ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) 

/-- Theorem 9.4.1 (required helper): The core alignment lemma for the
    prop→ground reflector. Given a ground previous-goal `prevGoal`
    (all atoms appear in `atoms`, `prevGoal.Nodup`), a Horn clause selected
    at position `idx`, show that the propositional `resolveStep` applied to
    the prev-goal's encoding yields precisely the encoding of the FO
    post-step prev-goal
    (`prevGoal.take idx ++ clause.bodyFOAtoms ++ prevGoal.drop (idx+1)`).

    Under `prevGoal.Nodup`, `selectedAtom` appears exactly once in `prevGoal`
    (at position `idx`), so the propositional `remove` at the Finset level
    precisely matches `take idx ++ drop (idx+1)` at the list level. The
    encoding is injective on `atoms` (by `groundAtomEncode_injective`), so
    every atom's `neg(encode a)` literal appears or doesn't appear in
    lockstep on both sides. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem resolveStep_alignment {L : Language} (hNoEq : L.withoutEquality)
    (atoms : List (FOAtom L hNoEq)) (hNodup : atoms.Nodup)
    (prevGoal : List (FOAtom L hNoEq))
    (hPrevInAtoms : ∀ a ∈ prevGoal, a ∈ atoms)
    (hPrevNodup : prevGoal.Nodup)
    (idx : Nat) (selectedAtom : FOAtom L hNoEq)
    (hSelIdx : prevGoal[idx]? = some selectedAtom)
    (clause : FOHornClause L hNoEq)
    (_hClauseBodyInAtoms :
      ∀ a ∈ (clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)), a ∈ atoms) :
    LCS.SLD.Propositional.resolveStep
        (LCS.Resolution.GCNF.Clause.ofList
          (prevGoal.map (fun a =>
            LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
        ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) selectedAtom atoms)
        ((foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) clause atoms) =
      LCS.Resolution.GCNF.Clause.ofList
        ((prevGoal.take idx ++ (clause.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)) ++
          prevGoal.drop (idx + 1)).map
          (fun a =>
            LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) 

/-- Theorem 9.4.1 (required helper): Per-step post-step prev-goal equality.
    The `.cons` constructor of `GroundSLDTranscript` indexes the post-step
    prev-goal at `(prev.take idx ++ body ++ prev.drop (idx+1)).map (fSA · Term.var)`.
    Under groundness of `prev` and `clause.bodyFOAtoms`, the outer `map` is
    the identity and the post-step prev-goal collapses to
    `prev.take idx ++ body ++ prev.drop (idx+1)`. This helper packages that
    observation and is used by the reflector to thread invariants through
    the recursion without repeatedly unfolding `formulaSubstAll_var_ground`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem postStepPrev_ground_eq {L : Language} (hNoEq : L.withoutEquality)
    (prevGoal : List (FOAtom L hNoEq)) (body : List (FOAtom L hNoEq)) (idx : Nat)
    (_hPrevGround : ∀ a ∈ prevGoal, ∀ x, ¬ a.vars x)
    (_hBodyGround : ∀ a ∈ body, ∀ x, ¬ a.vars x) :
    ((prevGoal.take idx ++
      body.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)) ++
      prevGoal.drop (idx + 1)).map
      ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))) =
    prevGoal.take idx ++ body ++ prevGoal.drop (idx + 1) 

end LCS.SLD.FirstOrder
end

