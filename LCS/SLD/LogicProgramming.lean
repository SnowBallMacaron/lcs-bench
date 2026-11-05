import LCS.Item
import LCS.Util
import LCS.SLD.FirstOrder
import LCS.FirstOrder.SyntaxN.Variables
import Attach
import LCS.SLD.LogicProgramming.ProofsStamp

/-! # SLD.LogicProgramming (Section 9.5)
    Source: Logic for Computer Science, Gallier 2015

    Anti-Horn clauses, logic programs, free (Herbrand) structures,
    and model-theoretic semantics of logic programs.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace LCS.SLD.LogicProgramming

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.SLD.FirstOrder

-- ===================================================================
-- Definition 9.5.1: Anti-Horn clauses and logic programs
-- ===================================================================

/-- Literal data and existential names for an anti-Horn matrix. -/
structure AntiHornClauseCore (L : Language) : Type where
  posLiterals : List (FOAtomCore L)
  negLiteral : Option (FOAtomCore L)
  existVars : List Nat

/-- Variables of the conjunction matrix, before existential closure. -/
def AntiHornClauseCore.bodyVarSet {L : Language} (a : AntiHornClauseCore L) : Set Nat :=
  fun v =>
    (∃ atom ∈ a.posLiterals, formulaFVN atom.toFormula v) ∨
    (∃ atom, a.negLiteral = some atom ∧ formulaFVN atom.toFormula v)

/-- Positive literal count and exact existential coverage (SQ31–SQ32). -/
def AntiHornClauseCore.WellFormed {L : Language} (a : AntiHornClauseCore L) : Prop :=
  (a.posLiterals ≠ [] ∨ a.negLiteral.isSome = true) ∧
  ∀ v, v ∈ a.existVars ↔ a.bodyVarSet v

/-- Definition 9.5.1: An equality-free, nonempty conjunction of literals
    with at most one negative literal, existentially closed over exactly
    its matrix variables (SQ31–SQ32, OD-9-1). -/
@[blueprint "chap9__definition_9_5_1" (main := true)]
def AntiHornClause (L : Language) (_hNoEq : L.withoutEquality) : Type :=
  { a : AntiHornClauseCore L // a.WellFormed }

namespace AntiHornClause

def toAntiHornClauseCore {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : AntiHornClauseCore L := a.val

theorem wellFormed {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : a.toAntiHornClauseCore.WellFormed := a.property

@[blueprint "chap9__definition_9_5_1"]
def posLiterals {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : List (FOAtom L hNoEq) := a.val.posLiterals

@[blueprint "chap9__definition_9_5_1"]
def negLiteral {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : Option (FOAtom L hNoEq) := a.val.negLiteral

@[blueprint "chap9__definition_9_5_1"]
def existVars {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : List Nat := a.val.existVars

end AntiHornClause

/-- Program matrices and a finite family of closed query components. -/
structure LogicProgramCore (L : Language) (hNoEq : L.withoutEquality) where
  prog : Set (FOHornClause L hNoEq)
  qry : List (AntiHornClause L hNoEq)

/-- Nonempty query and disjoint matrix variables (SQ30–SQ32). -/
def LogicProgramCore.WellFormed {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgramCore L hNoEq) : Prop :=
  lp.qry ≠ [] ∧ lp.qry.Pairwise (fun a b =>
    ∀ v, ¬ (a.toAntiHornClauseCore.bodyVarSet v ∧ b.toAntiHornClauseCore.bodyVarSet v))

/-- Definition 9.5.1: An arbitrary set of universally closed Horn clauses
    and a nonempty finite query with disjoint component matrix variables
    (SQ25, SQ30–SQ32). -/
@[blueprint "chap9__definition_9_5_1" (main := true)]
def LogicProgram (L : Language) (hNoEq : L.withoutEquality) : Type :=
  { lp : LogicProgramCore L hNoEq // lp.WellFormed }

namespace LogicProgram

def toLogicProgramCore {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : LogicProgramCore L hNoEq := lp.val

theorem wellFormed {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : lp.toLogicProgramCore.WellFormed := lp.property

@[blueprint "chap9__definition_9_5_1"]
def prog {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : Set (FOHornClause L hNoEq) := lp.val.prog

@[blueprint "chap9__definition_9_5_1"]
def qry {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : List (AntiHornClause L hNoEq) := lp.val.qry

end LogicProgram

-- ===================================================================
-- Definition 9.5.1 (companion): AntiHornClause helpers
-- ===================================================================

namespace AntiHornClause

/-- Definition 9.5.1 (companion): Collect all variable indices occurring in the
    formulae of the body (posLiterals and negLiteral). Returns the
    set of all variables appearing in the body B. -/
@[blueprint "chap9__definition_9_5_1"]
def bodyVarSet {L : Language} (hNoEq : L.withoutEquality) (a : AntiHornClause L hNoEq) : Set Nat :=
  a.toAntiHornClauseCore.bodyVarSet

/-- Definition 9.5.1 (companion): Free variables of an anti-Horn clause:
    variables in the body not bound by an existential quantifier. -/
@[blueprint "chap9__definition_9_5_1"]
def freeVars {L : Language} (hNoEq : L.withoutEquality) (a : AntiHornClause L hNoEq) : Set Nat :=
  fun v => (a.bodyVarSet (hNoEq := by all_goals exact hNoEq)) v ∧ v ∉ a.existVars

/-- The conjunction matrix, with the optional negative literal retaining its sign. -/
@[blueprint "chap9__definition_9_5_1"]
def matrix {L : Language} {hNoEq : L.withoutEquality} (a : AntiHornClause L hNoEq) : FormulaN L :=
  match hp : a.posLiterals, hn : a.negLiteral with
  | [], none => False.elim (by
      have h := a.wellFormed.1
      change a.posLiterals ≠ [] ∨ a.negLiteral.isSome = true at h
      simp [hp, hn] at h)
  | [], some n => .neg n.toFormula
  | p :: ps, n =>
      let positive := ps.foldl (fun f atom => .conj f atom.toFormula) p.toFormula
      match n with
      | none => positive
      | some atom => .conj positive (.neg atom.toFormula)

/-- Exact existential closure of the anti-Horn matrix (SQ31). -/
@[blueprint "chap9__definition_9_5_1"]
def toSentence {L : Language} {hNoEq : L.withoutEquality} (a : AntiHornClause L hNoEq) : FormulaN L :=
  a.existVars.foldr FormulaN.ex a.matrix

/-- Negate each matrix literal, obtaining its Horn clause. -/
@[blueprint "chap9__definition_9_5_1"]
def negatedClause {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : FOHornClause L hNoEq :=
  match a.negLiteral, a.posLiterals with
  | none, ps => FOHornClause.goal (hNoEq := hNoEq) (LCS.Finset.ofList ps)
  | some n, [] => FOHornClause.fact (hNoEq := hNoEq) n
  | some n, ps => FOHornClause.rule (hNoEq := hNoEq) n (LCS.Finset.ofList ps)

/-- The universal closure of the normalized Horn clause dual to the component. -/
@[blueprint "chap9__definition_9_5_1"]
def negationSentence {L : Language} {hNoEq : L.withoutEquality}
    (a : AntiHornClause L hNoEq) : FormulaN L :=
  a.existVars.foldr FormulaN.all
    (LCS.FOResolution.Method.Soundness.clauseToFormula hNoEq a.matrix (a.negatedClause.toFOClause hNoEq))

/-- Negating the existential conjunction gives its universal Horn clause
    (SQ31 and X-1 normalized-category reading). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem negationIsHorn {L : Language} (hNoEq : L.withoutEquality)
    (a : AntiHornClause L hNoEq) (M : Structure L) (s : Assignment M) :
    formulaEvalN M (.neg a.toSentence) s ↔ formulaEvalN M a.negationSentence s

end AntiHornClause

-- ===================================================================
-- Definition 9.5.1 (companion): LogicProgram helpers
-- ===================================================================

namespace LogicProgram

/-- Definition 9.5.1 (companion): Extracts the program P, the set of universal
    Horn clauses. -/
@[blueprint "chap9__definition_9_5_1"]
def program {L : Language} (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq) : Set (FOHornClause L hNoEq) :=
  lp.prog

/-- Definition 9.5.1 (companion): Extracts the query G, a disjunction of anti-Horn
    clauses G_1,...,G_n. -/
@[blueprint "chap9__definition_9_5_1"]
def query {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) : List (AntiHornClause L hNoEq) :=
  lp.qry

/-- Definition 9.5.1 (companion): The property that the query G = G_1 lor ... lor G_n
    is a nonempty disjunction of anti-Horn clauses. -/
@[blueprint "chap9__definition_9_5_1"]
def queryIsDisjunction {L : Language} (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq) : Prop :=
  lp.qry.length ≥ 1

/-- Definition 9.5.1 (companion): For all i != j, 1 <= i, j <= n, the sets of free
    variables FV(B_i) and FV(B_j) in the anti-Horn clause bodies are
    pairwise disjoint. -/
@[blueprint "chap9__definition_9_5_1"]
def variablesDisjoint {L : Language} (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq) : Prop :=
  ∀ (i j : Fin lp.qry.length),
    i ≠ j →
    ∀ v : Nat,
      ¬ ((AntiHornClause.bodyVarSet (hNoEq := by all_goals exact hNoEq)) (lp.qry.get i) v ∧
         (AntiHornClause.bodyVarSet (hNoEq := by all_goals exact hNoEq)) (lp.qry.get j) v)

/-- Definition 9.5.1 (companion): The union {z_1,...,z_q} of the sets of free
    variables from each B_i in the query G. -/
@[blueprint "chap9__definition_9_5_1"]
def outputVars {L : Language} (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq) : Set Nat :=
  fun v => ∃ (i : Fin lp.qry.length),
    (AntiHornClause.bodyVarSet (hNoEq := by all_goals exact hNoEq)) (lp.qry.get i) v

/-- The nonempty finite disjunction of the query's closed components. -/
@[blueprint "chap9__definition_9_5_1"]
def toSentence {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : FormulaN L :=
  lp.qry.tail.foldl (fun f a => .disj f a.toSentence)
    (lp.qry.head lp.wellFormed.1).toSentence

/-- The finite conjunction of the universal Horn clauses from this same query. -/
@[blueprint "chap9__definition_9_5_1"]
def negationSentence {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : FormulaN L :=
  lp.qry.tail.foldl (fun f a => .conj f a.negationSentence)
    (lp.qry.head lp.wellFormed.1).negationSentence

/-- Negating G gives the conjunction of the universal Horn duals of its
    own components (SQ31 and X-1). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem negQueryIsConjOfHorn {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (M : Structure L) (s : Assignment M) :
    formulaEvalN M (.neg lp.toSentence) s ↔ formulaEvalN M lp.negationSentence s

/-- Definition 9.5.1 (companion): A logic program satisfies the PROLOG restriction
    iff P consists only of definite clauses (each clause is a fact or rule,
    not a goal) and G is a single anti-Horn clause whose body is a
    conjunction of atomic formulae (no negative literal). -/
@[blueprint "chap9__definition_9_5_1"]
def isPROLOG {L : Language} (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq) : Prop :=
  (∀ c ∈ lp.prog, (FOHornClause.isDefinite (hNoEq := by all_goals exact hNoEq)) c) ∧
  lp.qry.length = 1 ∧
  (∀ a ∈ lp.qry, a.negLiteral = none)

/-- Definition 9.5.1: Enumerate the exact union of matrix variables without
    repetitions, using the component prefixes justified by exact coverage (SQ31). -/
@[blueprint "chap9__definition_9_5_1"]
def outputVarList {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) : List Nat :=
  (lp.qry.flatMap fun a => a.existVars).eraseDups

/-- The output enumeration contains no repeated coordinate names. -/
@[blueprint "chap9__definition_9_5_1"]
theorem outputVarList_nodup {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) : (lp.outputVarList hNoEq).Nodup

/-- The output list and matrix-variable union name exactly the same variables. -/
@[blueprint "chap9__definition_9_5_1"]
theorem mem_outputVarList {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (v : Nat) :
    v ∈ lp.outputVarList hNoEq ↔ lp.outputVars hNoEq v

/-- Definition 9.5.1 (companion): Given a substitution sigma returned by
    SLD-resolution, extracts the components sigma(z_1),...,sigma(z_q)
    corresponding to the output variables z_1,...,z_q. -/
@[blueprint "chap9__definition_9_5_1"]
def resultSubstitution {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (sigma : Nat → Term L) : List (Term L) :=
  lp.outputVarList.map sigma

end LogicProgram

-- ===================================================================
-- Definition 9.5.2: Free (Herbrand) structures
-- ===================================================================

/-- Definition 9.5.2 (companion): A closed L-term, i.e. a term with no free
    variables. Defined as a subtype of Term L satisfying isClosed. -/
@[blueprint "chap9__definition_9_5_2"]
def GroundTerm (L : Language) : Type :=
  { t : Term L // Term.isClosed t }

/-- Definition 9.5.2: The Herbrand universe H_L of L is the set of all closed (ground) L-terms. -/
@[blueprint "chap9__definition_9_5_2" (main := true)]
def HerbrandUniverse (L : Language) (_hNoEq : L.withoutEquality)
    (_hConst : Nonempty L.constSymbols) : Type :=
  GroundTerm L

/-- Constructor-domain predicate interpretations with a constant witness. -/
structure HerbrandStructureCore (L : Language) : Type where
  predInterp : L.predSymbols → List (GroundTerm L) → Prop
  hasConstant : Nonempty L.constSymbols

/-- Definition 9.5.2: A free structure of an equality-free, constant-completed
    language (SQ33). Its carrier consists of all ground terms of the ambient L. -/
@[blueprint "chap9__definition_9_5_2" (main := true)]
def HerbrandStructure (L : Language) (_hNoEq : L.withoutEquality) : Type :=
  HerbrandStructureCore L

namespace HerbrandStructure

@[blueprint "chap9__definition_9_5_2"]
def predInterp {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq) : L.predSymbols → List (GroundTerm L) → Prop :=
  HerbrandStructureCore.predInterp H

end HerbrandStructure

namespace HerbrandStructure

/-- Definition 9.5.2 (companion): Condition (i): for every function symbol f of
    rank n, f_H(t_1,...,t_n) = f(t_1,...,t_n). In the Herbrand
    structure, function symbols are interpreted as term constructors.
    Given ground terms t_1,...,t_n, the result Term.func f [t_1,...,t_n]
    is itself a ground term. -/
@[blueprint "chap9__definition_9_5_2"]
theorem funcInterp {L : Language} {hNoEq : L.withoutEquality}
    (_H : HerbrandStructure L hNoEq)
    (f : L.funSymbols)
    (ts : Fin (L.funArity f) → GroundTerm L) :
    -- The result of applying f to ground terms yields a ground term
    -- whose underlying term is Term.func f (fun i => (ts i).val).
    -- The result of applying f to ground terms t_1,...,t_n is the
    -- ground term f(t_1,...,t_n). This says the interpretation of f
    -- in the Herbrand structure is syntactic application: the "value"
    -- of f applied to ground terms is the term f(t_1,...,t_n) itself.
    ∃ (result : GroundTerm L),
      result.val = Term.func f (fun i => (ts i).val) 

/-- Definition 9.5.2 (companion): Condition (ii): for every constant symbol c,
    c_H = c. Constants are interpreted as themselves. -/
@[blueprint "chap9__definition_9_5_2"]
theorem constInterp {L : Language} {hNoEq : L.withoutEquality}
    (_H : HerbrandStructure L hNoEq)
    (c : L.constSymbols) :
    -- The constant c interpreted in the Herbrand structure is c itself:
    -- there exists a ground term whose underlying term is Term.const c
    ∃ (result : GroundTerm L),
      result.val = Term.const c 

end HerbrandStructure

-- ===================================================================
-- Example 9.5.1: Logic program with facts, rules, goal clause
-- ===================================================================

/-- Example 9.5.2 (companion): Helper to build a Fin 3 → α from three values. -/
@[blueprint "chap9__example_9_5_2"]
def vec3 (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- Example 9.5.2 (companion): Helper to build a Fin 5 → α from five values. -/
@[blueprint "chap9__example_9_5_2"]
def vec5 (a b c d e : α) : Fin 5 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e

/-- Example 9.5.1 (companion type): Predicate symbols for the
    logic program example: rocksinger (unary), teacher (unary),
    rich (unary). -/
@[blueprint "chap9__example_9_5_1"]
inductive ExLPPred : Type where
  | rocksinger : ExLPPred
  | teacher : ExLPPred
  | rich : ExLPPred

/-- Example 9.5.1 (companion type): Constant symbols:
    jackson, jean, susan. -/
@[blueprint "chap9__example_9_5_1"]
inductive ExLPConst : Type where
  | jackson : ExLPConst
  | jean : ExLPConst
  | susan : ExLPConst

/-- Example 9.5.1 (companion type): The first-order language with
    predicates rocksinger, teacher, rich (each rank 1), constants
    jackson, jean, susan, no function symbols, no equality. -/
@[blueprint "chap9__example_9_5_1"]
def exLPLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := ExLPConst
  predSymbols := ExLPPred
  predArity := fun
    | .rocksinger => 1
    | .teacher => 1
    | .rich => 1
  hasEquality := false

/-- Example 9.5.1 (companion): Helper for building atomic formulae in exLPLang. -/
@[blueprint "chap9__example_9_5_1"]
def mkLPAtom (p : ExLPPred) (t : Term exLPLang) :
    FOAtom exLPLang rfl :=
  FOAtomCore.predN p (fun _ => t)

/-- Example 9.5.1 (companion): The negative clause
    :-teacher(X),rich(X) from the program P. -/
@[blueprint "chap9__example_9_5_1"]
def exLP_negClause : FOHornClause exLPLang rfl :=
  (FOHornClause.goal (hNoEq := by all_goals rfl))
    (LCS.Finset.ofList [ mkLPAtom .teacher (Term.var 0),
      mkLPAtom .rich (Term.var 0) ])

/-- Example 9.5.1 (companion): The query
    ?- neg rocksinger(Y) lor rich(Z). -/
@[blueprint "chap9__example_9_5_1"]
def exLP_query : List (AntiHornClause exLPLang rfl) :=
  [ ⟨{
      posLiterals := [],
      negLiteral := some (mkLPAtom .rocksinger (Term.var 0)),
      existVars := [0] }, by
        simp only [AntiHornClauseCore.WellFormed, AntiHornClauseCore.bodyVarSet,
          List.mem_cons, List.mem_nil_iff]
        simp [
          exLPLang, mkLPAtom, FOAtomCore.toFormula, formulaFVN, termFV, vec1, Set.iUnion, Set.singleton, Fin.exists_fin_succ] ⟩,
    ⟨{
      posLiterals := [mkLPAtom .rich (Term.var 1)],
      negLiteral := none,
      existVars := [1] }, by
        simp only [AntiHornClauseCore.WellFormed, AntiHornClauseCore.bodyVarSet,
          List.mem_cons, List.mem_nil_iff]
        simp [
          exLPLang, mkLPAtom, FOAtomCore.toFormula, formulaFVN, termFV, Set.iUnion, Set.singleton, Fin.exists_fin_succ] ⟩ ]

/-- Example 9.5.1: The logic program with rocksinger/teacher facts, rich(X):-rocksinger(X),
    goal clause :-teacher(X),rich(X), and query ?- neg rocksinger(Y) lor rich(Z). -/
@[blueprint "chap9__example_9_5_1" (main := true)]
def exLogicProgram_9_5_1 : LogicProgram exLPLang rfl :=
  ⟨{
     prog := fun c => c ∈
       [ (FOHornClause.fact (hNoEq := by all_goals rfl)) (mkLPAtom .rocksinger (Term.const .jackson)),
         (FOHornClause.fact (hNoEq := by all_goals rfl)) (mkLPAtom .teacher (Term.const .jean)),
         (FOHornClause.fact (hNoEq := by all_goals rfl)) (mkLPAtom .teacher (Term.const .susan)),
         (FOHornClause.rule (hNoEq := by all_goals rfl))
           (mkLPAtom .rich (Term.var 0))
           (LCS.Finset.ofList [mkLPAtom .rocksinger (Term.var 0)]),
         exLP_negClause ]
     qry := exLP_query
 }, by
    constructor
    · simp [LogicProgramCore.WellFormed, exLP_query]
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
      · intro b hb v hab
        have hbEq : b = exLP_query[1] := List.mem_singleton.mp hb
        subst b
        have h0 := (exLP_query[0].wellFormed.2 v).mpr hab.1
        have h1 := (exLP_query[1].wellFormed.2 v).mpr hab.2
        change v ∈ ([0] : List Nat) at h0
        change v ∈ ([1] : List Nat) at h1
        simp only [List.mem_singleton] at h0 h1
        omega
      · intro b hb
        exact False.elim (List.not_mem_nil hb) ⟩


-- ===================================================================
-- Example 9.5.2: Tower of Hanoi logic program
-- ===================================================================

/-- Example 9.5.2 (companion type): Predicate symbols: hanoi (rank 2),
    move (rank 5), append (rank 3). -/
@[blueprint "chap9__example_9_5_2"]
inductive ExHanoiPred : Type where
  | hanoi : ExHanoiPred
  | move : ExHanoiPred
  | append : ExHanoiPred

/-- Example 9.5.2 (companion type): Function symbols: succ (rank 1),
    cons (rank 2), to (rank 2). -/
@[blueprint "chap9__example_9_5_2"]
inductive ExHanoiFunc : Type where
  | succ : ExHanoiFunc
  | cons : ExHanoiFunc
  | to : ExHanoiFunc

/-- Example 9.5.2 (companion type): Constants: a, b, c (peg names),
    zero (base natural number), nil (empty list). -/
@[blueprint "chap9__example_9_5_2"]
inductive ExHanoiConst : Type where
  | a : ExHanoiConst
  | b : ExHanoiConst
  | c : ExHanoiConst
  | zero : ExHanoiConst
  | nil : ExHanoiConst

/-- Example 9.5.2 (companion type): The first-order language for the
    tower of Hanoi example. -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiLang : Language where
  funSymbols := ExHanoiFunc
  funArity := fun
    | .succ => 1
    | .cons => 2
    | .to => 2
  constSymbols := ExHanoiConst
  predSymbols := ExHanoiPred
  predArity := fun
    | ExHanoiPred.hanoi => 2
    | ExHanoiPred.move => 5
    | .append => 3
  hasEquality := false

/-- Example 9.5.2 (companion): Build a constant term for exHanoiLang. -/
@[blueprint "chap9__example_9_5_2"]
def hanoiConst (k : ExHanoiConst) : Term exHanoiLang :=
  Term.const k

/-- Example 9.5.2 (companion): Build succ(t) for exHanoiLang. -/
@[blueprint "chap9__example_9_5_2"]
def hanoiSucc (t : Term exHanoiLang) : Term exHanoiLang :=
  Term.func .succ (vec1 t)

/-- Example 9.5.2 (companion): Build cons(hd, tl) for exHanoiLang. -/
@[blueprint "chap9__example_9_5_2"]
def hanoiCons (hd tl : Term exHanoiLang) : Term exHanoiLang :=
  Term.func .cons (vec2 hd tl)

/-- Example 9.5.2 (companion): Build to(x, y) for exHanoiLang. -/
@[blueprint "chap9__example_9_5_2"]
def hanoiTo (x y : Term exHanoiLang) : Term exHanoiLang :=
  Term.func .to (vec2 x y)

/-- Example 9.5.2 (companion): Build hanoi(n, out) atomic formula. -/
@[blueprint "chap9__example_9_5_2"]
def mkHanoi (n out : Term exHanoiLang) :
    FOAtom exHanoiLang rfl :=
  FOAtomCore.predN .hanoi (vec2 n out)

/-- Example 9.5.2 (companion): Build move(a,b,c,n,out) atomic formula. -/
@[blueprint "chap9__example_9_5_2"]
def mkMove (a b c n out : Term exHanoiLang) :
    FOAtom exHanoiLang rfl :=
  FOAtomCore.predN .move (vec5 a b c n out)

/-- Example 9.5.2 (companion): Build append(l1,l2,l3) atomic formula. -/
@[blueprint "chap9__example_9_5_2"]
def mkAppend (l1 l2 l3 : Term exHanoiLang) :
    FOAtom exHanoiLang rfl :=
  FOAtomCore.predN .append (vec3 l1 l2 l3)

/-- Example 9.5.2 (companion): The rule hanoi(N,Output):-move(a,b,c,N,Output). -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiClause_hanoi : FOHornClause exHanoiLang rfl :=
  (FOHornClause.rule (hNoEq := by all_goals rfl))
    (mkHanoi (Term.var 0) (Term.var 1))
    (LCS.Finset.ofList [mkMove (hanoiConst .a) (hanoiConst .b) (hanoiConst .c)
            (Term.var 0) (Term.var 1)])

/-- Example 9.5.2 (companion): The recursive move rule. -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiClause_move : FOHornClause exHanoiLang rfl :=
  let vA := Term.var 0
  let vB := Term.var 1
  let vC := Term.var 2
  let vM := Term.var 3
  let vOutput := Term.var 4
  let vOut1 := Term.var 5
  let vOut2 := Term.var 6
  (FOHornClause.rule (hNoEq := by all_goals rfl))
    (mkMove vA vB vC (hanoiSucc vM) vOutput)
    (LCS.Finset.ofList [ mkMove vA vC vB vM vOut1,
      mkMove vC vB vA vM vOut2,
      mkAppend vOut1 (hanoiCons (hanoiTo vA vB) vOut2) vOutput ])

/-- Example 9.5.2 (companion): The base case move(A,B,C,0,nil). -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiClause_moveBase : FOHornClause exHanoiLang rfl :=
  (FOHornClause.fact (hNoEq := by all_goals rfl))
    (mkMove (Term.var 0) (Term.var 1) (Term.var 2)
            (hanoiConst .zero) (hanoiConst .nil))

/-- Example 9.5.2 (companion): The recursive append rule. -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiClause_append_rec : FOHornClause exHanoiLang rfl :=
  (FOHornClause.rule (hNoEq := by all_goals rfl))
    (mkAppend (hanoiCons (Term.var 0) (Term.var 1))
              (Term.var 2)
              (hanoiCons (Term.var 0) (Term.var 3)))
    (LCS.Finset.ofList [mkAppend (Term.var 1) (Term.var 2) (Term.var 3)])

/-- Example 9.5.2 (companion): The base case append(nil,L1,L1). -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiClause_append_base : FOHornClause exHanoiLang rfl :=
  (FOHornClause.fact (hNoEq := by all_goals rfl))
    (mkAppend (hanoiConst .nil) (Term.var 0) (Term.var 0))

/-- Example 9.5.2 (companion): The query ?-hanoi(succ(succ(succ(0))), Output). -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiQuery : List (AntiHornClause exHanoiLang rfl) :=
  [ ⟨{
      posLiterals :=
        [mkHanoi
          (hanoiSucc (hanoiSucc (hanoiSucc (hanoiConst .zero))))
          (Term.var 0)],
      negLiteral := none,
      existVars := [0] }, by
        simp only [AntiHornClauseCore.WellFormed, AntiHornClauseCore.bodyVarSet,
          List.mem_cons, List.mem_nil_iff]
        simp [
          exHanoiLang, mkHanoi, hanoiSucc, hanoiConst, FOAtomCore.toFormula, formulaFVN, termFV, vec2, vec1, Set.iUnion, Set.singleton,
          Fin.exists_fin_succ]
        exact fun _ h => False.elim h ⟩ ]

/-- Example 9.5.2: The complete tower of Hanoi logic program with
    five definite clauses and a query for the 3-disk solution. -/
@[blueprint "chap9__example_9_5_2" (main := true)]
def exHanoiProgram : LogicProgram exHanoiLang rfl :=
  ⟨{
     prog := fun c => c ∈
       [ exHanoiClause_hanoi,
         exHanoiClause_move,
         exHanoiClause_moveBase,
         exHanoiClause_append_rec,
         exHanoiClause_append_base ]
     qry := exHanoiQuery
 }, by
    simp [LogicProgramCore.WellFormed, exHanoiQuery]
    exact List.Pairwise.cons (fun _ h => False.elim (List.not_mem_nil h)) List.Pairwise.nil ⟩


-- ===================================================================
-- Example 9.5.3: Indefinite answer example
-- ===================================================================

/-- Example 9.5.3 (companion type): Single unary predicate Q. -/
@[blueprint "chap9__example_9_5_3"]
inductive ExIndAnswerPred : Type where
  | Q : ExIndAnswerPred

/-- Example 9.5.3 (companion type): Two constants a and b. -/
@[blueprint "chap9__example_9_5_3"]
inductive ExIndAnswerConst : Type where
  | a : ExIndAnswerConst
  | b : ExIndAnswerConst

/-- Example 9.5.3 (companion type): Language with one unary predicate
    Q, two constants a and b, no function symbols. -/
@[blueprint "chap9__example_9_5_3"]
def exIndAnswerLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := ExIndAnswerConst
  predSymbols := ExIndAnswerPred
  predArity := fun | .Q => 1
  hasEquality := false

/-- Example 9.5.3 (companion): Helper for building Q(t). -/
@[blueprint "chap9__example_9_5_3"]
def mkQ (t : Term exIndAnswerLang) : FOAtom exIndAnswerLang rfl :=
  FOAtomCore.predN .Q (vec1 t)

/-- Example 9.5.3: The logic program where P = {neg Q(a) lor neg Q(b)} and
    G = exists x. neg Q(x): P supset G is valid but no single term t satisfies P supset neg Q(t). -/
@[blueprint "chap9__example_9_5_3" (main := true)]
def exIndefiniteAnswer : LogicProgram exIndAnswerLang rfl :=
  ⟨{
     prog := fun c => c ∈
       [ -- neg Q(a) lor neg Q(b) as a goal clause :-Q(a),Q(b)
         (FOHornClause.goal (hNoEq := by all_goals rfl))
           (LCS.Finset.ofList [ mkQ (Term.const .a),
             mkQ (Term.const .b) ]) ]
     qry :=
       [ -- exists x. neg Q(x)
         ⟨{
           posLiterals := [],
           negLiteral := some (mkQ (Term.var 0)),
           existVars := [0] }, by
          simp only [AntiHornClauseCore.WellFormed, AntiHornClauseCore.bodyVarSet,
            List.mem_cons, List.mem_nil_iff]
          simp [
            exIndAnswerLang, mkQ, FOAtomCore.toFormula, formulaFVN, termFV, vec1, Set.iUnion, Set.singleton, Fin.exists_fin_succ] ⟩ ]
 }, by
    simp [LogicProgramCore.WellFormed]
    exact List.Pairwise.cons (fun _ h => False.elim (List.not_mem_nil h)) List.Pairwise.nil ⟩


-- ===================================================================
-- Helper: Evaluation of Horn clauses in Herbrand structures
-- ===================================================================

/-- Definition 9.5.3 (required helper — raw term evaluation): Evaluate a
    term in a Herbrand structure under a variable assignment mapping
    variables to ground terms. Returns the underlying `Term L` (without
    the closed-term witness); used as the computational core of
    `evalTermInHerbrand`. -/
@[blueprint "chap9__definition_9_5_2"]
def evalTermInHerbrandRaw {L : Language}
    (assign : Nat → GroundTerm L) : Term L → Term L
  | .var v => (assign v).val
  | .const c => .const c
  | .func f args => .func f (fun i =>
      evalTermInHerbrandRaw assign (args i))

/-- Definition 9.5.3 (required helper — closedness witness): The raw
    term evaluation of any term under a ground-term assignment is
    itself closed. Packaged with `evalTermInHerbrandRaw` into the
    `GroundTerm` subtype by `evalTermInHerbrand`. -/
@[blueprint "chap9__definition_9_5_2"]
theorem evalTermInHerbrandRaw_closed {L : Language}
    (assign : Nat → GroundTerm L) (t : Term L) :
    Term.isClosed (evalTermInHerbrandRaw assign t) 

/-- Definition 9.5.3 (companion): Evaluate a term in a Herbrand structure under a variable
    assignment mapping variables to ground terms. -/
@[blueprint "chap9__definition_9_5_2"]
def evalTermInHerbrand {L : Language}
    (assign : Nat → GroundTerm L) (t : Term L) : GroundTerm L :=
  ⟨evalTermInHerbrandRaw assign t, evalTermInHerbrandRaw_closed assign t⟩

/-- Definition 9.5.3 (companion): Evaluate a formula in a Herbrand structure
    under a variable assignment mapping variables to ground terms. -/
@[blueprint "chap9__definition_9_5_2"]
def evalFormulaInHerbrand {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq)
    (assign : Nat → GroundTerm L) : FormulaN L → Prop
  | .predN P args =>
    H.predInterp P (List.ofFn (fun i =>
      evalTermInHerbrand assign (args i)))
  | .eq_ _ t1 t2 =>
    (evalTermInHerbrand assign t1).val =
    (evalTermInHerbrand assign t2).val
  | .neg A => ¬ evalFormulaInHerbrand H assign A
  | .conj A B =>
    evalFormulaInHerbrand H assign A ∧
    evalFormulaInHerbrand H assign B
  | .disj A B =>
    evalFormulaInHerbrand H assign A ∨
    evalFormulaInHerbrand H assign B
  | .impl A B =>
    evalFormulaInHerbrand H assign A →
    evalFormulaInHerbrand H assign B
  | .all i A =>
    ∀ (gt : GroundTerm L),
      evalFormulaInHerbrand H (fun n =>
        if n = i then gt else assign n) A
  | .ex i A =>
    ∃ (gt : GroundTerm L),
      evalFormulaInHerbrand H (fun n =>
        if n = i then gt else assign n) A

namespace FOHornClause

/-- Definition 9.5.2 (companion): Evaluate a Horn clause in a Herbrand
    structure: for a given variable assignment, the clause is satisfied iff
    whenever all body atoms are true, the head atom (if any) is also true.
    Clause-level specialization of Herbrand formula evaluation. -/
@[blueprint "chap9__definition_9_5_2"]
def evalInHerbrand {L : Language} (hNoEq : L.withoutEquality)
    (H : HerbrandStructure L hNoEq)
    (c : FOHornClause L hNoEq)
    (assign : Nat → GroundTerm L) : Prop :=
  match c with
  | FOHornClauseCore.fact head => evalFormulaInHerbrand H assign head.toFormula
  | FOHornClauseCore.rule head body =>
    (∀ atom ∈ body,
      evalFormulaInHerbrand H assign atom.toFormula) →
      evalFormulaInHerbrand H assign head.toFormula
  | FOHornClauseCore.goal body =>
    ¬ (∀ atom ∈ body,
      evalFormulaInHerbrand H assign atom.toFormula)

end FOHornClause

-- ===================================================================
-- Definition 9.5.3: Semantics of a logic program
-- ===================================================================

/-- Lemma 9.5.2 (companion): find the index of a value in a list,
    returning none if absent. -/
@[blueprint "chap9__lemma_9_5_2"]
def findIndex [BEq α] (l : List α) (v : α) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => if x == v then some 0
    else (findIndex xs v).map (· + 1)

/-- A ground q-tuple; q may be zero independently of the query size (SQ32). -/
@[blueprint "chap9__definition_9_5_3"]
abbrev GroundAnswerTuple (L : Language) (q : Nat) := Fin q → GroundTerm L

/-- Definition 9.5.3: A finite nonempty extensional family of ground q-tuples. -/
@[blueprint "chap9__definition_9_5_3"]
def DisjunctiveAnswer (L : Language) (q : Nat) : Type :=
  { S : LCS.Finset (GroundAnswerTuple L q) // ∃ t, t ∈ S }

/-- The finite answer family consisting of one ground q-tuple. -/
@[blueprint "chap9__definition_9_5_3"]
def singletonAnswer {L : Language} {q : Nat} (t : GroundAnswerTuple L q) :
    DisjunctiveAnswer L q :=
  ⟨LCS.Finset.singleton t, t, (LCS.Finset.mem_singleton t t).mpr rfl⟩

/-- Simultaneously assign the fixed output coordinates of a ground answer.
    Exact output coverage makes the remaining assignment irrelevant to the query. -/
@[blueprint "chap9__definition_9_5_3"]
noncomputable def groundAnswerAssignment {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq)
    (tuple : GroundAnswerTuple L (lp.outputVarList hNoEq).length)
    (assign : Nat → GroundTerm L) : Nat → GroundTerm L := by
  classical
  exact fun v => if h : ∃ i : Fin (lp.outputVarList hNoEq).length,
      (lp.outputVarList hNoEq).get i = v then tuple (Classical.choose h) else assign v

/-- Definition 9.5.3: All clauses of P hold at every assignment before the
    disjunction of ground matrix instances is tested (SQ25, SQ30–SQ35). -/
@[blueprint "chap9__definition_9_5_3"]
def validInFreeStructures {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (_hConst : Nonempty L.constSymbols)
    (tuples : DisjunctiveAnswer L (lp.outputVarList hNoEq).length) : Prop :=
  ∀ (H : HerbrandStructure L hNoEq),
    (∀ (s : Nat → GroundTerm L) c, c ∈ lp.prog → FOHornClause.evalInHerbrand hNoEq H c s) →
    ∀ assign : Nat → GroundTerm L,
      ∃ tuple, tuple ∈ tuples.val ∧ ∃ a ∈ lp.qry,
        (∀ atom ∈ a.posLiterals,
          evalFormulaInHerbrand H (groundAnswerAssignment hNoEq lp tuple assign) atom.toFormula) ∧
        (match a.negLiteral with
          | none => True
          | some atom => ¬ evalFormulaInHerbrand H
              (groundAnswerAssignment hNoEq lp tuple assign) atom.toFormula)

/-- Definition 9.5.3: M(P,G) is a family of finite nonempty answer sets.
    The printed big union is read as a family (SQ35, OD-9-1). -/
@[blueprint "chap9__definition_9_5_3" (main := true)]
def programSemantics {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols) :
    Set (DisjunctiveAnswer L (lp.outputVarList hNoEq).length) :=
  validInFreeStructures hNoEq lp hConst

/-- The ground-answer task tests one exact output tuple against universal P. -/
@[blueprint "chap9__definition_9_5_3"]
def groundAnswerValid {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols)
    (t : GroundAnswerTuple L (lp.outputVarList hNoEq).length) : Prop :=
  programSemantics hNoEq lp hConst (singletonAnswer t)

/-- The general query task: universal program truth entails the closed query. -/
@[blueprint "chap9__definition_9_5_3"]
def queryValid {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (_hConst : Nonempty L.constSymbols) : Prop :=
  ∀ H : HerbrandStructure L hNoEq,
    (∀ s c, c ∈ lp.prog → FOHornClause.evalInHerbrand hNoEq H c s) →
    ∀ s, evalFormulaInHerbrand H s lp.toSentence

namespace programSemantics

/-- Under the PROLOG restriction select singleton answers (SQ35). -/
@[blueprint "chap9__definition_9_5_3"]
def isDefiniteSemantics {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols)
    (_hProlog : lp.isPROLOG hNoEq) :
    Set (DisjunctiveAnswer L (lp.outputVarList hNoEq).length) :=
  fun S => programSemantics hNoEq lp hConst S ∧ ∃ t, S.val = LCS.Finset.singleton t

/-- Membership in the definite specialization is valid singleton membership. -/
@[blueprint "chap9__definition_9_5_3"]
theorem mem_isDefiniteSemantics {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols)
    (hProlog : lp.isPROLOG hNoEq)
    (S : DisjunctiveAnswer L (lp.outputVarList hNoEq).length) :
    isDefiniteSemantics hNoEq lp hConst hProlog S ↔
      programSemantics hNoEq lp hConst S ∧ ∃ t, S.val = LCS.Finset.singleton t

/-- A valid PROLOG query has a singleton answer, for arbitrary P (SQ30, SQ35). -/
@[attach_debt, blueprint "chap9__definition_9_5_3"]
theorem definiteAnswer_exists {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols)
    (hProlog : lp.isPROLOG hNoEq) (hValid : queryValid hNoEq lp hConst) :
    ∃ S, isDefiniteSemantics hNoEq lp hConst hProlog S

end programSemantics

-- ===================================================================
-- Lemma 9.5.1 (helper defs): Herbrand homomorphism and model
-- construction
-- ===================================================================

/-- Lemma 9.5.1 (required helper — closedness descent): If `f(t_1,...,t_n)`
    is closed, then each argument `t_i` is closed. Used to descend into
    function arguments when defining the Herbrand homomorphism by
    structural recursion on ground terms. -/
@[blueprint "chap9__lemma_9_5_1"]
theorem closedFunc_arg {L : Language}
    {f : L.funSymbols} {args : Fin (L.funArity f) → Term L}
    (hcl : Term.isClosed (Term.func f args))
    (i : Fin (L.funArity f)) :
    Term.isClosed (args i) 

/-- Lemma 9.5.1 (helper): The homomorphism h : GroundTerm L -> A from
    the Herbrand universe to an arbitrary model's domain, defined by
    evaluating each ground term in the model. h(c) = interp(c) for
    constants, h(f(t_1,...,t_n)) = f_A(h(t_1),...,h(t_n)) for
    function applications. Here we represent the model's domain as
    a type A, with interpretations for constants and functions. -/
@[blueprint "chap9__lemma_9_5_1"]
noncomputable def herbrandHomomorphism {L : Language}
    (constInterp : L.constSymbols → α)
    (funcInterp : (f : L.funSymbols) → (Fin (L.funArity f) → α) → α) :
    GroundTerm L → α :=
  fun gt => evalGroundTerm constInterp funcInterp gt.val gt.property
where
  evalGroundTerm {L : Language}
      (ci : L.constSymbols → α)
      (fi : (f : L.funSymbols) → (Fin (L.funArity f) → α) → α) :
      (t : Term L) → Term.isClosed t → α
    | .var v, hcl =>
        -- Term.isClosed (Term.var v) is termFV (Term.var v) = ∅ = {v} = ∅
        -- which is absurd since v ∈ {v}.
        have hv : (termFV (Term.var v)) v := rfl
        absurd hv (by rw [hcl]; exact id)
    | .const c, _ => ci c
    | .func f args, hcl => fi f (fun i =>
        evalGroundTerm ci fi (args i) (closedFunc_arg hcl i))

/-- Lemma 9.5.1 (helper): Construct a HerbrandStructure from an
    arbitrary L-structure (represented by its interpretation functions)
    and the homomorphism h, by defining
    P_H(t_1,...,t_n) iff P_A(h(t_1),...,h(t_n)). -/
@[blueprint "chap9__lemma_9_5_1"]
noncomputable def herbrandModelFromArbitrary {L : Language} {hNoEq : L.withoutEquality}
    (constI : L.constSymbols → α)
    (funcI : (f : L.funSymbols) → (Fin (L.funArity f) → α) → α)
    (predI : L.predSymbols → List α → Prop)
    (hConst : Nonempty L.constSymbols) :
    HerbrandStructure L hNoEq where
  predInterp := fun P ts =>
    predI P (ts.map (herbrandHomomorphism constI funcI))
  hasConstant := hConst

-- ===================================================================
-- Lemma 9.5.1 (helper defs): NNF, universal-only, no-equality
-- predicates for formulas
-- ===================================================================

-- formulaNoEq is imported from SemanticsN (§5.4 companion)

/-- Lemma 9.5.1 (required companion): A FormulaN is in negation normal form.
    Used to state that a sentence X on which Lem 9.5.1 operates has no
    implications and only atom-level negations. -/
@[blueprint "chap9__lemma_9_5_1"]
def formulaIsNNF {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg (.predN _ _) => True
  | .neg (.eq_ _ _ _) => True
  | .neg _ => False
  | .conj A B => formulaIsNNF A ∧ formulaIsNNF B
  | .disj A B => formulaIsNNF A ∧ formulaIsNNF B
  | .impl _ _ => False
  | .all _ A => formulaIsNNF A
  | .ex _ A => formulaIsNNF A

/-- Lemma 9.5.1 (required companion): A FormulaN contains only universal
    quantifiers (no existential). -/
@[blueprint "chap9__lemma_9_5_1"]
def formulaUniversalOnly {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => formulaUniversalOnly A
  | .conj A B => formulaUniversalOnly A ∧ formulaUniversalOnly B
  | .disj A B => formulaUniversalOnly A ∧ formulaUniversalOnly B
  | .impl A B => formulaUniversalOnly A ∧ formulaUniversalOnly B
  | .all _ A => formulaUniversalOnly A
  | .ex _ _ => False

-- ===================================================================
-- Lemma 9.5.1 (helper defs): Evaluation of ground terms in a model,
-- and the Herbrand structure constructed from a model
-- ===================================================================

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Evaluate a ground term in a model A by
    structural recursion. h(c) = A.interpConst c,
    h(f(t_1,...,t_n)) = A.interpFunc f (h(t_1),...,h(t_n)). -/
def evalGroundTermInModel {L : Language} (A : Structure L) :
    (t : Term L) → Term.isClosed t → A.carrier
  | .var v, hcl => absurd (show termFV (.var v) v from rfl) (by rw [hcl]; exact id)
  | .const c, _ => A.interpConst c
  | .func f args, hcl => A.interpFunc f (fun i =>
      evalGroundTermInModel A (args i) (closedFunc_arg hcl i))

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): The homomorphism h : GroundTerm L → A.carrier
    mapping each ground term to its interpretation in the model A. -/
def herbrandHom {L : Language} (A : Structure L) (gt : GroundTerm L) : A.carrier :=
  evalGroundTermInModel A gt.val gt.property

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): The homomorphism commutes with term evaluation:
    termEval A (h ∘ s) t = h(evalTermInHerbrand s t). -/
theorem herbrandHom_comm {L : Language} (A : Structure L)
    (s : Nat → GroundTerm L) (t : Term L) :
    termEval A (fun v => herbrandHom A (s v)) t =
    herbrandHom A (evalTermInHerbrand s t) := by
-- BEGIN PROOF
  simp [herbrandHom, evalTermInHerbrand]
  induction t with
  | var v => simp [termEval, evalTermInHerbrandRaw]
  | const c => simp [termEval, evalTermInHerbrandRaw, evalGroundTermInModel]
  | func f args ih =>
    simp [termEval, evalTermInHerbrandRaw, evalGroundTermInModel]
    congr 1; funext i; exact ih i

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): The assignment update commutes with the
    homomorphism h. -/
theorem herbrandHom_assignUpdate {L : Language} (A : Structure L)
    (s : Nat → GroundTerm L) (i : Nat) (gt : GroundTerm L) :
    assignUpdate (fun v => herbrandHom A (s v)) i (herbrandHom A gt) =
    (fun v => herbrandHom A (if v = i then gt else s v)) := by
-- BEGIN PROOF
  funext v; simp [assignUpdate]; split <;> rfl

/-- Lemma 9.5.2 (required helper): A default ground term from the
    nonemptiness witness, used for list indexing defaults (list `.getD`
    fallback and `.headD` fallback) in the statement of the definite
    answer lemma. -/
@[blueprint "chap9__lemma_9_5_2"]
noncomputable def herbDefaultGT {L : Language}
    (hConst : Nonempty L.constSymbols) : GroundTerm L :=
  ⟨Term.const (Classical.choice hConst), by simp [Term.isClosed, termFV]⟩

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Construct a Herbrand structure from a model A.
    P_H(t_1,...,t_n) iff P_A(h(t_1),...,h(t_n)). -/
noncomputable def herbrandStructureFromModel {L : Language} {hNoEq : L.withoutEquality}
    (A : Structure L) (hConst : Nonempty L.constSymbols) :
    HerbrandStructure L hNoEq where
  predInterp := fun P ts => A.interpPred P (fun i =>
    herbrandHom A (ts.getD i.val (herbDefaultGT hConst)))
  hasConstant := hConst

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): List.ofFn getD for Fin index. -/
theorem ofFn_getD_fin {n : Nat} {α : Type} (f : Fin n → α)
    (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
-- BEGIN PROOF
  unfold List.getD
  rw [List.getElem?_eq_getElem (h := by simp)]
  simp [List.getElem_ofFn]

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): The predN interpretation of the constructed
    Herbrand structure matches the model's interpretation. -/
theorem herbrandStructureFromModel_predN {L : Language} {hNoEq : L.withoutEquality}
    (A : Structure L) (hConst : Nonempty L.constSymbols)
    (P : L.predSymbols) (s : Nat → GroundTerm L)
    (args : Fin (L.predArity P) → Term L) :
    (herbrandStructureFromModel (hNoEq := hNoEq) A hConst).predInterp P
      (List.ofFn (fun i => evalTermInHerbrand s (args i))) ↔
    A.interpPred P
      (fun i => termEval A (fun v => herbrandHom A (s v)) (args i)) := by
-- BEGIN PROOF
  have key : (fun (i : Fin (L.predArity P)) =>
      herbrandHom A ((List.ofFn (fun j =>
        evalTermInHerbrand s (args j))).getD i.val
          (herbDefaultGT hConst))) =
    (fun i => termEval A (fun v => herbrandHom A (s v)) (args i)) := by
    funext i; rw [ofFn_getD_fin]
    exact (herbrandHom_comm A s (args i)).symm
  simp only [herbrandStructureFromModel, HerbrandStructure.predInterp, herbDefaultGT] at key ⊢
  rw [key]





-- ===================================================================
-- Lemma 9.5.1 (helper): Forward direction of the Herbrand theorem
-- ===================================================================

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): If A satisfies X under assignment h ∘ s,
    then the Herbrand structure constructed from A satisfies X under s.
    Proved by induction on formula structure using NNF, universal-only,
    and no-equality conditions. -/
theorem herbrand_model_transfer {L : Language} {hNoEq : L.withoutEquality}
    (A : Structure L) (hConst : Nonempty L.constSymbols)
    (s : Nat → GroundTerm L) (X : FormulaN L)
    (hNNF : formulaIsNNF X) (hUniv : formulaUniversalOnly X)
    (hFormulaNoEq : formulaNoEq X) :
    formulaEvalN A X (fun v => herbrandHom A (s v)) →
    evalFormulaInHerbrand (herbrandStructureFromModel (hNoEq := hNoEq) A hConst) s X := by
-- BEGIN PROOF
  induction X generalizing s with
  | predN P args =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact (herbrandStructureFromModel_predN (hNoEq := hNoEq) A hConst P s args).mpr
  | eq_ _ _ _ => exact fun _ => False.elim hFormulaNoEq
  | neg B _ =>
    cases B with
    | predN P args =>
      simp only [formulaEvalN, evalFormulaInHerbrand]
      exact fun hN hH => hN
        ((herbrandStructureFromModel_predN (hNoEq := hNoEq) A hConst P s args).mp hH)
    | eq_ _ _ _ => exact fun _ => False.elim hFormulaNoEq
    | _ => exact fun _ => False.elim hNNF
  | conj A B ihA ihB =>
    obtain ⟨hNA, hNB⟩ := hNNF
    obtain ⟨hUA, hUB⟩ := hUniv
    obtain ⟨hEA, hEB⟩ := hFormulaNoEq
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact fun ⟨ha, hb⟩ =>
      ⟨ihA s hNA hUA hEA ha, ihB s hNB hUB hEB hb⟩
  | disj A B ihA ihB =>
    obtain ⟨hNA, hNB⟩ := hNNF
    obtain ⟨hUA, hUB⟩ := hUniv
    obtain ⟨hEA, hEB⟩ := hFormulaNoEq
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact fun h => h.elim
      (Or.inl ∘ ihA s hNA hUA hEA)
      (Or.inr ∘ ihB s hNB hUB hEB)
  | impl _ _ => exact fun _ => False.elim hNNF
  | all i B ih =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    intro hAll gt
    let s' : Nat → GroundTerm L := fun n => if n = i then gt else s n
    apply ih s' hNNF hUniv hFormulaNoEq
    rw [← herbrandHom_assignUpdate]
    exact hAll (herbrandHom A gt)
  | ex _ _ => exact fun _ => False.elim hUniv

-- ===================================================================
-- Lemma 9.5.1 (helper): Backward direction — Herbrand structure
-- embeds into a general L-structure
-- ===================================================================

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Convert a HerbrandStructure to a general
    L-Structure with carrier = GroundTerm L. -/
noncomputable def herbrandToStructure {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq) : Structure L where
  carrier := GroundTerm L
  carrierNonempty := by
    obtain ⟨c⟩ := H.hasConstant
    exact ⟨⟨Term.const c, by simp [Term.isClosed, termFV]⟩⟩
  interpFunc := fun f args =>
    ⟨Term.func f (fun i => (args i).val), by
      show termFV _ = ∅; funext x; apply propext; constructor
      · intro hx; simp [termFV] at hx; obtain ⟨i, hi⟩ := hx
        have := (args i).property
        rw [Term.isClosed] at this; rw [this] at hi; exact hi
      · exact False.elim⟩
  interpConst := fun c =>
    ⟨Term.const c, by simp [Term.isClosed, termFV]⟩
  interpPred := fun P args => H.predInterp P (List.ofFn args)

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Term evaluation in herbrandToStructure
    agrees with evalTermInHerbrand at the val level. -/
theorem herbrandToStructure_termEval_val {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq) (s : Nat → GroundTerm L)
    (t : Term L) :
    (termEval (herbrandToStructure H) s t).val =
    evalTermInHerbrandRaw s t := by
-- BEGIN PROOF
  induction t with
  | var v => simp [termEval, evalTermInHerbrandRaw]
  | const c =>
    simp [termEval, evalTermInHerbrandRaw, herbrandToStructure]
  | func f args ih =>
    simp [termEval, evalTermInHerbrandRaw, herbrandToStructure]
    funext i; exact ih i

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Term evaluation in herbrandToStructure
    agrees with evalTermInHerbrand. -/
theorem herbrandToStructure_termEval {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq) (s : Nat → GroundTerm L)
    (t : Term L) :
    termEval (herbrandToStructure H) s t =
    evalTermInHerbrand s t := by
-- BEGIN PROOF
  apply Subtype.ext; simp [evalTermInHerbrand]
  exact herbrandToStructure_termEval_val H s t

-- retained: used by LCS.SLD.LogicProgramming.Completeness
/-- Lemma 9.5.1 (helper): Formula evaluation in herbrandToStructure
    agrees with evalFormulaInHerbrand. -/
theorem herbrandToStructure_formulaEval {L : Language} {hNoEq : L.withoutEquality}
    (H : HerbrandStructure L hNoEq) (s : Nat → GroundTerm L)
    (A : FormulaN L) :
    formulaEvalN (herbrandToStructure H) A s ↔
    evalFormulaInHerbrand H s A := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P args =>
    show (herbrandToStructure H).interpPred P
        (fun i => termEval (herbrandToStructure H) s (args i)) ↔
      H.predInterp P
        (List.ofFn (fun i => evalTermInHerbrand s (args i)))
    have hinterp : (herbrandToStructure H).interpPred =
      fun P args => H.predInterp P (List.ofFn args) := rfl
    rw [hinterp]
    have : (fun i => termEval (herbrandToStructure H) s (args i)) =
      (fun i => evalTermInHerbrand s (args i)) :=
      funext (fun i => herbrandToStructure_termEval H s (args i))
    rw [this]
  | eq_ _ t1 t2 =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    rw [herbrandToStructure_termEval H s t1,
        herbrandToStructure_termEval H s t2]
    exact Subtype.ext_iff
  | neg A ih =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact not_congr (ih s)
  | conj A B ihA ihB =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    exact imp_congr (ihA s) (ihB s)
  | all i A ih =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    constructor
    · intro hAll gt; rw [← ih]; exact hAll gt
    · intro hAll gt; erw [ih]; exact hAll gt
  | ex i A ih =>
    simp only [formulaEvalN, evalFormulaInHerbrand]
    constructor
    · intro ⟨gt, hgt⟩; exact ⟨gt, by rw [← ih]; exact hgt⟩
    · intro ⟨gt, hgt⟩; exact ⟨gt, by erw [ih]; exact hgt⟩

-- ===================================================================
-- Lemma 9.5.1: Herbrand satisfiability theorem
-- ===================================================================

/-- Lemma 9.5.1: A sentence X in NNF containing only universal quantifiers is satisfiable
    in some model iff it is satisfiable in some free structure. -/
@[blueprint "chap9__lemma_9_5_1" (main := true)]
theorem herbrand_satisfiability {L : Language}
    (X : FormulaN L)
    -- X is a sentence (no free variables)
    (_hSentence : FormulaN.isClosed X)
    -- X is in NNF (negation normal form)
    (hNNF : formulaIsNNF X)
    -- X contains only universal quantifiers (no existential)
    (hUniv : formulaUniversalOnly X)
    -- L has no equality
    (hNoEq : L.withoutEquality)
    -- L has at least one constant
    (hConst : Nonempty L.constSymbols)
    -- X contains no equality subformulae
    (hNoEqF : formulaNoEq X) :
    -- X is satisfiable in some L-structure iff satisfiable in some
    -- Herbrand structure.
    (∃ (M : Structure L) (s : Assignment M),
      formulaEvalN M X s) ↔
    (∃ (H : HerbrandStructure L hNoEq)
       (s : Nat → GroundTerm L),
      evalFormulaInHerbrand H s X) 

-- ===================================================================
-- Example 9.5.3 (companion theorems): Indefinite answer properties
-- ===================================================================

/-- Example 9.5.3 (companion): The ground term constant `a` of
    exIndAnswerLang. -/
@[blueprint "chap9__example_9_5_3"]
def groundConst_a : GroundTerm exIndAnswerLang :=
  ⟨Term.const ExIndAnswerConst.a, by simp [Term.isClosed, termFV]⟩

/-- Example 9.5.3 (companion): The ground term constant `b` of
    exIndAnswerLang. -/
@[blueprint "chap9__example_9_5_3"]
def groundConst_b : GroundTerm exIndAnswerLang :=
  ⟨Term.const ExIndAnswerConst.b, by simp [Term.isClosed, termFV]⟩

/-- Example 9.5.3 (companion): The formula
    neg Q(a) lor neg Q(b) supset exists x. neg Q(x) is valid.
    In any structure, if neg Q(a_A) or neg Q(b_A) holds, then
    exists x. neg Q(x) holds (take x = a_A or x = b_A). -/
@[blueprint "chap9__example_9_5_3"]
theorem exIndAnswer_valid :
    -- For every HerbrandStructure over exIndAnswerLang,
    -- if the program clause (neg Q(a) lor neg Q(b)) is satisfied,
    -- then the query (exists x. neg Q(x)) is satisfied.
    ∀ (H : HerbrandStructure exIndAnswerLang rfl),
      -- If H satisfies P: for some ground term t, Q(t) fails
      -- (i.e. neg Q(a) or neg Q(b) holds)
      (¬ H.predInterp .Q [groundConst_a] ∨
       ¬ H.predInterp .Q [groundConst_b]) →
      -- Then there exists a ground term t such that neg Q(t) holds
      ∃ (t : GroundTerm exIndAnswerLang),
        ¬ H.predInterp .Q [t] 

-- H where Q holds for everything except groundConst_b


-- H where Q holds for everything except groundConst_a


/-- Example 9.5.3: Every term, including a variable, has a countermodel
    and assignment to its proposed single answer (SQ44, OD-9-1). -/
@[blueprint "chap9__example_9_5_3"]
theorem exIndAnswer_noSingleWitness :
    ∀ (t : Term exIndAnswerLang),
      ∃ (H : HerbrandStructure exIndAnswerLang rfl) (s : Nat → GroundTerm exIndAnswerLang),
        (¬ H.predInterp .Q [groundConst_a] ∨
         ¬ H.predInterp .Q [groundConst_b]) ∧
        H.predInterp .Q [evalTermInHerbrand s t]

-- ===================================================================
-- Lemma 9.5.2: Definite answer lemma
-- ===================================================================



-- Helper: findIndex returns some i when v ∈ l


-- Helper: for atomic formulas, eval transfers via predInterp monotonicity
-- and FV agreement


/-- Universal satisfaction of a finite Horn program in an ordinary
    structure, used by the definite answer lemma (SQ25, R-SEM). -/
@[blueprint "chap9__lemma_9_5_2"]
def definiteProgramModels {L : Language} {hNoEq : L.withoutEquality}
    (P : List (FOHornClause L hNoEq)) (M : Structure L) : Prop :=
  ∀ (s : Assignment M) c, c ∈ P → match c with
    | FOHornClauseCore.fact a => formulaEvalN M a.toFormula s
    | FOHornClauseCore.rule a bs => (∀ b ∈ bs, formulaEvalN M b.toFormula s) → formulaEvalN M a.toFormula s
    | FOHornClauseCore.goal bs => ¬ (∀ b ∈ bs, formulaEvalN M b.toFormula s)

/-- Lemma 9.5.2: a finite definite P entailing ∃zs (⋀ B) has a uniform
    ground tuple of length q = |zs| whose matrix instance follows from P
    in every ordinary structure. B is a finite list of equality-free atoms;
    its conjunction may be empty (true), and q and P may independently be
    empty (OD-9-1/SQ32). Agreement outside zs expresses existential closure;
    the conclusion substitutes simultaneously into the open atoms (SQ31). -/
@[attach_debt, blueprint "chap9__lemma_9_5_2" (main := true)]
theorem definiteAnswerLemma {L : Language} (hNoEq : L.withoutEquality)
    (P : List (FOHornClause L hNoEq))
    (hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (B : List (FOAtom L hNoEq)) (zs : List Nat)
    (hBodyVars : ∀ atom ∈ B, formulaFVN atom.toFormula ⊆ fun v => v ∈ zs)
    (hConst : Nonempty L.constSymbols)
    (hEntails : ∀ M : Structure L, definiteProgramModels P M →
      ∀ s : Assignment M, ∃ s' : Assignment M,
        (∀ v, v ∉ zs → s' v = s v) ∧ ∀ atom ∈ B, formulaEvalN M atom.toFormula s') :
    ∃ tuple : List (GroundTerm L), tuple.length = zs.length ∧
      ∀ M : Structure L, definiteProgramModels P M → ∀ s : Assignment M,
        ∀ atom ∈ B, formulaEvalN M
          (formulaSubstAll atom.toFormula (fun v => match findIndex zs v with
            | some i => (tuple.getD i (herbDefaultGT hConst)).val
            | none => .var v)) s

/-- Concatenation of the move lists represented by nil and cons in
    Example 9.5.2; the two constructors give the printed append roles. -/
@[blueprint "chap9__example_9_5_2"]
inductive HanoiAppendRelation : Term exHanoiLang → Term exHanoiLang → Term exHanoiLang → Prop
  | nil (ys) : HanoiAppendRelation (hanoiConst .nil) ys ys
  | cons {x xs ys zs} : HanoiAppendRelation xs ys zs →
      HanoiAppendRelation (hanoiCons x xs) ys (hanoiCons x zs)

/-- Recursive Hanoi move relation: transfer from source to destination using
    the spare peg, transfer the smaller tower to the spare peg, record the
    directed move to(source,destination), then transfer from spare to destination.
    This is the qualitative recursive interpretation of the printed roles
    in Example 9.5.2 (OD-9-5, X-2). -/
@[blueprint "chap9__example_9_5_2"]
inductive HanoiMoveRelation : Term exHanoiLang → Term exHanoiLang →
    Term exHanoiLang → Term exHanoiLang → Term exHanoiLang → Prop
  | zero (source destination spare) :
      HanoiMoveRelation source destination spare (hanoiConst .zero) (hanoiConst .nil)
  | succ {source destination spare n out1 out2 output} :
      HanoiMoveRelation source spare destination n out1 →
      HanoiMoveRelation spare destination source n out2 →
      HanoiAppendRelation out1 (hanoiCons (hanoiTo source destination) out2) output →
      HanoiMoveRelation source destination spare (hanoiSucc n) output

/-- Free interpretation of the three predicates by Hanoi transfer and list
    concatenation. hanoi fixes the source, destination and spare to a,b,c. -/
@[blueprint "chap9__example_9_5_2"]
def exHanoiMoveStructure : HerbrandStructure exHanoiLang rfl where
  hasConstant := ⟨.zero⟩
  predInterp := fun p args => match p, args with
    | .hanoi, [n, output] =>
        HanoiMoveRelation (hanoiConst .a) (hanoiConst .b) (hanoiConst .c) n.val output.val
    | .move, [source, destination, spare, n, output] =>
        HanoiMoveRelation source.val destination.val spare.val n.val output.val
    | .append, [xs, ys, zs] => HanoiAppendRelation xs.val ys.val zs.val
    | _, _ => False

/-- The five-clause program has the recursive Hanoi move interpretation,
    with the printed peg roles and the sole output coordinate Output = 0.
    The three-disc query is the existing exHanoiQuery (OD-9-5, X-2). -/
@[attach_debt, blueprint "chap9__example_9_5_2"]
theorem exHanoiProgram_moveRelation :
    (exHanoiProgram.outputVarList (show exHanoiLang.withoutEquality from rfl) = [0]) ∧
    (∀ s c, c ∈ exHanoiProgram.prog →
      FOHornClause.evalInHerbrand (show exHanoiLang.withoutEquality from rfl) exHanoiMoveStructure c s) ∧
    (∀ source destination spare n output : GroundTerm exHanoiLang,
      exHanoiMoveStructure.predInterp .move [source, destination, spare, n, output] ↔
        HanoiMoveRelation source.val destination.val spare.val n.val output.val) ∧
    (∀ n output : GroundTerm exHanoiLang,
      exHanoiMoveStructure.predInterp .hanoi [n, output] ↔
        HanoiMoveRelation (hanoiConst .a) (hanoiConst .b) (hanoiConst .c) n.val output.val)

end LCS.SLD.LogicProgramming
end
