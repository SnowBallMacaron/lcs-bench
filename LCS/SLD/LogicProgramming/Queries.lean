import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Queries.ProofsStamp

/-! # Queries and answers (§9.5.1–9.5.2)

Arbitrary atomic answers, refutation translations, common free models, and
finite disjunctive answers. Program clauses are universally interpreted,
and substitutions act on open matrices (SQ25, SQ30–SQ35).
-/

noncomputable section
namespace LCS.SLD.LogicProgramming

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm LCS.FOResolution.Unification
open LCS.SLD.FirstOrder

/-- Truth of a Horn matrix at one assignment, including the empty goal. -/
@[blueprint "chap9__definition_9_5_1"]
def hornMatrixTruth {L : Language} {hNoEq : L.withoutEquality}
    (M : Structure L) (s : Assignment M) : FOHornClause L hNoEq → Prop
  | FOHornClauseCore.fact a => formulaEvalN M a.toFormula s
  | FOHornClauseCore.rule a bs => (∀ b ∈ bs, formulaEvalN M b.toFormula s) → formulaEvalN M a.toFormula s
  | FOHornClauseCore.goal bs => ¬ (∀ b ∈ bs, formulaEvalN M b.toFormula s)

/-- One structure satisfies every universally closed clause of arbitrary P (SQ30). -/
@[blueprint "chap9__definition_9_5_1"]
def hornProgramModels {L : Language} {hNoEq : L.withoutEquality}
    (P : Set (FOHornClause L hNoEq)) (M : Structure L) : Prop :=
  ∀ s c, c ∈ P → hornMatrixTruth M s c

/-- Consequence in all ordinary structures and all assignments (R-SEM). -/
@[blueprint "chap9__definition_9_5_1"]
def programConsequence {L : Language} {hNoEq : L.withoutEquality}
    (P : Set (FOHornClause L hNoEq)) (G : FormulaN L) : Prop :=
  ∀ M : Structure L, hornProgramModels P M → ∀ s, formulaEvalN M G s

/-- The coordinate list enumerates exactly the open formula's free variables. -/
@[blueprint "chap9__definition_9_5_1"]
def exactQueryVariables {L : Language} (G : FormulaN L) (zs : List Nat) : Prop :=
  zs.Nodup ∧ ∀ v, v ∈ zs ↔ formulaFVN G v

/-- Simultaneous finite substitution; terms may themselves contain variables.
    The support witness is the coordinate list (OD-7-2/SQ038). -/
noncomputable def finiteAnswerSubstitution {L : Language} (zs : List Nat)
    (ts : Fin zs.length → Term L) : FiniteSubstitution L := by
  classical
  exact {
    support := zs
    map := fun v => if h : ∃ i : Fin zs.length, zs.get i = v
      then ts (Classical.choose h) else .var v
    outsideSupport := by
      intro v hv
      have hn : ¬ ∃ i : Fin zs.length, zs.get i = v := by
        rintro ⟨i, hi⟩
        exact hv (hi ▸ List.get_mem zs i)
      exact dite_eq_right hn }

/-- The map of the finite simultaneous answer substitution. -/
@[blueprint "chap9__definition_9_5_1"]
noncomputable def answerSubstitution {L : Language} (zs : List Nat)
    (ts : Fin zs.length → Term L) : Nat → Term L :=
  (finiteAnswerSubstitution zs ts).map

/-- An arbitrary term-vector answer to the open positive atomic query.
    The vector has exactly one term per actual free variable; no groundness
    or refutation-generation restriction is imposed (§9.5.1, SQ30–SQ31). -/
@[blueprint "chap9__definition_9_5_1"]
def AtomicQueryAnswer {L : Language} (hNoEq : L.withoutEquality)
    (P : Set (FOHornClause L hNoEq))
    (_hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : FOAtom L hNoEq) (zs : List Nat)
    (_hVars : exactQueryVariables G.toFormula zs)
    (ts : Fin zs.length → Term L) : Prop :=
  programConsequence P (formulaSubstAll G.toFormula (answerSubstitution zs ts))

/-- Logical success: each model of P has values for the query variables.
    Values may depend on the model; this is distinct from fixing one answer. -/
@[blueprint "chap9__definition_9_5_1"]
def atomicQuerySuccess {L : Language} (hNoEq : L.withoutEquality)
    (P : Set (FOHornClause L hNoEq))
    (_hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : FOAtom L hNoEq) (zs : List Nat)
    (_hVars : exactQueryVariables G.toFormula zs) : Prop :=
  ∀ M : Structure L, hornProgramModels P M → ∀ s : Assignment M,
    ∃ s' : Assignment M, (∀ v, v ∉ zs → s' v = s v) ∧ formulaEvalN M G.toFormula s'

/-- Logical success is precisely P ⊨ ∃zs G in all structures (§9.5.1). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem atomicQuerySuccess_iff_existentialConsequence {L : Language}
    (hNoEq : L.withoutEquality) (P : Set (FOHornClause L hNoEq))
    (hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : FOAtom L hNoEq) (zs : List Nat) (hVars : exactQueryVariables G.toFormula zs) :
    atomicQuerySuccess hNoEq P hDef G zs hVars ↔
      programConsequence P (zs.foldr FormulaN.ex G.toFormula)

/-- The full Horn translation of P and the negated atomic query. -/
@[blueprint "chap9__definition_9_5_1"]
def atomicHornTranslation {L : Language} {hNoEq : L.withoutEquality}
    (P : Set (FOHornClause L hNoEq)) (G : FOAtom L hNoEq) : Set (FOHornClause L hNoEq) :=
  fun c => c ∈ P ∨ c = FOHornClause.goal (hNoEq := hNoEq) (LCS.Finset.singleton G)

/-- The set-consequence form of validity iff negated implication is unsatisfiable
    (§9.5.1, arbitrary P under SQ30). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem query_valid_iff_negation_unsatisfiable {L : Language}
    (hNoEq : L.withoutEquality) (P : Set (FOHornClause L hNoEq))
    (_hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : FOAtom L hNoEq) (zs : List Nat) (_hVars : exactQueryVariables G.toFormula zs) :
    programConsequence P (zs.foldr FormulaN.ex G.toFormula) ↔
      ¬ ∃ (M : Structure L) (s : Assignment M), hornProgramModels P M ∧
        formulaEvalN M (.neg (zs.foldr FormulaN.ex G.toFormula)) s

/-- The second iff and the complete Horn-family interpretation use the same
    P, G and exact variable vector. Universal closure is semantic (SQ25, SQ30). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem query_refutation_iff_hornTranslation {L : Language}
    (hNoEq : L.withoutEquality) (P : Set (FOHornClause L hNoEq))
    (_hDef : ∀ c ∈ P, FOHornClause.isDefinite hNoEq c)
    (G : FOAtom L hNoEq) (zs : List Nat) (_hVars : exactQueryVariables G.toFormula zs) :
    ((¬ ∃ (M : Structure L) (s : Assignment M), hornProgramModels P M ∧
        formulaEvalN M (.neg (zs.foldr FormulaN.ex G.toFormula)) s) ↔
      ¬ ∃ M : Structure L, hornProgramModels (atomicHornTranslation P G) M) ∧
    (∀ M : Structure L, hornProgramModels (atomicHornTranslation P G) M ↔
      hornProgramModels P M ∧
        ∀ s, formulaEvalN M (zs.foldr FormulaN.all (.neg G.toFormula)) s)

/-- Lemma 9.5.1 for arbitrary theories: a single common ordinary model
    exists iff a single free model satisfies every member (SQ33–SQ34). -/
@[attach_debt, blueprint "chap9__lemma_9_5_1"]
theorem universalTheory_freeModel_iff {L : Language} (hNoEq : L.withoutEquality)
    (_hConst : Nonempty L.constSymbols) (S : Set (FormulaN L))
    (_hSentences : ∀ X ∈ S, FormulaN.isClosed X)
    (_hNNF : ∀ X ∈ S, formulaIsNNF X)
    (_hUniversal : ∀ X ∈ S, formulaUniversalOnly X) :
    (∃ M : Structure L, ∀ X ∈ S, ∀ s, formulaEvalN M X s) ↔
      ∃ H : HerbrandStructure L hNoEq, ∀ X ∈ S, ∀ s, evalFormulaInHerbrand H s X

/-- The same universal-NNF theory has no ordinary model iff it has no
    free model; the ambient equality-free language has a constant (SQ33–SQ34). -/
@[attach_debt, blueprint "chap9__lemma_9_5_1"]
theorem universalTheory_freeUnsatisfiable_iff {L : Language} (hNoEq : L.withoutEquality)
    (_hConst : Nonempty L.constSymbols) (S : Set (FormulaN L))
    (_hSentences : ∀ X ∈ S, FormulaN.isClosed X)
    (_hNNF : ∀ X ∈ S, formulaIsNNF X)
    (_hUniversal : ∀ X ∈ S, formulaUniversalOnly X) :
    (¬ ∃ M : Structure L, ∀ X ∈ S, ∀ s, formulaEvalN M X s) ↔
      ¬ ∃ H : HerbrandStructure L hNoEq, ∀ X ∈ S, ∀ s, evalFormulaInHerbrand H s X

/-- The disjunction of the open query matrices, before existential closure.
    Each conjunction and the disjunction itself have positive size (SQ31–SQ32). -/
@[blueprint "chap9__definition_9_5_3"]
def LogicProgram.queryMatrix {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : FormulaN L :=
  lp.qry.tail.foldl (fun f a => .disj f a.matrix) (lp.qry.head lp.wellFormed.1).matrix

/-- The general closed-query test agrees in ordinary and free structures. -/
@[attach_debt, blueprint "chap9__definition_9_5_3"]
theorem queryValid_iff_consequence {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) (hConst : Nonempty L.constSymbols) :
    queryValid hNoEq lp hConst ↔ programConsequence lp.prog lp.toSentence

/-- A singleton ground answer is exactly validity of its instance of the
    full query matrix, with one coordinate per output variable (SQ30–SQ35).
    Empty output lists are allowed; positive conjunction size is inherited
    from the anti-Horn components. -/
@[attach_debt, blueprint "chap9__definition_9_5_3"]
theorem groundQueryAnswer_iff_singletonValidity {L : Language}
    (hNoEq : L.withoutEquality) (lp : LogicProgram L hNoEq)
    (hConst : Nonempty L.constSymbols)
    (t : GroundAnswerTuple L (lp.outputVarList hNoEq).length) :
    groundAnswerValid hNoEq lp hConst t ↔
      programConsequence lp.prog (formulaSubstAll lp.queryMatrix
        (answerSubstitution (lp.outputVarList hNoEq) (fun i => (t i).val)))

/-- The complete set of universal Horn matrices P together with the
    Horn dual of every query component (SQ25, SQ30–SQ31). -/
@[blueprint "chap9__lemma_9_5_2"]
def queryHornTranslation {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : Set (FOHornClause L hNoEq) :=
  fun c => c ∈ lp.prog ∨ c ∈ lp.qry.map AntiHornClause.negatedClause

/-- A Horn matrix as a formula. The empty clause is the contradictory
    expansion A ∧ ¬A required by the logical grammar (R-CONN). -/
@[blueprint "chap9__lemma_9_5_2"]
def hornMatrixFormula {L : Language} {hNoEq : L.withoutEquality}
    (A : FormulaN L) (c : FOHornClause L hNoEq) : FormulaN L :=
  LCS.FOResolution.Method.Soundness.clauseToFormula hNoEq A (c.toFOClause hNoEq)

/-- The complete variable list for the finite used program and all query
    matrices. Output variables remain coordinates even when q = 0 (SQ31). -/
@[blueprint "chap9__lemma_9_5_2"]
def completeQueryTheoryVariables {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) (D : List (FOHornClause L hNoEq)) (xs : List Nat) : Prop :=
  xs.Nodup ∧ ∀ v, v ∈ xs ↔
    lp.outputVars hNoEq v ∨
      ∃ c ∈ D ++ lp.qry.map AntiHornClause.negatedClause,
        formulaFVN (hornMatrixFormula lp.queryMatrix c) v

/-- The validity/refutation equivalences and a single nonempty finite ground
    family. Both conclusions reuse its coordinates and the same Horn matrices.
    The finite subtheory D is extracted from arbitrary P (SQ30); every instance
    substitutes into matrices, not closed sentences (SQ25, SQ31). -/
@[attach_debt, blueprint "chap9__lemma_9_5_2"]
theorem finiteDisjunctiveAnswer_witnesses {L : Language} (hNoEq : L.withoutEquality)
    (hConst : Nonempty L.constSymbols) (lp : LogicProgram L hNoEq) :
    (programConsequence lp.prog lp.toSentence ↔
      ¬ ∃ (M : Structure L) (s : Assignment M), hornProgramModels lp.prog M ∧
        formulaEvalN M (.neg lp.toSentence) s) ∧
    ((¬ ∃ (M : Structure L) (s : Assignment M), hornProgramModels lp.prog M ∧
        formulaEvalN M (.neg lp.toSentence) s) ↔
      ¬ ∃ M : Structure L, hornProgramModels (queryHornTranslation lp) M) ∧
    (∀ M : Structure L, hornProgramModels (queryHornTranslation lp) M ↔
      hornProgramModels lp.prog M ∧ ∀ s, formulaEvalN M lp.negationSentence s) ∧
    (programConsequence lp.prog lp.toSentence ↔
      ∃ (D : List (FOHornClause L hNoEq)) (xs : List Nat)
        (family : DisjunctiveAnswer L xs.length),
        (∀ c ∈ D, c ∈ lp.prog) ∧ completeQueryTheoryVariables lp D xs ∧
        programConsequence (fun c => c ∈ D) lp.toSentence ∧
        (¬ ∃ (M : Structure L) (s : Assignment M),
          ∀ tuple ∈ family.val, ∀ c ∈ D ++ lp.qry.map AntiHornClause.negatedClause,
            formulaEvalN M
              (formulaSubstAll (hornMatrixFormula lp.queryMatrix c)
                (answerSubstitution xs (fun i => (tuple i).val))) s) ∧
        (∀ M : Structure L, hornProgramModels lp.prog M → ∀ s,
          ∃ tuple ∈ family.val, formulaEvalN M
            (formulaSubstAll lp.queryMatrix
              (answerSubstitution xs (fun i => (tuple i).val))) s))

/-- Fixed equality-free signature for the independent negative-premise
    schema: rank-zero A, B and side atoms, plus one constant (SQ43). -/
@[blueprint "chap9__definition_9_5_1"]
def negativePremiseLanguage : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Unit
  predSymbols := Nat
  predArity := fun _ => 0
  hasEquality := false

/-- Independent closed atoms: 0 is A, 1 is B, and 2+j is a side premise. -/
@[blueprint "chap9__definition_9_5_1"]
def negativePremiseAtom (p : Nat) : FormulaN negativePremiseLanguage :=
  .predN p (fun i => Fin.elim0 i)

/-- The closed rule B :- A₁,…,Aᵢ₋₁,¬A,Aᵢ₊₁,…,Aₙ over independent
    rank-zero predicates. Either side list may be empty; with both empty
    the formula is ¬A ⇒ B, equivalently A ∨ B (SQ43). -/
@[blueprint "chap9__definition_9_5_1"]
def negativePremiseSchema (before after : Nat) : FormulaN negativePremiseLanguage :=
  .impl
    ((List.range before).foldr (fun j f => .conj (negativePremiseAtom (2 + j)) f)
      ((List.range after).foldl (fun f j => .conj f (negativePremiseAtom (2 + before + j)))
        (.neg (negativePremiseAtom 0))))
    (negativePremiseAtom 1)

/-- A one-element structure realizes any valuation of the independent atoms. -/
@[blueprint "chap9__definition_9_5_1"]
def negativePremiseModel (v : Nat → Prop) : Structure negativePremiseLanguage where
  carrier := Unit
  carrierNonempty := ⟨()⟩
  interpFunc := fun f => Empty.elim f
  interpConst := fun _ => ()
  interpPred := fun p _ => v p

/-- All side premises true, A-only and B-only are models, whereas their
    intersection is not. This is the Horn-model intersection obstruction
    of Problem 3.5.9 used in §9.5.5 (SQ43). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem negativePremise_intersectionObstruction (before after : Nat) :
    (∀ s, formulaEvalN (negativePremiseModel (fun p => p ≠ 1))
      (negativePremiseSchema before after) s) ∧
    (∀ s, formulaEvalN (negativePremiseModel (fun p => p ≠ 0))
      (negativePremiseSchema before after) s) ∧
    (∀ s, ¬ formulaEvalN (negativePremiseModel (fun p => p ≠ 1 ∧ p ≠ 0))
      (negativePremiseSchema before after) s)

/-- No finite conjunction of universally closed Horn clauses over this
    same signature is equivalent to the independent negative-premise schema.
    Distinct A and B are fixed by the signature (SQ43). -/
@[attach_debt, blueprint "chap9__definition_9_5_1"]
theorem negativePremise_not_finiteHornEquivalent (before after : Nat) :
    ∀ D : List (FOHornClause negativePremiseLanguage rfl),
      ¬ ∀ M : Structure negativePremiseLanguage,
        (∀ s, formulaEvalN M (negativePremiseSchema before after) s) ↔
          hornProgramModels (fun c => c ∈ D) M

end LCS.SLD.LogicProgramming
end
