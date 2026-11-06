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

/-- The disjunction of the open query matrices, before existential closure.
    Each conjunction and the disjunction itself have positive size (SQ31–SQ32). -/
@[blueprint "chap9__definition_9_5_3"]
def LogicProgram.queryMatrix {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : FormulaN L :=
  lp.qry.tail.foldl (fun f a => .disj f a.matrix) (lp.qry.head lp.wellFormed.1).matrix

/-- The complete set of universal Horn matrices P together with the
    Horn dual of every query component (SQ25, SQ30–SQ31). -/
@[blueprint "chap9__lemma_9_5_2"]
def queryHornTranslation {L : Language} {hNoEq : L.withoutEquality}
    (lp : LogicProgram L hNoEq) : Set (FOHornClause L hNoEq) :=
  fun c => c ∈ lp.prog ∨ c ∈ lp.qry.map AntiHornClause.negatedClause

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
