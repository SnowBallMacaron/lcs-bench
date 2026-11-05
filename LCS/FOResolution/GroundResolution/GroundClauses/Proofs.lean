import LCS.FOResolution.GroundResolution.GroundClauses

section

namespace LCS.FOResolution.GroundResolution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FOResolution.ClauseForm

open LCS.FirstOrder.SemanticsN

namespace FOClause





end FOClause

end LCS.FOResolution.GroundResolution

end

section

namespace LCS.FOResolution.GroundResolution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FOResolution.ClauseForm

open LCS.FirstOrder.SemanticsN

namespace FOResolutionTree



end FOResolutionTree

end LCS.FOResolution.GroundResolution

end

section

namespace LCS.FOResolution.GroundResolution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FOResolution.ClauseForm

open LCS.FirstOrder.SemanticsN

open LCS.Resolution.GCNF

open LCS.Resolution.Method

open LCS.Resolution.Method.Completeness

open LCS.FirstOrder.SemanticsN

open Classical



















helper /-- Given a first-order structure M and assignment s, construct the
    propositional valuation that agrees with M,s on ground atomic
    formulae via the encoding. -/
noncomputable def propValuation {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L)
    (s : Assignment M)
    (decode : Nat → FOAtom L hNoEq) : Nat → Bool :=
  fun n => if formulaEvalN M (decode n).toFormula s then true else false

helper /-- A positive ground first-order literal is satisfied by M,s iff its
    propositional translation is satisfied by the corresponding valuation. -/
theorem groundLiteral_pos_sat_iff {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (B : FOAtom L hNoEq) :
    FOLiteral.isSatisfied (hNoEq := hNoEq) M s (.pos B) ↔
    Literal.satisfiedBy (groundLiteralToProp (hNoEq := hNoEq) encode (.pos B))
      (propValuation (hNoEq := hNoEq) M s decode) := by
-- BEGIN PROOF
  constructor
  · intro h
    show propValuation (hNoEq := hNoEq) M s decode (encode B) = true
    unfold propValuation
    simp only [hdec B, ite_eq_left_iff, reduceCtorEq]
    exact fun hc => absurd h hc
  · intro h
    show formulaEvalN M B.toFormula s
    have hv : propValuation (hNoEq := hNoEq) M s decode (encode B) = true := h
    unfold propValuation at hv
    simp only [hdec B, ite_eq_left_iff, reduceCtorEq] at hv
    exact Classical.byContradiction hv

helper /-- A negative ground first-order literal is satisfied by M,s iff its
    propositional translation is satisfied by the corresponding valuation. -/
theorem groundLiteral_neg_sat_iff {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (B : FOAtom L hNoEq) :
    FOLiteral.isSatisfied (hNoEq := hNoEq) M s (.neg B) ↔
    Literal.satisfiedBy (groundLiteralToProp (hNoEq := hNoEq) encode (.neg B))
      (propValuation (hNoEq := hNoEq) M s decode) := by
-- BEGIN PROOF
  constructor
  · intro h
    show (propValuation (hNoEq := hNoEq) M s decode) (encode B) = false
    unfold propValuation; rw [hdec]; exact if_neg h
  · intro h
    show ¬ formulaEvalN M B.toFormula s
    have : (propValuation (hNoEq := hNoEq) M s decode) (encode B) = false := h
    unfold propValuation at this; rw [hdec] at this
    intro hc; rw [if_pos hc] at this; exact absurd this (by decide)

helper /-- A ground first-order literal is satisfied iff its propositional
    translation is satisfied by the corresponding valuation. -/
theorem groundLiteral_sat_iff {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (lit : FOLiteral L hNoEq) :
    FOLiteral.isSatisfied (hNoEq := hNoEq) M s lit ↔
    Literal.satisfiedBy (groundLiteralToProp (hNoEq := hNoEq) encode lit)
      (propValuation (hNoEq := hNoEq) M s decode) := by
-- BEGIN PROOF
  cases lit with
  | pos B => exact groundLiteral_pos_sat_iff (hNoEq := hNoEq) M s encode decode hdec B
  | neg B => exact groundLiteral_neg_sat_iff (hNoEq := hNoEq) M s encode decode hdec B

helper /-- If an FO clause is satisfied, its propositional translation is too. -/
theorem groundClause_sat_forward {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (c : FOClause L hNoEq) :
    FOClause.isSatisfied (hNoEq := hNoEq) M s c →
    Clause.satisfiedBy (groundClauseToProp (hNoEq := hNoEq) encode c)
      (propValuation (hNoEq := hNoEq) M s decode) := by
-- BEGIN PROOF
  intro ⟨lit, hlit_mem, hlit_sat⟩
  refine ⟨groundLiteralToProp (hNoEq := hNoEq) encode lit,
          ?_, (groundLiteral_sat_iff (hNoEq := hNoEq) M s encode decode hdec lit).mp hlit_sat⟩
  simp only [groundClauseToProp, Finset.mem_ofList]
  exact List.mem_map.mpr ⟨lit, hlit_mem, rfl⟩

helper /-- If the propositional translation of a clause is satisfied, the
    original FO clause is satisfied. -/
theorem groundClause_sat_backward {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (c : FOClause L hNoEq) :
    Clause.satisfiedBy (groundClauseToProp (hNoEq := hNoEq) encode c)
      (propValuation (hNoEq := hNoEq) M s decode) →
    FOClause.isSatisfied (hNoEq := hNoEq) M s c := by
-- BEGIN PROOF
  intro ⟨plit, hplit_mem, hplit_sat⟩
  simp only [groundClauseToProp, Finset.mem_ofList] at hplit_mem
  obtain ⟨folit, hfolit_mem, hfolit_eq⟩ := List.mem_map.mp hplit_mem
  refine ⟨folit, hfolit_mem, ?_⟩
  rw [← hfolit_eq] at hplit_sat
  exact (groundLiteral_sat_iff (hNoEq := hNoEq) M s encode decode hdec folit).mpr hplit_sat





helper /-- In the Herbrand structure, ground atomic formulas (predN P args
    where all args are ground) evaluate to the truth value assignment. -/
theorem herbrand_predN_eval {L : Language} (hNoEq : L.withoutEquality)
    (truthVal : FOAtom L hNoEq → Prop)
    (s : Assignment (herbrandStructure (hNoEq := hNoEq) truthVal))
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L)
    (hGround : ∀ i, termVars (args i) = Set.empty) :
    formulaEvalN (herbrandStructure (hNoEq := hNoEq) truthVal) (FormulaN.predN P args) s ↔
    truthVal (FOAtomCore.predN P args) := by
-- BEGIN PROOF
  have hEvalArgs : (fun i => termEval (herbrandStructure (hNoEq := hNoEq) truthVal) s (args i)) = args := by
    ext i; exact herbrand_termEval_ground (hNoEq := hNoEq) truthVal s (args i) (hGround i)
  simp only [formulaEvalN]
  show (herbrandStructure (hNoEq := hNoEq) truthVal).interpPred P
    (fun i => termEval (herbrandStructure (hNoEq := hNoEq) truthVal) s (args i)) ↔ _
  rw [hEvalArgs]
  exact Iff.rfl

helper /-- Key bridge lemma: In the Herbrand structure built from truthVal,
    for a ground formula B of the form predN P args (ground args),
    formulaEvalN matches truthVal.

    This is the core connection used by fo_ground_unsat_implies_prop_valid.
    Since ground clause literals (per Definition 8.2.1) wrap predN P args
    with ground arguments, this covers all literals appearing in ground
    clause sets from clause form conversion. -/
theorem herbrand_ground_predN_literal {L : Language} (hNoEq : L.withoutEquality)
    (truthVal : FOAtom L hNoEq → Prop)
    (s : Assignment (herbrandStructure (hNoEq := hNoEq) truthVal))
    (B : FOAtom L hNoEq)
    (hPredN : ∃ (P : L.predSymbols) (args : Fin (L.predArity P) → Term L),
      B = FOAtomCore.predN P args ∧ ∀ i, termVars (args i) = Set.empty) :
    formulaEvalN (herbrandStructure (hNoEq := hNoEq) truthVal) B.toFormula s ↔ truthVal B := by
-- BEGIN PROOF
  obtain ⟨P, args, rfl, hArgsGround⟩ := hPredN
  exact herbrand_predN_eval (hNoEq := hNoEq) truthVal s P args hArgsGround

end LCS.FOResolution.GroundResolution

end
