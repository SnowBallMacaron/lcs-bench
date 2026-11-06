import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.Midsequents

Theorem 7.4.1: midsequents of G2nnf proofs and the quantifier part below them, with
the sequent, midsequent and end sequent of Example 7.4.4.
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

-- ===================================================================
-- Theorem 7.4.1 (helper): AllRulesPropOrWeakening
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Predicate asserting that every rule applied in a G2nnf proof tree is either propositional or a weakening (not a quantifier rule). Used for the upper part of the midsequent splitting. -/
@[blueprint "chap7__theorem_7_4_1"]
def AllRulesPropOrWeakening {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    (rule.isPropositionalRule ∨ rule.isWeakening) ∧
    AllRulesPropOrWeakening (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (rule.isPropositionalRule ∨ rule.isWeakening) ∧
    AllRulesPropOrWeakening (hL := hL) sub1 ∧
    AllRulesPropOrWeakening (hL := hL) sub2

-- ===================================================================
-- Theorem 7.4.1 (helper): AllRulesQuantifier
-- ===================================================================

-- ===================================================================
-- Theorem 7.4.1 (helper): occurrence-indexed lower paths
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Every inference strictly below the
target occurrence selected by `path` is a quantifier-for-subformulae
inference.  The target node's own inference belongs to the upper subtree and
is therefore not inspected here. -/
@[blueprint "chap7__theorem_7_4_1"]
def AllRulesQuantifierOnPath {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath
  | .leftPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath
  | .rightPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath subpath

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A quantifier-only path from an empty-succedent root reaches a node with
empty succedent.  Left quantifier rules preserve the succedent, while right
quantifier rules cannot have an empty conclusion succedent. -/
theorem _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree.succedent_eq_empty_of_quantifierPath
    {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hRoot : Δroot = LCS.Finset.empty) :
    Δnode = LCS.Finset.empty := by
  induction path with
  | root _ =>
    exact hRoot
  | onePremise rule hAdmit hPrem hSC sub path ih =>
    rcases hQuantifier with ⟨hRule, hPath⟩
    cases rule <;>
      simp only [G2nnfRuleCore.isQuantifierRule] at hRule
    · exact ih hPath hRoot
    · rename_i A occurrence x B y hSelected Gamma Delta
      change LCS.Finset.insert A Delta = LCS.Finset.empty at hRoot
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRoot] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
    · exact ih hPath hRoot
    · rename_i A occurrence x B t hSelected Gamma Delta
      change LCS.Finset.insert A Delta = LCS.Finset.empty at hRoot
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRoot] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule, G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule, G2nnfRuleCore.premises] at hRule hPrem

/-- A prenex formula whose quantifier prefix is entirely universal.  This
Chapter-7 predicate avoids importing the Chapter-8 clause-form API. -/
@[blueprint "chap7__theorem_7_6_1"]
def UniversalPrenexFormula {L : Language} (A : FormulaN L) : Prop :=
  isPrenex A ∧
  ∀ p, p ∈ prenexPrefix A →
    p.1 = QuantifierKind.universal

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- The selected lower path consists only of universal-left
quantifier-for-subformulae steps. -/
def AllRulesAllSubLeftOnPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    match rule with
    | .allSubLeft _ _ _ _ _ _ _ _ =>
      AllRulesAllSubLeftOnPath subpath
    | _ => False
  | .leftPremise _ _ _ _ _ _ _ => False
  | .rightPremise _ _ _ _ _ _ _ => False

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves quantifier-freeness. -/
theorem qf_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree (formulaSubstN A t x) := by
  induction A <;>
    simp_all [formulaSubstN,
      FirstOrder.SemanticsN.isQuantifierFree]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution does not change a prenex formula's quantifier prefix. -/
theorem prenexPrefix_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    prenexPrefix (formulaSubstN A t x) = prenexPrefix A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ _ _ => rfl
  | disj _ _ _ _ => rfl
  | impl _ _ _ _ => rfl
  | all y A ih =>
    by_cases hxy : x = y <;>
      simp [formulaSubstN, hxy, prenexPrefix, ih]
  | ex y A ih =>
    by_cases hxy : x = y <;>
      simp [formulaSubstN, hxy, prenexPrefix, ih]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves prenex form. -/
theorem isPrenex_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hPrenex : isPrenex A) :
    isPrenex (formulaSubstN A t x) := by
  cases A with
  | all y A =>
    change isPrenex A at hPrenex
    by_cases hxy : x = y
    · simpa [formulaSubstN, hxy, isPrenex] using hPrenex
    · simpa [formulaSubstN, hxy, isPrenex] using
        isPrenex_formulaSubstN A t x hPrenex
  | ex y A =>
    change isPrenex A at hPrenex
    by_cases hxy : x = y
    · simpa [formulaSubstN, hxy, isPrenex] using hPrenex
    · simpa [formulaSubstN, hxy, isPrenex] using
        isPrenex_formulaSubstN A t x hPrenex
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact qf_formulaSubstN _ _ _ hPrenex

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A quantifier-free formula has no maximal quantified subformula. -/
theorem not_mem_maxQuantSubformulae_of_qf {L : Language}
    (A C : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    ¬ Membership.mem (maxQuantSubformulaeCore A) C := by
  induction A with
  | predN _ _ | eq_ _ _ _ | neg _ _ | impl _ _ _ _ =>
    exact id
  | conj A B ihA ihB | disj A B ihA ihB =>
    intro hMem
    rcases hMem with hMem | hMem
    · exact ihA hQF.1 hMem
    · exact ihB hQF.2 hMem
  | all _ _ | ex _ _ =>
    exact hQF.elim

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A maximal quantified subformula of a prenex formula is the whole
formula. -/
theorem eq_of_mem_maxQuantSubformulae_of_isPrenex {L : Language}
    (A C : FormulaN L)
    (hPrenex : isPrenex A)
    (hMem : Membership.mem (maxQuantSubformulaeCore A) C) :
    C = A := by
  cases A with
  | all _ _ => exact hMem
  | ex _ _ => exact hMem
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact (not_mem_maxQuantSubformulae_of_qf _ _ hPrenex hMem).elim

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution preserves the universal-prenex invariant. -/
theorem universalPrenexFormula_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hUniversal : UniversalPrenexFormula A) :
    UniversalPrenexFormula (formulaSubstN A t x) := by
  refine ⟨isPrenex_formulaSubstN A t x hUniversal.1, ?_⟩
  intro p hp
  apply hUniversal.2 p
  rw [← prenexPrefix_formulaSubstN A t x]
  exact hp

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Removing one leading universal quantifier preserves the
universal-prenex invariant. -/
theorem universalPrenexFormula_body_of_all {L : Language}
    (B : FormulaN L) (x : Nat)
    (hUniversal :
      UniversalPrenexFormula (FormulaN.all x B)) :
    UniversalPrenexFormula B := by
  refine ⟨hUniversal.1, ?_⟩
  intro p hp
  exact hUniversal.2 p (List.mem_cons.mpr (Or.inr hp))

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- The principal premise formula of a universal-left
quantifier-for-subformulae step remains universal-prenex. -/
theorem universalPrenexFormula_allSubLeft_premise
    {L : Language} [DecidableEq (FormulaN L)]
    (A B : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hUniversal : UniversalPrenexFormula A)
    (hSelected : occurrence.selected = FormulaN.all x B) :
    UniversalPrenexFormula
      (occurrence.replace (formulaSubstN B t x)) := by
  have hSelectedA :=
    eq_of_mem_maxQuantSubformulae_of_isPrenex
      A occurrence.selected hUniversal.1 occurrence.selected_mem
  have hA : A = FormulaN.all x B :=
    hSelectedA.symm.trans hSelected
  subst A
  cases occurrence
  simp only [MaxQuantifierOccurrence.replace]
  exact universalPrenexFormula_formulaSubstN B t x
    (universalPrenexFormula_body_of_all B x hUniversal)

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- An empty-succedent quantifier path starting from a
universal-prenex antecedent can contain only universal-left steps, and
every antecedent formula at its target remains universal-prenex. -/
theorem allSubLeftOnPath_and_universalPrenexAntecedent
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hRootSuccedent : Δroot = LCS.Finset.empty)
    (hRootAntecedent :
      ∀ A, A ∈ Γroot → UniversalPrenexFormula A) :
    AllRulesAllSubLeftOnPath path ∧
    ∀ A, A ∈ Γnode → UniversalPrenexFormula A := by
  induction path with
  | root _ =>
    exact ⟨trivial, hRootAntecedent⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
    rcases hQuantifier with ⟨hRule, hPath⟩
    cases rule <;>
      simp only [G2nnfRuleCore.isQuantifierRule] at hRule
    · rename_i A occurrence x B t hSelected Gamma Delta
      change Delta = LCS.Finset.empty at hRootSuccedent
      change
        (∀ F, F ∈ LCS.Finset.insert A Gamma →
          UniversalPrenexFormula F)
        at hRootAntecedent
      have hUniversalA : UniversalPrenexFormula A :=
        hRootAntecedent A
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hPremiseAntecedent :
          ∀ F,
            F ∈ LCS.Finset.insert
              (occurrence.replace
                (formulaSubstN B t x)) Gamma →
            UniversalPrenexFormula F := by
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with hPrincipal | hRetained
        · subst F
          exact universalPrenexFormula_allSubLeft_premise
            A B occurrence x t hUniversalA hSelected
        · exact hRootAntecedent F
            (LCS.Finset.mem_insert.mpr (Or.inr hRetained))
      exact ih hPath hRootSuccedent hPremiseAntecedent
    · rename_i A occurrence x B y hSelected Gamma Delta
      change LCS.Finset.insert A Delta =
        LCS.Finset.empty at hRootSuccedent
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRootSuccedent] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
    · rename_i A occurrence x B y hSelected Gamma Delta
      change
        (∀ F, F ∈ LCS.Finset.insert A Gamma →
          UniversalPrenexFormula F)
        at hRootAntecedent
      have hUniversalA : UniversalPrenexFormula A :=
        hRootAntecedent A
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hSelectedA : occurrence.selected = A :=
        eq_of_mem_maxQuantSubformulae_of_isPrenex
          A occurrence.selected hUniversalA.1 occurrence.selected_mem
      have hA : A = FormulaN.ex x B :=
        hSelectedA.symm.trans hSelected
      have hExistential :
          (QuantifierKind.existential, x) ∈ prenexPrefix A := by
        rw [hA]
        exact List.Mem.head _
      have hKind :=
        hUniversalA.2 (QuantifierKind.existential, x) hExistential
      cases hKind
    · rename_i A occurrence x B t hSelected Gamma Delta
      change LCS.Finset.insert A Delta =
        LCS.Finset.empty at hRootSuccedent
      have hA : Membership.mem (LCS.Finset.insert A Delta) A :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      rw [hRootSuccedent] at hA
      exact (LCS.Finset.not_mem_empty hA).elim
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule,
        G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
    rcases hQuantifier with ⟨hRule, _⟩
    cases rule <;>
      simp [G2nnfRuleCore.isQuantifierRule,
        G2nnfRuleCore.premises] at hRule hPrem

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- Specialization of the lower-path invariant to a singleton
universal-prenex antecedent and empty succedent. -/
theorem singletonUniversalPrenex_quantifierPath
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    {Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      (LCS.Finset.singleton source) LCS.Finset.empty}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path) :
    Δnode = LCS.Finset.empty ∧
    AllRulesAllSubLeftOnPath path ∧
    ∀ A, A ∈ Γnode → UniversalPrenexFormula A := by
  have hRootAntecedent :
      ∀ A, A ∈ LCS.Finset.singleton source →
        UniversalPrenexFormula A := by
    intro A hA
    rw [LCS.Finset.mem_singleton] at hA
    subst A
    exact hSource
  have hPath :=
    allSubLeftOnPath_and_universalPrenexAntecedent path
      hQuantifier rfl hRootAntecedent
  exact
    ⟨G2nnfProofTree.succedent_eq_empty_of_quantifierPath
        path hQuantifier rfl,
      hPath⟩

-- ===================================================================
-- Theorem 7.4.1 (companion structure): IsMidsequentG2nnf
-- ===================================================================

/-- Theorem 7.4.1 (companion structure): A sequent `mid` is the midsequent
of `T` when it is quantifier-free and there is one occurrence-identified node
whose upper subtree contains only propositional/weakening inferences and whose
root-to-node path contains only quantifier-for-subformulae inferences.  The
single `NodeOccurrence` witness prevents equal sequents at different nodes
from supplying the upper and lower conditions independently. -/
@[blueprint "chap7__theorem_7_4_1"]
structure IsMidsequentG2nnf {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop where
  /-- Every formula in the midsequent antecedent and succedent is
      quantifier-free -/
  midIsQuantifierFree :
    (∀ A, Membership.mem mid.1 A →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, Membership.mem mid.2 A →
      FirstOrder.SemanticsN.isQuantifierFree A)
  /-- One occurrence supplies the target subtree, its exact position in `T`,
      the upper-rule condition, and the lower-path condition together. -/
  midOccurrence :
    ∃ occurrence : NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening (hL := hL) occurrence.node ∧
      AllRulesQuantifierOnPath occurrence.path

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- A genuine midsequent occurrence below a singleton
universal-prenex antecedent has empty succedent, and the same occurrence
carries the upper-tree and universal-left lower-path invariants. -/
theorem universalPrenexSingleton_midsequentSpecialization
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    {T : G2nnfProofTree hL
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ occurrence : NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening (hL := hL) occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      ∀ A, A ∈ mid.1 → UniversalPrenexFormula A := by
  rcases hMid.midOccurrence with
    ⟨occurrence, hAbove, hQuantifier⟩
  rcases singletonUniversalPrenex_quantifierPath source hSource
      occurrence.path hQuantifier with
    ⟨hSuccedent, hAllSubLeft, hAntecedent⟩
  exact
    ⟨hSuccedent,
      ⟨occurrence, hAbove, hAllSubLeft, hAntecedent⟩⟩

-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExPred
-- ===================================================================

/-- Example 7.4.4 (companion type): Predicate symbols for the NNF sharpened Hauptsatz example: P (unary), Q (unary), R (unary). These predicates are used to construct the sequent (P(a) or forall x(Q(x) or forall y R(y))) -> P(a), Q(a), R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExPred : Type where
  /-- Unary predicate P -/
  | P : NNFHauptExPred
  /-- Unary predicate Q -/
  | Q : NNFHauptExPred
  /-- Unary predicate R -/
  | R : NNFHauptExPred

-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExFunc
-- ===================================================================

/-- Example 7.4.4 (companion type): Function symbols for the NNF sharpened Hauptsatz example: f (unary). The function f is used in the terms f(a) and f(b) appearing in the succedent. -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExFunc : Type where
  /-- Unary function f -/
  | f : NNFHauptExFunc

-- ===================================================================
-- Example 7.4.4 (companion type): NNFHauptExConst
-- ===================================================================

/-- Example 7.4.4 (companion type): Constant symbols for the NNF sharpened Hauptsatz example: a and b. The constants a and b appear in the ground terms P(a), Q(a), f(a), and f(b). -/
@[blueprint "chap7__example_7_4_4"]
inductive NNFHauptExConst : Type where
  /-- Constant a -/
  | a : NNFHauptExConst
  /-- Constant b -/
  | b : NNFHauptExConst

-- ===================================================================
-- Example 7.4.4 (companion def): nnfHauptExLang
-- ===================================================================

/-- Example 7.4.4 (companion def): A language with unary predicates P, Q, R; unary function f; and constants a, b. This language is used to construct the sequent and proof trees for the NNF sharpened Hauptsatz example. -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptExLang : Language where
  hasEquality := false
  funSymbols := NNFHauptExFunc
  funArity := fun | .f => 1
  constSymbols := NNFHauptExConst
  predSymbols := NNFHauptExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 1

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptExVec1
-- ===================================================================

/-- Example 7.4.4 (companion def): Build a Fin 1 -> Term from a single term in nnfHauptExLang. Used to construct unary predicate applications P(t), Q(t), R(t). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptExVec1 (t : Term nnfHauptExLang) :
    Fin 1 → Term nnfHauptExLang
  | ⟨0, _⟩ => t

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptEx_fa
-- ===================================================================

/-- Example 7.4.4 (companion def): The term f(a) used in the succedent
formulae R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_fa : Term nnfHauptExLang :=
  Term.func NNFHauptExFunc.f
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

-- ===================================================================
-- Example 7.4.4 (helper): nnfHauptEx_fb
-- ===================================================================

/-- Example 7.4.4 (companion def): The term f(b) used in the succedent
formula R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_fb : Term nnfHauptExLang :=
  Term.func NNFHauptExFunc.f
    (nnfHauptExVec1 (Term.const NNFHauptExConst.b))

-- ===================================================================
-- Example 7.4.4 (helper): formula abbreviations
-- ===================================================================

/-- Example 7.4.4 (companion abbrev): P(a) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Pa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.P
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

/-- Example 7.4.4 (companion abbrev): Q(a) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Qa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.Q
    (nnfHauptExVec1 (Term.const NNFHauptExConst.a))

/-- Example 7.4.4 (companion abbrev): R(f(a)) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Rfa : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 nnfHauptEx_fa)

/-- Example 7.4.4 (companion abbrev): R(f(b)) in the example language. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_Rfb : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 nnfHauptEx_fb)

/-- Example 7.4.4 (companion abbrev): R(f(a)) and R(f(b)). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_RfaAndRfb : FormulaN nnfHauptExLang :=
  FormulaN.conj nnfHauptEx_Rfa nnfHauptEx_Rfb

/-- Example 7.4.4 (companion abbrev): forall y R(y) (y = 1). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_forallYRy : FormulaN nnfHauptExLang :=
  FormulaN.all 1
    (FormulaN.predN NNFHauptExPred.R
      (nnfHauptExVec1 (Term.var 1)))

/-- Example 7.4.4 (companion abbrev): Q(x) or forall y R(y) (x = 0). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_QxOrForallYRy :
    FormulaN nnfHauptExLang :=
  FormulaN.disj
    (FormulaN.predN NNFHauptExPred.Q
      (nnfHauptExVec1 (Term.var 0)))
    nnfHauptEx_forallYRy

/-- Example 7.4.4 (companion abbrev): forall x(Q(x) or forall y R(y)) (x=0).
The maximal quantified subformula of the antecedent formula. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_forallXBody : FormulaN nnfHauptExLang :=
  FormulaN.all 0 nnfHauptEx_QxOrForallYRy

/-- Example 7.4.4 (companion abbrev): The antecedent formula
P(a) or forall x(Q(x) or forall y R(y)). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_antFormula : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa nnfHauptEx_forallXBody

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or R(f(a))).
An antecedent formula of the midsequent. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_midAnt1 : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfa)

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or R(f(b))).
An antecedent formula of the midsequent. -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_midAnt2 : FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfb)

/-- Example 7.4.4 (companion abbrev): P(a) or (Q(a) or forall y R(y)). Intermediate formula after first allSubLeft instantiation (x := a). -/
@[blueprint "chap7__example_7_4_4"]
abbrev nnfHauptEx_afterFirstInst :
    FormulaN nnfHauptExLang :=
  FormulaN.disj nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_forallYRy)

-- ===================================================================
-- Example 7.4.4 (helper): succedent set
-- ===================================================================

@[blueprint "chap7__example_7_4_4"]
abbrev NNFHauptExFormula := FormulaN nnfHauptExLang

@[blueprint "chap7__example_7_4_4"]
abbrev NNFHauptExFormulaSet :=
  LCS.Finset NNFHauptExFormula

-- ATTACH-BLOCKER: unsupported untagged abbrev
noncomputable abbrev nnfHauptExDeltaBase : NNFHauptExFormulaSet :=
  LCS.Finset.insert nnfHauptEx_Pa
    (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty)

@[blueprint "chap7__example_7_4_4"]
noncomputable abbrev nnfHauptExDelta : NNFHauptExFormulaSet :=
  LCS.Finset.insert nnfHauptEx_Pa
    (LCS.Finset.insert nnfHauptEx_Qa
      (LCS.Finset.insert nnfHauptEx_RfaAndRfb LCS.Finset.empty))

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev nnfHauptEx_Ry : FormulaN nnfHauptExLang :=
  FormulaN.predN NNFHauptExPred.R
    (nnfHauptExVec1 (Term.var 1))

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_forallYOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_forallYRy :=
  .all 1 nnfHauptEx_Ry

@[blueprint "chap7__example_7_4_4"]
def nnfHauptEx_forallXOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_forallXBody :=
  .all 0 nnfHauptEx_QxOrForallYRy

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_afterFirstYOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_afterFirstInst :=
  .disjRight nnfHauptEx_Pa
    (.disjRight nnfHauptEx_Qa nnfHauptEx_forallYOccurrence)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
def nnfHauptEx_antXOccurrence :
    MaxQuantifierOccurrence nnfHauptEx_antFormula :=
  .disjRight nnfHauptEx_Pa nnfHauptEx_forallXOccurrence

noncomputable section

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_PaRectified :
    isRectified nnfHauptEx_Pa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_QaRectified :
    isRectified nnfHauptEx_Qa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfaRectified :
    isRectified nnfHauptEx_Rfa :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfbRectified :
    isRectified nnfHauptEx_Rfb :=
  AllRectified.isRectified_of_isQuantifierFree _ trivial

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_RfaAndRfbRectified :
    isRectified nnfHauptEx_RfaAndRfb :=
  AllRectified.isRectified_of_isQuantifierFree _ ⟨trivial, trivial⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_midAnt1Rectified :
    isRectified nnfHauptEx_midAnt1 :=
  AllRectified.isRectified_of_isQuantifierFree _
    ⟨trivial, ⟨trivial, trivial⟩⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example
theorem nnfHauptEx_midAnt2Rectified :
    isRectified nnfHauptEx_midAnt2 :=
  AllRectified.isRectified_of_isQuantifierFree _
    ⟨trivial, ⟨trivial, trivial⟩⟩
end
end LCS.Herbrand.NNFHauptsatz.Theorem
end
