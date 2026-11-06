import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.GraphOfConjunction
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

/-- The disjoint union of the equivalence relations on the occurring sort fibers. -/
@[attach_debt, blueprint "chap10__lemma_10_6_2"]
theorem positiveClosure_equivalence {L : MSLanguage} (C : MSFormula L) :
    Equivalence (msCongruenceClosure (graphOfConjunction C)
      (positiveEquationRelation C) (positiveEquationRelation_sortSupported C))

-- ===================================================================
-- Lemma 10.6.2: the semantic-equality relation R and entailment basis
-- ===================================================================

/-- Lemma 10.6.2 (companion): `E_set = {t_1 =̇_{s_1} u_1, …,
t_m =̇_{s_m} u_m}` — the set of POSITIVE equations of `C` used as the
entailment basis for `R_s`. -/
@[blueprint "chap10__lemma_10_6_2"]
def equationSetOfConjunction {L : MSLanguage} (C : MSFormula L) :
    Set (MSFormula L) :=
  fun A => msIsPositiveEquation A ∧ msConjunctContains C A

/-- Lemma 10.6.2 (companion): The `S(C)`-indexed family `R` of relations
`R_s` on `TERM(C)`, defined by `t R_s u ↔ E_set ⊨ t =̇_s u`. Shown to be
a `G(C)`-congruence containing `E`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def semanticEqualityRelation {L : MSLanguage} (C : MSFormula L)
    (s : L.SortType) (t u : MSTerm L s) : Prop :=
  ∃ hL : L.hasEquality = true,
    msEntails (equationSetOfConjunction C) (MSFormula.eq_ hL s t u)

/-- Lemma 10.6.2 (companion): The node-level lift of the semantic-equality
family `R` to `(graphOfConjunction C).Node`: two nodes are `R`-related
when they have a common sort `s` and their underlying sort-`s` terms are
`R_s`-related. This is the `G(C)`-relation whose congruence property is
asserted by `semanticEqualityRelation_isCongruence`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def semanticEqualityRelationNode {L : MSLanguage}
    (C : MSFormula L) (p q : (graphOfConjunction C).Node) : Prop :=
  ∃ (s : L.SortType) (h1 : p.1.1 = s) (h2 : q.1.1 = s),
    semanticEqualityRelation C s (h1 ▸ p.1.2) (h2 ▸ q.1.2)

/-- Lemma 10.6.2 (companion): Introduction rule for the node relation from
explicit sorted-term shapes: if `u.1 = ⟨s, tu⟩`, `v.1 = ⟨s, tv⟩` and the
sort-level relation holds between `tu` and `tv`, then the node relation
holds. Avoids manual transport at the call sites. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem semanticEqualityRelationNode_mk {L : MSLanguage} (C : MSFormula L)
    (u v : (graphOfConjunction C).Node) (s : L.SortType)
    (tu tv : MSTerm L s) (hu : u.1 = ⟨s, tu⟩) (hv : v.1 = ⟨s, tv⟩)
    (hrel : semanticEqualityRelation C s tu tv) :
    semanticEqualityRelationNode C u v 

/-- Lemma 10.6.2 (companion): Elimination rule for the node relation:
given explicit shapes `u.1 = ⟨s, tu⟩`, `v.1 = ⟨s, tv⟩`, the node relation
yields the sort-level relation between `tu` and `tv`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem semanticEqualityRelationNode_elim {L : MSLanguage} (C : MSFormula L)
    (u v : (graphOfConjunction C).Node) (s : L.SortType)
    (tu tv : MSTerm L s) (hu : u.1 = ⟨s, tu⟩) (hv : v.1 = ⟨s, tv⟩)
    (hrel : semanticEqualityRelationNode C u v) :
    semanticEqualityRelation C s tu tv 

/-- Lemma 10.6.2 (companion): The semantic-equality family `R` is a
`G(C)`-congruence containing `E` — established via reflexivity on `E`
(`E_set ⊨ t_i =̇ u_i` so `t_i R u_i`) and the equality semantics of
function application (componentwise `E_set ⊨ y_i =̇ z_i` give
`E_set ⊨ f y_1…y_k =̇ f z_1…z_k`). -/
@[attach_debt, blueprint "chap10__lemma_10_6_2"]
theorem semanticEqualityRelation_isCongruence {L : MSLanguage}
    (C : MSFormula L) :
    MSGCongruence (graphOfConjunction C) (semanticEqualityRelationNode C) 

/-- Lemma 10.6.2 (companion): The seed relation `E = positiveEquationRelation`
is contained in the semantic-equality node relation `R`: a positive
equation `t =̇_s u` of `C` lies in `E_set`, so any model of `E_set`
satisfies `t =̇_s u` — hence `t R_s u`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem positiveEquationRelation_subset_semantic {L : MSLanguage}
    (C : MSFormula L) (p q : (graphOfConjunction C).Node)
    (h : positiveEquationRelation C p q) :
    semanticEqualityRelationNode C p q 

/-- Lemma 10.6.2 (companion): The soundness step. Because `R*` is the
LEAST `G(C)`-congruence containing `E` (`msCongruenceClosure_smallest`,
sibling core module) and `R = semanticEqualityRelation` is a
`G(C)`-congruence containing `E`, `R* ⊆ R`; hence a collision
`r_j R* v_j` gives `E_set ⊨ r_j =̇_{s'_j} v_j`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem collision_entails_equation {L : MSLanguage} (C : MSFormula L)
    (hL : L.hasEquality = true) (s : L.SortType) (r v : MSTerm L s)
    (p q : (graphOfConjunction C).Node) (hp : p.1 = ⟨s, r⟩) (hq : q.1 = ⟨s, v⟩)
    (hcol : msCongruenceClosure (graphOfConjunction C)
      (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) p q) :
    msEntails (equationSetOfConjunction C) (MSFormula.eq_ hL s r v) 

/-- Lemma 10.6.2 (companion): A conjunct contained in `C` is true in any
model of `C` — if `C_M[v] = T` and `msConjunctContains C X`, then
`X_M[v] = T`. By induction on the conjunction tree of `C`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem msConjunctContains_eval {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) :
    ∀ (C X : MSFormula L), msConjunctContains C X →
      msFormulaEval M C v = BoolVal.T → msFormulaEval M X v = BoolVal.T 

/-- Lemma 10.6.2 (companion, forward direction): If `r_j R* v_j` for some
negated equation `¬ r_j =̇ v_j` of `C`, then since any model of `C`
satisfies `E_set`, that model would satisfy both `r_j =̇ v_j` (from
`collision_entails_equation`) and `¬ r_j =̇ v_j` — a contradiction — so
`C` is unsatisfiable. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem collision_unsat_direction {L : MSLanguage} (C : MSFormula L)
    (h : ∃ (hL : L.hasEquality = true) (s : L.SortType) (r v : MSTerm L s)
      (p q : (graphOfConjunction C).Node),
      msConjunctContains C (MSFormula.neg (MSFormula.eq_ hL s r v)) ∧
        p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
        msCongruenceClosure (graphOfConjunction C)
          (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) p q) :
    msUnsatisfiable C 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
