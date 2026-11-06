import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Equality.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Equality.PureVariable
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.SharpenedHauptsatz.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.SharpenedHauptsatz

Theorem 7.4.2: midsequents of G2nnf= proofs and the sharpened Hauptsatz for G1nnf=
and G2nnf=.
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

-- ===================================================================
-- Lemma 7.4.3 (helper): RuleAppearsInTree_G2nnfEq
-- ===================================================================

-- ===================================================================
-- Lemma 7.4.3 (helper): RuleAppearsBelow_G2nnfEq
-- ===================================================================

-- ===================================================================
-- Theorem 7.4.2 (helper): allRulesSatisfy
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting that every rule in a G2nnf= proof tree satisfies the given predicate P. Used to state that all rules above the midsequent are propositional, weakening, or inessential cuts. -/
@[blueprint "chap7__theorem_7_4_2"]
def allRulesSatisfy {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (P : G2nnfEqRule L hL → Prop) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => True
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    P (.base rule) ∧ allRulesSatisfy P sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    P (.base rule) ∧ allRulesSatisfy P sub1 ∧
    allRulesSatisfy P sub2

-- ===================================================================
-- Theorem 7.4.2 (helper): occurrence-indexed lower paths
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Every inference strictly below the
target occurrence selected by `path` is a G2nnf= quantifier-for-subformulae
inference.  The target node's own inference belongs to the upper subtree. -/
@[blueprint "chap7__theorem_7_4_2"]
def AllRulesQuantifierOnPath_G2nnfEq {L : Language}
    {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath
  | .leftPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath
  | .rightPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath

-- ===================================================================
-- Theorem 7.4.2 (companion structure): IsMidsequent_G2nnfEq
-- ===================================================================

/-- Theorem 7.4.2 (companion structure): A sequent `mid` is the midsequent
of `T` when it is quantifier-free and one occurrence-identified node supplies
both the upper subtree (propositional, weakening, or inessential-cut rules)
and the lower quantifier-only root-to-node path.  Bundling the exact path with
the node prevents equal sequents at different occurrences from being spliced.
-/
@[blueprint "chap7__theorem_7_4_2"]
structure IsMidsequent_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
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
    ∃ occurrence : G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2,
      allRulesSatisfy (fun rule =>
        rule.isPropositionalOnly ∨ rule.isWeakening ∨
        rule.isInessentialCut) occurrence.node ∧
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path

-- ===================================================================
-- Theorem 7.4.2 (companion def): allFormulaeNNF
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting that every formula in both the antecedent and succedent of an `LCS.Finset`-based sequent is in NNF (FormulaN.isNNF holds for each formula). This is the hypothesis that all formulae in Gamma -> Delta are in negation normal form. -/
@[blueprint "chap7__theorem_7_4_2"]
def allFormulaeNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop :=
  (∀ A, Membership.mem seq.1 A → FormulaN.isNNF A) ∧
  (∀ A, Membership.mem seq.2 A → FormulaN.isNNF A)

-- ===================================================================
-- Theorem 7.4.2 (companion def): G1nnfEqProvable_Set
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting existence of an indexed G1nnf= proof tree concluding with the given `LCS.Finset`-based sequent. Under the indexed API, G1nnf= provability is `Nonempty (G1nnfEqProofTree Γ Δ)`. Mirrors `G1nnfProvableSet` from Layer 3a for the equality system. -/
@[blueprint "chap7__theorem_7_4_2"]
def G1nnfEqProvable_Set {L : Language} (hL : L.hasEquality = true)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop :=
  Nonempty (G1nnfEqProofTree hL seq.1 seq.2)

-- ===================================================================
-- Theorem 7.4.2: sharpenedHauptsatz_G2nnfEq
-- ===================================================================

/-- Theorem 7.4.2: Given a rectified `LCS.Finset`-based sequent (Gamma, Delta) containing only formulae in NNF, if it is G1nnf=-provable, then there is a pure-variable proof in G2nnf= without essential cuts that contains a midsequent Gamma' -> Delta' satisfying three properties: (1) Every formula in Gamma' -> Delta' is quantifier-free. (2) Every inference rule above Gamma' -> Delta' is either a weakening, a propositional rule, or an inessential cut (but not a quantifier rule). (3) Every inference rule below Gamma' -> Delta' is a quantifier rule. Rectification is the standing assumption at the start of §7.4 and is enforced at every G2nnf= proof node. The free/bound naming convention is required on the end/input sequent only, through finsetCrossNoFreeBound. Under the indexed `G2nnfEqProofTree Γ Δ` API, the conclusion is baked into the type, so no `T.conclusion = seq` or `T.WellFormed` conjunct is needed. The proof is essentially identical to the proof of Theorem 7.4.1 (sharpenedHauptsatz_G2nnf), but uses Lemma 7.4.3 (g2nnfEq_permutability) instead of Lemma 7.4.2. Lexicographic induction on (proofMeasureM_G2nnfEq T, proofMeasureN_G2nnfEq T). Base case: when m=0 and n=0, all propositional/weakening/ inessential-cut inferences are above all quantifier inferences; the midsequent is extracted from the premise of the highest quantifier inference. Inductive case 1 (m>0): find a quantifier rule above a propositional rule or inessential cut and permute them using Lemma 7.4.3. Inductive case 2 (m=0, n>0): find a quantifier rule above a weakening and permute them using Lemma 7.4.3. -/
@[attach_debt, blueprint "chap7__theorem_7_4_2" (main := true)]
theorem sharpenedHauptsatz_G2nnfEq {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hAllNNF : allFormulaeNNF seq)
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2)
    (hProv : G1nnfEqProvable_Set hL seq) :
    ∃ (T : G2nnfEqProofTree hL seq.1 seq.2)
      (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)),
      IsPureVariableProof_G2nnfEq T ∧
      T.hasNoEssentialCuts ∧
      IsMidsequent_G2nnfEq T mid 
end LCS.Herbrand.NNFHauptsatz.Equality
end
