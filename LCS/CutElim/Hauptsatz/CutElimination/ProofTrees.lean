import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Definition 6.4.2 (companion): A G1nnf proof tree over a language without
equality, indexed by its conclusion antecedent and succedent as `LCS.Finset (FormulaN L)`.
This matches the textbook Def 6.4.2: sequents are pairs of finite SETS
of NNF formulae. Leaves are axiom rule applications (zero premises),
and internal nodes apply one-premise or two-premise rules to subtrees
whose indices match `rule.premises Γ Δ`. Structural validity is built
into the type: exchange and contraction are free (Finset is unordered
and idempotent), and weakening is directly constructible via
`Finset.insert`. Every rule application also stores its complete
`ApplicationConditions`, so each indexed conclusion is in NNF. -/
@[blueprint "chap6__definition_6_4_2"]
inductive G1nnfProofTree {L : Language} (hL : L.withoutEquality) :
    LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) → Type where
  /-- Axiom leaf: the rule must produce zero premises in context
  (Γ, Δ); the conclusion is `rule.conclusion Γ Δ`. -/
  | axiom_ (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
      (hAxiom : (rule.premises Gamma Delta).length = 0)
      (hAC : rule.ApplicationConditions Gamma Delta) :
      G1nnfProofTree hL (rule.conclusion Gamma Delta).1
                     (rule.conclusion Gamma Delta).2
  /-- One-premise rule: `rule.premises Γ Δ` has length 1, and the
  subtree is indexed by that single premise. -/
  | onePremise (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 1)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub : G1nnfProofTree hL ((rule.premises Gamma Delta)[0]'(by omega)).1
                             ((rule.premises Gamma Delta)[0]'(by omega)).2) :
      G1nnfProofTree hL (rule.conclusion Gamma Delta).1
                     (rule.conclusion Gamma Delta).2
  /-- Two-premise rule: `rule.premises Γ Δ` has length 2, with the
  subtrees indexed by the two premises. -/
  | twoPremise (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 2)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub1 : G1nnfProofTree hL ((rule.premises Gamma Delta)[0]'(by omega)).1
                              ((rule.premises Gamma Delta)[0]'(by omega)).2)
      (sub2 : G1nnfProofTree hL ((rule.premises Gamma Delta)[1]'(by omega)).1
                              ((rule.premises Gamma Delta)[1]'(by omega)).2) :
      G1nnfProofTree hL (rule.conclusion Gamma Delta).1
                     (rule.conclusion Gamma Delta).2

namespace G1nnfProofTree

/-- Definition 6.4.2 (companion): Returns the conclusion
sequent of a G1nnf proof tree. For the indexed tree this is just
the type index `(Γ, Δ)`. -/
@[blueprint "chap6__definition_6_4_2"]
def conclusion {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G1nnfProofTree hL Γ Δ) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

end G1nnfProofTree

-- ===================================================================
-- Definition 6.4.2 (companion type): G1nnfDeductionTree (indexed)
-- ===================================================================
/-- Definition 6.4.2 (companion): Deduction trees for G1nnf over a language without
    equality, indexed by conclusion antecedent and succedent as `LCS.Finset (FormulaN L)`.
    Parallel to `G1nnfProofTree` with free-form leaves: a leaf is any
    NNF (Γ, Δ) pair with no rule applied. Both proof trees and deduction trees are formed from the G1nnf rules. Proof trees are
    precisely the deduction trees whose leaves each correspond to an
    axiom rule application (see `G1nnfDeductionTree.isProof` /
    `G1nnfDeductionTree.toProofTree`). -/
@[blueprint "chap6__definition_6_4_2"]
inductive G1nnfDeductionTree {L : Language} (hL : L.withoutEquality) :
    LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) → Type where
  /-- Free-form leaf: any NNF (Γ, Δ) pair is a leaf; no rule required. -/
  | leaf (Gamma Delta : LCS.Finset (FormulaN L))
      (hNNF : G1nnfFinsetSequent.IsNNF (Gamma, Delta)) :
      G1nnfDeductionTree hL Gamma Delta
  /-- One-premise rule application. -/
  | onePremise (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 1)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub : G1nnfDeductionTree hL ((rule.premises Gamma Delta)[0]'(by omega)).1
                                 ((rule.premises Gamma Delta)[0]'(by omega)).2) :
      G1nnfDeductionTree hL (rule.conclusion Gamma Delta).1
                          (rule.conclusion Gamma Delta).2
  /-- Two-premise rule application. -/
  | twoPremise (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 2)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub1 : G1nnfDeductionTree hL ((rule.premises Gamma Delta)[0]'(by omega)).1
                                  ((rule.premises Gamma Delta)[0]'(by omega)).2)
      (sub2 : G1nnfDeductionTree hL ((rule.premises Gamma Delta)[1]'(by omega)).1
                                  ((rule.premises Gamma Delta)[1]'(by omega)).2) :
      G1nnfDeductionTree hL (rule.conclusion Gamma Delta).1
                          (rule.conclusion Gamma Delta).2

namespace G1nnfDeductionTree

/-- Definition 6.4.2 (companion): Returns the conclusion sequent of a
G1nnf deduction tree. For the indexed tree this is just the type index
`(Γ, Δ)`. -/
@[blueprint "chap6__definition_6_4_2"]
def conclusion {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G1nnfDeductionTree hL Γ Δ) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

/-- Definition 6.4.2 (companion): `isProof` — true iff every leaf
corresponds to a zero-premise rule application. This is the bridge
between deduction trees and proof trees. -/
@[blueprint "chap6__definition_6_4_2"]
def isProof {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} → G1nnfDeductionTree hL Γ Δ → Prop
  | _, _, .leaf Gamma Delta _ =>
      ∃ rule : G1nnfRule L,
        (rule.premises Gamma Delta).length = 0 ∧
        rule.ApplicationConditions Gamma Delta ∧
        (rule.conclusion Gamma Delta) = (Gamma, Delta)
  | _, _, .onePremise _ _ _ _ _ sub => sub.isProof
  | _, _, .twoPremise _ _ _ _ _ sub1 sub2 => sub1.isProof ∧ sub2.isProof

/-- Definition 6.4.2 (companion): Converts a deduction tree whose leaves
are all axiom-rule applications into a `G1nnfProofTree` of the same
conclusion. Marked `noncomputable` because the axiom-rule witness at
each leaf is extracted via `Classical.choose`. -/
@[blueprint "chap6__definition_6_4_2"]
noncomputable def toProofTree {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfDeductionTree hL Γ Δ) → T.isProof → G1nnfProofTree hL Γ Δ
  | _, _, .leaf Gamma Delta _, hp => by
      let rule := Classical.choose hp
      have hspec := Classical.choose_spec hp
      have hAxiom : (rule.premises Gamma Delta).length = 0 := hspec.1
      have hAC : rule.ApplicationConditions Gamma Delta := hspec.2.1
      have hConc : (rule.conclusion Gamma Delta) = (Gamma, Delta) := hspec.2.2
      have hTree : G1nnfProofTree hL (rule.conclusion Gamma Delta).1
                                   (rule.conclusion Gamma Delta).2 :=
        G1nnfProofTree.axiom_ rule Gamma Delta hAxiom hAC
      rw [hConc] at hTree
      exact hTree
  | _, _, .onePremise rule Γ Δ hPrem hAC sub, hp =>
      G1nnfProofTree.onePremise rule Γ Δ hPrem hAC (sub.toProofTree hp)
  | _, _, .twoPremise rule Γ Δ hPrem hAC sub1 sub2, hp =>
      G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
        (sub1.toProofTree hp.1) (sub2.toProofTree hp.2)

end G1nnfDeductionTree
namespace G1nnfProofTree

/-- Lemma 6.4.6 (companion): Forgetful embedding from a G1nnf proof tree
    to the underlying deduction tree. Every proof tree IS a deduction tree
    (the deduction-tree type has free leaves; proof-tree leaves come with a
    rule-axiom witness that is dropped on forgetting). Used to specialize
    Def 6.4.5's `notBoundIn` (textbook-defined on deduction trees) to
    proof trees via `T.forgetProofTree.notBoundIn y`. -/
@[blueprint "chap6__definition_6_4_2"]
noncomputable def forgetProofTree {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → G1nnfDeductionTree hL Γ Δ
  | _, _, .axiom_ rule Γ Δ _ hAC =>
      G1nnfDeductionTree.leaf (rule.conclusion Γ Δ).1
        (rule.conclusion Γ Δ).2 hAC.2
  | _, _, .onePremise rule Γ Δ hPrem hAC sub =>
      G1nnfDeductionTree.onePremise rule Γ Δ hPrem hAC sub.forgetProofTree
  | _, _, .twoPremise rule Γ Δ hPrem hAC sub1 sub2 =>
      G1nnfDeductionTree.twoPremise rule Γ Δ hPrem hAC
        sub1.forgetProofTree sub2.forgetProofTree

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end
