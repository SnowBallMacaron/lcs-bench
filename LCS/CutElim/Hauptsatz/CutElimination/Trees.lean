import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Trees.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.FirstOrder.SyntaxN
namespace FormulaN

/-- Definition 6.4.3: The degree |A| of a formula A in NNF is defined
inductively: (i) If A is atomic or the negation of an atomic formula,
|A| = 0; (ii) If A is (B or C) or (B and C), |A| = max(|B|,|C|) + 1;
(iii) If A is forall x B or exists x B, |A| = |B| + 1. For non-NNF
formulae (e.g., neg of compound), a default value is returned. -/
@[blueprint "chap6__definition_6_4_3" (main := true)]
def degree {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg (.predN _ _) => 0
  | .neg (.eq_ _ _ _) => 0
  | .disj A B => max A.degree B.degree + 1
  | .conj A B => max A.degree B.degree + 1
  | .all _ A => A.degree + 1
  | .ex _ A => A.degree + 1
  | _ => 0

end FormulaN
end LCS.FirstOrder.SyntaxN
end

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

end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

/-- Definition 6.4.2 (companion): Returns the conclusion
sequent of a G1nnf proof tree. For the indexed tree this is just
the type index `(Γ, Δ)`. -/
@[blueprint "chap6__definition_6_4_2"]
def conclusion {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G1nnfProofTree hL Γ Δ) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) : T.conclusion = (Γ, Δ) := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every proof tree has an NNF root sequent. -/
theorem conclusion_isNNF {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) :
    G1nnfFinsetSequent.IsNNF T.conclusion := by
  cases T with
  | axiom_ _ _ _ _ hAC => exact hAC.2
  | onePremise _ _ _ _ hAC _ => exact hAC.2
  | twoPremise _ _ _ _ hAC _ _ => exact hAC.2

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

open LCS.FirstOrder.SemanticsN LCS.FirstOrder.SemanticsN.Substitution in
/-- Soundness of G1nnf: every proof tree over a language without equality
has a valid end sequent. The cut inference combines its two independent
antecedents and succedents. -/
@[blueprint "chap6__definition_6_4_2"]
theorem g1nnf_soundness {L : Language} (hL : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ) :
    ∀ (M : Structure L) (val : Assignment M),
      (∀ A ∈ Γ, formulaEvalN M A val) →
      ∃ A ∈ Δ, formulaEvalN M A val 


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

end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfDeductionTree

/-- Definition 6.4.2 (companion): Returns the conclusion sequent of a
G1nnf deduction tree. For the indexed tree this is just the type index
`(Γ, Δ)`. -/
@[blueprint "chap6__definition_6_4_2"]
def conclusion {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G1nnfDeductionTree hL Γ Δ) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfDeductionTree hL Γ Δ) : T.conclusion = (Γ, Δ) := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every deduction tree has an NNF root sequent, including a free leaf's
actual indexed conclusion. -/
theorem conclusion_isNNF {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfDeductionTree hL Γ Δ) :
    G1nnfFinsetSequent.IsNNF T.conclusion := by
  cases T with
  | leaf _ _ hNNF => exact hNNF
  | onePremise _ _ _ _ hAC _ => exact hAC.2
  | twoPremise _ _ _ _ hAC _ _ => exact hAC.2

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
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfRule

/-- Definition 6.4.4 (required helper): Extracts the cut formula from
a G1nnf rule. Returns `some A` for a cut rule with cut formula `A`,
and `none` for non-cut rules. Used in the body of
`G1nnfProofTree.cutRank` to distinguish cut inferences (which contribute
`|A| + 1` to the cut-rank) from non-cut inferences. -/
@[blueprint "chap6__definition_6_4_4"]
def cutFormula {L : Language} : G1nnfRule L → Option (FormulaN L)
  | .cut A _ _ => some A
  | _ => none

end G1nnfRule
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
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

/-- Definition 6.4.4: The cut-rank c(T) of a G1nnf proof tree T is
defined inductively: if T is an axiom, c(T) = 0; if the last inference
has one premise and is not a cut, c(T) = c(T₁); if the last inference
has two premises and is not a cut, c(T) = max(c(T₁), c(T₂)); if the
last inference is a cut with cut formula A,
c(T) = max(|A| + 1, c(T₁), c(T₂)). -/
@[blueprint "chap6__definition_6_4_4" (main := true)]
noncomputable def cutRank {L : Language} {hL : L.withoutEquality} : {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ _ sub => cutRank sub
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
    match rule.cutFormula with
    | some A => max (A.degree + 1) (max (cutRank sub1) (cutRank sub2))
    | none => max (cutRank sub1) (cutRank sub2)

/-- Definition 6.4.4 (companion): No node of the proof tree applies a cut
rule. This is checked at the root and recursively in every subtree. -/
@[blueprint "chap6__definition_6_4_4"]
def hasNoCut {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} → G1nnfProofTree hL Γ Δ → Prop
  | _, _, .axiom_ rule _ _ _ _ => rule.cutFormula = none
  | _, _, .onePremise rule _ _ _ _ sub =>
    rule.cutFormula = none ∧ hasNoCut sub
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
    rule.cutFormula = none ∧ hasNoCut sub1 ∧ hasNoCut sub2

/-- Definition 6.4.4 (companion): The cut-rank is zero exactly when no
node applies a cut. Each cut contributes `A.degree + 1`, even when the
cut formula has degree zero. -/
@[blueprint "chap6__definition_6_4_4"]
theorem cutRank_eq_zero_iff_hasNoCut {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ) :
    T.cutRank = 0 ↔ T.hasNoCut 

/-- Definition 6.4.4 (companion): A G1nnf proof tree T is cut-free
iff its cut-rank is 0. By `cutRank_eq_zero_iff_hasNoCut`, this is
equivalent to the structural condition that no node applies a cut. -/
@[blueprint "chap6__definition_6_4_4"]
noncomputable def isCutFree {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) : Prop :=
  cutRank T = 0

-- ===================================================================
-- Definition 6.4.4 (helper): G1nnfProofTree.depth
-- ===================================================================

/-- Definition 6.4.4 (helper): The depth of a G1nnf proof tree,
measuring the maximum number of inference steps from the root to
any leaf. Used in the statements of the substitution, weakening,
inversion, reduction, and cut elimination theorems. -/
@[blueprint "chap6__lemma_6_4_4"]
noncomputable def depth {L : Language} {hL : L.withoutEquality} : {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ _ sub => depth sub + 1
  | _, _, .twoPremise _ _ _ _ _ sub1 sub2 =>
    max (depth sub1) (depth sub2) + 1

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem LCS.Finset.insert_comm [DecidableEq α] (a b : α) (s : LCS.Finset α) :
    LCS.Finset.insert a (LCS.Finset.insert b s) =
    LCS.Finset.insert b (LCS.Finset.insert a s) := by
-- BEGIN PROOF
  apply LCS.Finset.ext
  intro x
  rw [LCS.Finset.mem_insert, LCS.Finset.mem_insert,
      LCS.Finset.mem_insert, LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | rfl | h) <;> simp_all
  · rintro (rfl | rfl | h) <;> simp_all

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Inserting into the first set commutes with taking its union. -/
theorem LCS.Finset.insert_union [DecidableEq α] (a : α) (s t : LCS.Finset α) :
    LCS.Finset.insert a (LCS.Finset.union s t) =
      LCS.Finset.union (LCS.Finset.insert a s) t := by
  apply LCS.Finset.ext
  intro x
  simp only [LCS.Finset.mem_insert, LCS.Finset.mem_union, or_assoc]

end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfRule

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Extending the antecedent preserves a rule's side conditions provided
the inserted formula avoids the eigenvariable of a universal-right or
existential-left rule. Non-eigenvariable rules need no extra hypothesis. -/
theorem sideConditions_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hSC : rule.SideConditions Gamma Delta)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.SideConditions (LCS.Finset.insert C Gamma) Delta := by
-- BEGIN PROOF
  cases rule <;>
    simp only [SideConditions] at hSC ⊢ <;>
    simp_all
-- END PROOF

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Extending the succedent preserves a rule's side conditions provided
the inserted formula avoids the eigenvariable of a universal-right or
existential-left rule. Non-eigenvariable rules need no extra hypothesis. -/
theorem sideConditions_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hSC : rule.SideConditions Gamma Delta)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.SideConditions Gamma (LCS.Finset.insert C Delta) := by
-- BEGIN PROOF
  cases rule <;>
    simp only [SideConditions] at hSC ⊢ <;>
    simp_all
-- END PROOF

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Extending the antecedent preserves a legal rule application when the
inserted formula is in NNF and avoids the eigenvariable of a universal-right
or existential-left rule. The NNF hypothesis is necessary because the
extended conclusion is itself a G1nnf sequent. -/
theorem applicationConditions_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.ApplicationConditions (LCS.Finset.insert C Gamma) Delta := by
-- BEGIN PROOF
  cases rule <;>
    refine
      ⟨sideConditions_insert_left _ Gamma Delta C hAC.1 hFresh, ?_⟩ <;>
    simp only [conclusion] at hAC ⊢
  all_goals first
    | exact hAC.2
    | simpa only [LCS.Finset.insert_comm, LCS.Finset.insert_union] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
-- END PROOF

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Extending the succedent preserves a legal rule application when the
inserted formula is in NNF and avoids the eigenvariable of a universal-right
or existential-left rule. The NNF hypothesis is necessary because the
extended conclusion is itself a G1nnf sequent. -/
theorem applicationConditions_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.ApplicationConditions Gamma (LCS.Finset.insert C Delta) := by
-- BEGIN PROOF
  cases rule <;>
    refine
      ⟨sideConditions_insert_right _ Gamma Delta C hAC.1 hFresh, ?_⟩ <;>
    simp only [conclusion] at hAC ⊢
  all_goals first
    | exact hAC.2
    | simpa only [LCS.Finset.insert_comm, LCS.Finset.insert_union] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
-- END PROOF

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A zero-premise application can be weakened on the left by extending the
context stored inside its axiom rule. The returned conclusion equality records
that the actual axiom conclusion, rather than its ignored ambient contexts, was
extended. -/
theorem applicationConditions_axiom_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAxiom : (rule.premises Gamma Delta).length = 0)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF) :
    ∃ weakenedRule : G1nnfRule L,
      (weakenedRule.premises Gamma Delta).length = 0 ∧
      weakenedRule.ApplicationConditions Gamma Delta ∧
      weakenedRule.conclusion Gamma Delta =
        (LCS.Finset.insert C (rule.conclusion Gamma Delta).1,
          (rule.conclusion Gamma Delta).2) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomPosAtomic A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomNegAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomNegAtomic A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompLeft A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompLeft A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompRight A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompRight A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · rfl
  | cut _ _ _ => simp [premises] at hAxiom
  | conjLeft1 _ _ => simp [premises] at hAxiom
  | conjLeft2 _ _ => simp [premises] at hAxiom
  | conjRight _ _ => simp [premises] at hAxiom
  | disjLeft _ _ => simp [premises] at hAxiom
  | disjRight1 _ _ => simp [premises] at hAxiom
  | disjRight2 _ _ => simp [premises] at hAxiom
  | allLeft _ _ _ => simp [premises] at hAxiom
  | allRight _ _ _ => simp [premises] at hAxiom
  | exLeft _ _ _ => simp [premises] at hAxiom
  | exRight _ _ _ => simp [premises] at hAxiom
-- END PROOF

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A zero-premise application can be weakened on the right by extending the
context stored inside its axiom rule. The returned conclusion equality records
that the actual axiom conclusion, rather than its ignored ambient contexts, was
extended. -/
theorem applicationConditions_axiom_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAxiom : (rule.premises Gamma Delta).length = 0)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF) :
    ∃ weakenedRule : G1nnfRule L,
      (weakenedRule.premises Gamma Delta).length = 0 ∧
      weakenedRule.ApplicationConditions Gamma Delta ∧
      weakenedRule.conclusion Gamma Delta =
        ((rule.conclusion Gamma Delta).1,
          LCS.Finset.insert C (rule.conclusion Gamma Delta).2) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomPosAtomic A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomNegAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomNegAtomic A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompLeft A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompLeft A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · rfl
  | axiomCompRight A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompRight A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | cut _ _ _ => simp [premises] at hAxiom
  | conjLeft1 _ _ => simp [premises] at hAxiom
  | conjLeft2 _ _ => simp [premises] at hAxiom
  | conjRight _ _ => simp [premises] at hAxiom
  | disjLeft _ _ => simp [premises] at hAxiom
  | disjRight1 _ _ => simp [premises] at hAxiom
  | disjRight2 _ _ => simp [premises] at hAxiom
  | allLeft _ _ _ => simp [premises] at hAxiom
  | allRight _ _ _ => simp [premises] at hAxiom
  | exLeft _ _ _ => simp [premises] at hAxiom
  | exRight _ _ _ => simp [premises] at hAxiom
-- END PROOF


-- END PROOF



end G1nnfRule
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

/-- Lemma 6.4.3 (companion): Collect all eigenvariables from a G1nnf proof tree. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def eigenvariables {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → Set Nat
  | _, _, .axiom_ _ _ _ _ _ => fun _ => False
  | _, _, .onePremise rule _ _ _ _ sub => fun v =>
    (match rule with
     | .allRight _ _ y => v = y
     | .exLeft _ _ y => v = y
     | _ => False) ∨ eigenvariables sub v
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 => fun v =>
    (match rule with
     | .allRight _ _ y => v = y
     | .exLeft _ _ y => v = y
     | _ => False) ∨ eigenvariables sub1 v ∨ eigenvariables sub2 v

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz




-- END PROOF


-- END PROOF


-- END PROOF


-- END PROOF


-- END PROOF

-- ===================================================================
-- Weakening: weakenTreeLeft — insert a formula into the antecedent
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Internal helper: structural weakening on the left of a G1nnf
proof tree. Given a proof of Γ → Δ, produces a proof of
(insert C Γ) → Δ by pushing `insert C` through each rule's context
parameter and reconciling indices via `insert_comm`. Used as the
underlying construction for the tagged Lem 6.4.5 statement
`g1nnf_weakening_left`. -/
noncomputable def G1nnfProofTree.weakenTreeLeft {L : Language} {hL : L.withoutEquality}
    (C : FormulaN L) (hNNF : C.isNNF) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) →
    (∀ v, v ∈ formulaFVN C → ¬ T.eigenvariables v) →
    G1nnfProofTree hL (LCS.Finset.insert C Γ) Δ
  | _, _, .axiom_ rule Gamma Delta hAxiom hAC, _ => by
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Gamma Delta C hAxiom hAC hNNF
    let weakenedRule := Classical.choose hWeakened
    have hSpec := Classical.choose_spec hWeakened
    have hTree :=
      G1nnfProofTree.axiom_ (hL := hL) weakenedRule Gamma Delta hSpec.1 hSpec.2.1
    rw [hSpec.2.2] at hTree
    exact hTree
  | _, _, .onePremise rule Gamma Delta hPrem hAC sub, hFV =>
    have hSubFV : ∀ v, v ∈ formulaFVN C → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    have weakSub := weakenTreeLeft C hNNF sub hSubFV
    by
    cases rule with
    | conjLeft1 A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.conj A B) Gamma]
      refine .onePremise (.conjLeft1 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjLeft1 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert A (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C A Gamma]; exact weakSub
    | conjLeft2 A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.conj A B) Gamma]
      refine .onePremise (.conjLeft2 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjLeft2 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert B (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C B Gamma]; exact weakSub
    | allLeft x A t =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.all x A) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.all x A) Gamma]
      refine .onePremise (.allLeft x A t) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.allLeft x A t) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert (formulaSubstN A t x) (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C (formulaSubstN A t x) Gamma]; exact weakSub
    | exLeft x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_left
        (.exLeft x A y) Gamma Delta C hAC hNNF hFresh
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.ex x A) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.ex x A) Gamma]
      refine .onePremise (.exLeft x A y) (LCS.Finset.insert C Gamma) Delta
        hPrem hAC' ?_
      show G1nnfProofTree hL (LCS.Finset.insert (formulaSubstN A (.var y) x) (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C (formulaSubstN A (.var y) x) Gamma]; exact weakSub
    | disjRight1 A B =>
      exact .onePremise (.disjRight1 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjRight1 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | disjRight2 A B =>
      exact .onePremise (.disjRight2 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjRight2 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | allRight x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_left
        (.allRight x A y) Gamma Delta C hAC hNNF hFresh
      exact .onePremise (.allRight x A y) (LCS.Finset.insert C Gamma) Delta
        hPrem hAC' weakSub
    | exRight x A t =>
      exact .onePremise (.exRight x A t) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.exRight x A t) Gamma Delta C hAC hNNF trivial) weakSub
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | _, _, .twoPremise rule Gamma Delta hPrem hAC sub1 sub2, hFV =>
    have hSub1FV : ∀ v, v ∈ formulaFVN C → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV : ∀ v, v ∈ formulaFVN C → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    have weakSub1 := weakenTreeLeft C hNNF sub1 hSub1FV
    have weakSub2 := weakenTreeLeft C hNNF sub2 hSub2FV
    by
    cases rule with
    | cut A Lam Theta =>
      show G1nnfProofTree hL
        (LCS.Finset.insert C (LCS.Finset.union Gamma Lam))
        (LCS.Finset.union Delta Theta)
      rw [LCS.Finset.insert_union]
      exact .twoPremise (.cut A Lam Theta) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.cut A Lam Theta) Gamma Delta C hAC hNNF trivial) weakSub1 sub2
    | conjRight A B =>
      exact .twoPremise (.conjRight A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjRight A B) Gamma Delta C hAC hNNF trivial)
        weakSub1 weakSub2
    | disjLeft A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.disj A B) Gamma]
      refine .twoPremise (.disjLeft A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjLeft A B) Gamma Delta C hAC hNNF trivial) ?_ ?_
      · show G1nnfProofTree hL (LCS.Finset.insert A (LCS.Finset.insert C Gamma)) Delta
        rw [← LCS.Finset.insert_comm C A Gamma]; exact weakSub1
      · show G1nnfProofTree hL (LCS.Finset.insert B (LCS.Finset.insert C Gamma)) Delta
        rw [← LCS.Finset.insert_comm C B Gamma]; exact weakSub2
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Structural weakening on the right: given a proof of Γ → Δ,
produce a proof of Γ → (insert C Δ). Symmetric to weakenTreeLeft. -/
noncomputable def G1nnfProofTree.weakenTreeRight {L : Language} {hL : L.withoutEquality}
    (C : FormulaN L) (hNNF : C.isNNF) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) →
    (∀ v, v ∈ formulaFVN C → ¬ T.eigenvariables v) →
    G1nnfProofTree hL Γ (LCS.Finset.insert C Δ)
  | _, _, .axiom_ rule Gamma Delta hAxiom hAC, _ => by
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Gamma Delta C hAxiom hAC hNNF
    let weakenedRule := Classical.choose hWeakened
    have hSpec := Classical.choose_spec hWeakened
    have hTree :=
      G1nnfProofTree.axiom_ (hL := hL) weakenedRule Gamma Delta hSpec.1 hSpec.2.1
    rw [hSpec.2.2] at hTree
    exact hTree
  | _, _, .onePremise rule Gamma Delta hPrem hAC sub, hFV =>
    have hSubFV : ∀ v, v ∈ formulaFVN C → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    have weakSub := weakenTreeRight C hNNF sub hSubFV
    by
    cases rule with
    | disjRight1 A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Delta))
      rw [LCS.Finset.insert_comm C (.disj A B) Delta]
      refine .onePremise (.disjRight1 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjRight1 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub
    | disjRight2 A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Delta))
      rw [LCS.Finset.insert_comm C (.disj A B) Delta]
      refine .onePremise (.disjRight2 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjRight2 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert B (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C B Delta]; exact weakSub
    | allRight x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_right
        (.allRight x A y) Gamma Delta C hAC hNNF hFresh
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.all x A) Delta))
      rw [LCS.Finset.insert_comm C (.all x A) Delta]
      refine .onePremise (.allRight x A y) Gamma (LCS.Finset.insert C Delta)
        hPrem hAC' ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert (formulaSubstN A (.var y) x) (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C (formulaSubstN A (.var y) x) Delta]; exact weakSub
    | exRight x A t =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.ex x A) Delta))
      rw [LCS.Finset.insert_comm C (.ex x A) Delta]
      refine .onePremise (.exRight x A t) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.exRight x A t) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert (formulaSubstN A t x) (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C (formulaSubstN A t x) Delta]; exact weakSub
    | conjLeft1 A B =>
      exact .onePremise (.conjLeft1 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjLeft1 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | conjLeft2 A B =>
      exact .onePremise (.conjLeft2 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjLeft2 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | allLeft x A t =>
      exact .onePremise (.allLeft x A t) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.allLeft x A t) Gamma Delta C hAC hNNF trivial) weakSub
    | exLeft x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_right
        (.exLeft x A y) Gamma Delta C hAC hNNF hFresh
      exact .onePremise (.exLeft x A y) Gamma (LCS.Finset.insert C Delta)
        hPrem hAC' weakSub
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | _, _, .twoPremise rule Gamma Delta hPrem hAC sub1 sub2, hFV =>
    have hSub1FV : ∀ v, v ∈ formulaFVN C → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV : ∀ v, v ∈ formulaFVN C → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    have weakSub1 := weakenTreeRight C hNNF sub1 hSub1FV
    have weakSub2 := weakenTreeRight C hNNF sub2 hSub2FV
    by
    cases rule with
    | cut A Lam Theta =>
      show G1nnfProofTree hL (LCS.Finset.union Gamma Lam)
        (LCS.Finset.insert C (LCS.Finset.union Delta Theta))
      rw [LCS.Finset.insert_union]
      refine .twoPremise (.cut A Lam Theta) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.cut A Lam Theta) Gamma Delta C hAC hNNF trivial) ?_ sub2
      show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub1
    | conjRight A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Delta))
      rw [LCS.Finset.insert_comm C (.conj A B) Delta]
      refine .twoPremise (.conjRight A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjRight A B) Gamma Delta C hAC hNNF trivial) ?_ ?_
      · show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
        rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub1
      · show G1nnfProofTree hL Gamma (LCS.Finset.insert B (LCS.Finset.insert C Delta))
        rw [← LCS.Finset.insert_comm C B Delta]; exact weakSub2
    | disjLeft A B =>
      exact .twoPremise (.disjLeft A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjLeft A B) Gamma Delta C hAC hNNF trivial)
        weakSub1 weakSub2
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem

end LCS.CutElim.Hauptsatz
end

