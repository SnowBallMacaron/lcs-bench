import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.CutRank.ProofsStamp

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
namespace G1nnfProofTree

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
