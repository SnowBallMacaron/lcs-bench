import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.FirstOrder.Semantics
import LCS.CutElim.Hauptsatz.Equality.SystemG1nnfEq
import Attach
import LCS.CutElim.Hauptsatz.Equality.CutElimination.ProofsStamp

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality
namespace G1nnfEqProofTree

/-- Lemma 6.4.8 (helper): The depth of a G1nnfEq proof tree,
measuring the maximum number of inference steps from the root to
any leaf. -/
@[blueprint "chap6__theorem_6_4_2"]
noncomputable def depth {L : Language} {hL : L.hasEquality = true} :
    {Γ Δ : Finset (FormulaN L)} →
    G1nnfEqProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ _ sub => depth sub + 1
  | _, _, .twoPremise _ _ _ _ _ sub1 sub2 =>
    max (depth sub1) (depth sub2) + 1

end G1nnfEqProofTree

/-- Lemma 6.4.9 (required def): A cut is inessential if its cut
formula is a literal over the equality predicate, i.e., it has
the form s = t or neg(s = t). Inessential cuts are preserved by
the cut elimination theorem for G1nnf_equal; only essential cuts
are eliminated. -/
@[blueprint "chap6__lemma_6_4_9"]
def isInessentialCut {L : Language} : FormulaN L → Prop
  | .eq_ _ _ _ => True
  | .neg (.eq_ _ _ _) => True
  | _ => False

-- ===================================================================
-- Lemma 6.4.9 (required def): isEssentialCut
-- ===================================================================

namespace G1nnfEqProofTree

/-- Lemma 6.4.9 (required def): The essential cut-rank of a
G1nnfEq proof tree, defined like cutRank but only counting
essential cuts (ignoring inessential equality cuts). -/
@[blueprint "chap6__lemma_6_4_9"]
noncomputable def essentialCutRank {L : Language} {hL : L.hasEquality = true} :
    {Γ Δ : Finset (FormulaN L)} →
    G1nnfEqProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ _ sub => essentialCutRank sub
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
    match rule.cutFormula with
    | some (.eq_ _ _ _) =>
      -- Inessential cut (literal equality): ignore
      max (essentialCutRank sub1) (essentialCutRank sub2)
    | some (.neg (.eq_ _ _ _)) =>
      -- Inessential cut (negated equality): ignore
      max (essentialCutRank sub1) (essentialCutRank sub2)
    | some A =>
      -- Essential cut: count towards cut-rank
      max (A.degree + 1)
        (max (essentialCutRank sub1) (essentialCutRank sub2))
    | none =>
      max (essentialCutRank sub1) (essentialCutRank sub2)

/-- Transport a proof tree across equal conclusion indices. -/
noncomputable def cast {L : Language} {hL : L.hasEquality = true}
    {Γ Δ Γ' Δ' : Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfEqProofTree hL Γ Δ) :
    G1nnfEqProofTree hL Γ' Δ' :=
  hΓ ▸ hΔ ▸ T

/-- The predicate rank of a literal. Ordinary predicate literals use the
language arity, equality literals have rank two, and non-literals contribute
zero. This is the local rank notion needed by Lemma 6.4.9. -/
@[blueprint "chap6__theorem_6_4_2"]
def literalPredRank {L : Language} : FormulaN L → Nat
  | .predN P _ => L.predArity P
  | .neg (.predN P _) => L.predArity P
  | .eq_ _ _ _ => 2
  | .neg (.eq_ _ _ _) => 2
  | _ => 0

end G1nnfEqProofTree
namespace G1nnfEqProofTree

/-- Lemma 6.4.9 (helper): Collect the maximum predicate rank of
all literal cut formulae in a single proof tree, traversing
recursively through the entire tree. -/
@[blueprint "chap6__theorem_6_4_2"]
noncomputable def maxPredRankTree {L : Language} {hL : L.hasEquality = true} :
    {Γ Δ : Finset (FormulaN L)} →
    G1nnfEqProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ _ sub => maxPredRankTree sub
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
    let localRank := match rule.cutFormula with
      | some A => literalPredRank A
      | none => 0
    max localRank
      (max (maxPredRankTree sub1) (maxPredRankTree sub2))

/-- Lemma 6.4.9 (required def): The maximal predicate rank `m` of all
predicate symbols whose literals are cut formulae in either input tree.
The legacy principal-formula argument is retained for source compatibility
but does not contribute to the textbook bound. -/
noncomputable def maxPredRank {L : Language} {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) : Nat :=
  max (maxPredRankTree T1) (maxPredRankTree T2)

/- Permanent contract regressions for the literal and ambient rank bounds. -/
/-- A structural classification of the root constructor used by the
Lemma 6.4.9 case split. Unlike a predicate on the conclusion sequent,
this records whether the proof itself is an equality leaf, a base-system
leaf, or an inference node. -/
inductive ReductionRootKind : Type where
  | baseAxiom
  | equalityAxiom
  | onePremise
  | twoPremise

/-- Lemma 6.4.9 (required def): A G1nnfEq proof tree T has no
essential cuts iff its essential cut-rank is 0. -/
@[blueprint "chap6__theorem_6_4_2"]
noncomputable def hasNoEssentialCuts {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) : Prop :=
  essentialCutRank T = 0

end G1nnfEqProofTree

-- ===================================================================
-- Lemma 6.4.9: Reduction lemma for G1nnf_equal
-- ===================================================================

/-- Lemma 6.4.9: (Reduction lemma for G1^nnf_=) Given G1nnfEq proofs
T1 of Gamma -> insert A Delta and T2 of insert A Lambda -> Theta, a
proof T of union Gamma Lambda -> union Delta Theta can be constructed
with essential-cut rank c(T) ≤ |A|, provided c(T1), c(T2) ≤ |A| and
no variable occurs both free and bound anywhere in the output sequent.

Adopted rank-only form (E-6.4.9-FORM). The printed depth clause is
erratum E-6.4.9: in instance B-02, the depth-0 equality axioms
T1 = s ≐ t, Ps → Pt and T2 = t ≐ r, Pt → Pr require a depth-2 proof
of s ≐ t, Ps, t ≐ r → Pr, exceeding the printed bound. -/
@[attach_debt, blueprint "chap6__lemma_6_4_9" (main := true)]
theorem g1nnfEq_reduction_lemma {L : Language} {hL : L.hasEquality = true}
    {Γ Δ Λ Θ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T₁ : G1nnfEqProofTree hL Γ (Finset.insert A Δ))
    (T₂ : G1nnfEqProofTree hL (Finset.insert A Λ) Θ)
    (hRank1 : T₁.essentialCutRank ≤ A.degree)
    (hRank2 : T₂.essentialCutRank ≤ A.degree)
    (hOut : finsetCrossNoFreeBound (Finset.union Γ Λ) (Finset.union Δ Θ)) :
    ∃ T : G1nnfEqProofTree hL (Finset.union Γ Λ) (Finset.union Δ Θ),
      T.essentialCutRank ≤ A.degree 

-- ===================================================================
-- Theorem 6.4.2: Cut elimination theorem for G1nnf_equal
-- ===================================================================

/-- Theorem 6.4.2: (Cut elimination theorem for G1^nnf_=) A G1nnfEq
proof T whose end sequent has no variable occurring both free and bound
can be converted to a proof T* without essential cuts, with
depth(T*) ≤ exp(m+2, c(T), depth(T)). The adopted literal reading of m
is `maxPredRankTree T`: the maximal rank of predicate symbols of literal
cut formulae in T, counting equality literals with rank 2. -/
@[attach_debt, blueprint "chap6__theorem_6_4_2" (main := true)]
theorem g1nnfEq_cut_elimination {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ)
    (m : Nat)
    (hm : m = G1nnfEqProofTree.maxPredRankTree T) :
    ∃ T_star : G1nnfEqProofTree hL Γ Δ,
      T_star.hasNoEssentialCuts ∧
      T_star.depth ≤
        iterExp (m + 2) T.essentialCutRank T.depth 

end LCS.CutElim.Hauptsatz.Equality
end
