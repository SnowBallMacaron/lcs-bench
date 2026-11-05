import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.FirstOrder.Semantics
import LCS.CutElim.Hauptsatz.Equality.Part1
import Attach
import LCS.CutElim.Hauptsatz.Equality.Part2.ProofsStamp

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality

/-- Definition 6.4.6 (companion): Concrete example of negation
closure. The sequent -> neg(s = t), f(s) = f(t) is an equality
axiom obtained by applying negRight to a funCong axiom, moving the
equality s_1 = t_1 from the antecedent to the succedent as
neg(s_1 = t_1). Here we construct this for a unary function symbol
f with terms s and t. -/
@[blueprint "chap6__definition_6_4_6"]
def g1nnfEqAxiomExample {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) (_hArity : L.funArity f = 1)
    (s t : Term L) : G1nnfEqAxiom L hL :=
  let ss : Fin (L.funArity f) → Term L := fun _ => s
  let ts : Fin (L.funArity f) → Term L := fun _ => t
  .negRight (.funCong f ss ts Finset.empty Finset.empty) (.eq_ hL s t)





end LCS.CutElim.Hauptsatz.Equality
end

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

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
/-- Lemma 6.4.8 (helper): Collect all formulae appearing in a
G1nnfEq proof tree (in all sequent positions). Returns a Finset
by unioning the antecedent and succedent at each node. -/
noncomputable def allFormulae {L : Language} {hL : L.hasEquality = true} :
    {Γ Δ : Finset (FormulaN L)} →
    G1nnfEqProofTree hL Γ Δ → Finset (FormulaN L)
  | _, _, .axiom_ rule Gamma Delta _ _ =>
    Finset.union (rule.conclusion Gamma Delta).1
                 (rule.conclusion Gamma Delta).2
  | _, _, .onePremise rule Gamma Delta _ _ sub =>
    Finset.union
      (Finset.union (rule.conclusion Gamma Delta).1
                    (rule.conclusion Gamma Delta).2)
      (allFormulae sub)
  | _, _, .twoPremise rule Gamma Delta _ _ sub1 sub2 =>
    Finset.union
      (Finset.union (rule.conclusion Gamma Delta).1
                    (rule.conclusion Gamma Delta).2)
      (Finset.union (allFormulae sub1) (allFormulae sub2))

end G1nnfEqProofTree
end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality

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

/-- Lemma 6.4.9 (required def): A cut is essential if it is not
inessential, i.e., its cut formula is not a literal equality
formula. Essential cuts are the ones eliminated by the cut
elimination theorem for G1nnf_equal. -/
@[blueprint "chap6__lemma_6_4_9"]
def isEssentialCut {L : Language} (A : FormulaN L) : Prop :=
  ¬ isInessentialCut A

end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport a proof tree across equal conclusion indices. -/
noncomputable def cast {L : Language} {hL : L.hasEquality = true}
    {Γ Δ Γ' Δ' : Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfEqProofTree hL Γ Δ) :
    G1nnfEqProofTree hL Γ' Δ' :=
  hΓ ▸ hΔ ▸ T

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transporting the conclusion indices does not change essential cut-rank. -/
theorem essentialCutRank_cast {L : Language} {hL : L.hasEquality = true}
    {Γ Δ Γ' Δ' : Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfEqProofTree hL Γ Δ) :
    essentialCutRank (cast hΓ hΔ T) = essentialCutRank T := by
  subst Γ'
  subst Δ'
  rfl

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The maximal predicate arity occurring anywhere in a formula. Equality is
treated as a distinguished binary predicate, and every logical constructor
propagates the maximum rank of its immediate subformulae. -/
@[simp]
def ambientFormulaPredRank {L : Language} : FormulaN L → Nat
  | .predN P _ => L.predArity P
  | .eq_ _ _ _ => 2
  | .neg A => ambientFormulaPredRank A
  | .conj A B =>
      max (ambientFormulaPredRank A) (ambientFormulaPredRank B)
  | .disj A B =>
      max (ambientFormulaPredRank A) (ambientFormulaPredRank B)
  | .impl A B =>
      max (ambientFormulaPredRank A) (ambientFormulaPredRank B)
  | .all _ A => ambientFormulaPredRank A
  | .ex _ A => ambientFormulaPredRank A





end G1nnfEqProofTree
end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality
namespace G1nnfEqRule

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The predicate-rank contribution of a rule's cut formula. Non-cut rules
contribute zero. -/
def ambientCutPredRank {L : Language} {hL : L.hasEquality = true}
    (rule : G1nnfEqRule L hL) : Nat :=
  match rule.cutFormula with
  | some A => G1nnfEqProofTree.ambientFormulaPredRank A
  | none => 0



end G1nnfEqRule
end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality
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



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

























-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A structural classification of the root constructor used by the
Lemma 6.4.9 case split. Unlike a predicate on the conclusion sequent,
this records whether the proof itself is an equality leaf, a base-system
leaf, or an inference node. -/
inductive ReductionRootKind : Type where
  | baseAxiom
  | equalityAxiom
  | onePremise
  | twoPremise

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Classify the actual root constructor of a G1nnfEq proof tree. -/
def reductionRootKind {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)} :
    G1nnfEqProofTree hL Γ Δ → ReductionRootKind
  | .axiom_ (.base _) _ _ _ _ => .baseAxiom
  | .axiom_ (.eqAxiom _) _ _ _ _ => .equalityAxiom
  | .onePremise _ _ _ _ _ _ => .onePremise
  | .twoPremise _ _ _ _ _ _ _ => .twoPremise

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The proof tree itself has an equality-axiom leaf at its root. -/
def IsEqualityAxiomRoot {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) : Prop :=
  reductionRootKind T = .equalityAxiom

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The proof tree itself has an ordinary base-system axiom leaf at its root. -/
def IsBaseAxiomRoot {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) : Prop :=
  reductionRootKind T = .baseAxiom

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The proof tree has a one- or two-premise inference at its root. -/
def IsInferenceRoot {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) : Prop :=
  reductionRootKind T = .onePremise ∨
    reductionRootKind T = .twoPremise





end G1nnfEqProofTree
end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality
namespace G1nnfEqProofTree

/-- Lemma 6.4.9 (required def): A G1nnfEq proof tree T has no
essential cuts iff its essential cut-rank is 0. -/
@[blueprint "chap6__theorem_6_4_2"]
noncomputable def hasNoEssentialCuts {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) : Prop :=
  essentialCutRank T = 0

end G1nnfEqProofTree
end LCS.CutElim.Hauptsatz.Equality
end

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality

/-- Lemma 6.4.8 (companion): In an LKe-proof, all weakenings can be
permuted above all other inferences. Input: an LKe-proof tree T of
some sequent Γ → Δ. Output: an LKe-proof tree T' of the SAME sequent
Γ → Δ together with a proof that `T'.isWeakeningNormalized` — i.e.
every `weakenLeft`/`weakenRight` in T' occurs immediately above an
axiom leaf, possibly through a chain of further weakenings. Textbook:
this is the first step of the Lem 6.4.8 proof sketch, "in an
LKe-proof, all weakenings can be moved above all other inferences."
Statement-level only; body sorry. -/
theorem g1nnfEq_weakening_permutation {L : Language}
    (Γ Δ : List (FormulaN L))
    (T : LCS.CutElim.LKe.LKeProofTree (LCS.FirstOrder.Gentzen.Sequent.mk Γ Δ)) :
    ∃ T' : LCS.CutElim.LKe.LKeProofTree
      (LCS.FirstOrder.Gentzen.Sequent.mk Γ Δ),
      T'.isWeakeningNormalized := by
-- BEGIN PROOF
  -- DEBT(Lemma 6.4.8 proof step: all weakenings of an LKe-proof moved above the other inferences; proof pending)
  sorry

/-- Lemma 6.4.8 (companion): Given an LKe-proof of a sequent whose
formulae are all in NNF, a G1nnf_=-proof of the corresponding
finset-sequent can be constructed. This is the "simulate LKe by
G1nnf_=" step of the Lem 6.4.8 textbook proof. Statement-level only;
body sorry. -/
theorem g1nnfEq_simulation_of_lke {L : Language} (hL : L.hasEquality = true)
    (Γ Δ : List (FormulaN L))
    (hNNFΓ : ∀ A ∈ Γ, FormulaN.isNNF A)
    (hNNFΔ : ∀ A ∈ Δ, FormulaN.isNNF A)
    (T : LCS.CutElim.LKe.LKeProofTree (LCS.FirstOrder.Gentzen.Sequent.mk Γ Δ)) :
    Nonempty (G1nnfEqProofTree hL (Γ.foldr Finset.insert ∅)
                               (Δ.foldr Finset.insert ∅)) := by
-- BEGIN PROOF
  -- DEBT(Lemma 6.4.8 proof step: an LKe-proof of a sequent in NNF simulated in G1nnf=; proof pending)
  sorry

/-- Lemma 6.4.8: (Completeness of G1^nnf_=) For the system G1nnf_equal,
every valid sequent is provable. -/
@[attach_debt, blueprint "chap6__lemma_6_4_8" (main := true)]
theorem g1nnfEq_completeness {L : Language} (hL : L.hasEquality = true)
    (Gamma Delta : Finset (FormulaN L))
    (hValid : ∀ A, A ∈ Gamma → FormulaN.isNNF A)
    (hValidD : ∀ A, A ∈ Delta → FormulaN.isNNF A)
    (hSeqValid : ∀ (M : Structure L) (val : Assignment M),
      (∀ A, A ∈ Gamma → formulaEvalN M A val) →
      (∃ A, A ∈ Delta ∧ formulaEvalN M A val)) :
    Nonempty (G1nnfEqProofTree hL Gamma Delta) 

-- ===================================================================
-- Lemma 6.4.9: Reduction lemma for G1nnf_equal
-- ===================================================================



/-- Reduction case where the left proof has an equality-axiom leaf at
its root and the right proof has an
ordinary base-system axiom leaf. The classifiers inspect proof constructors
and do not infer them from the shape of the conclusion sequent. -/
theorem g1nnfEq_reduction_case_eqAxiomLeft {L : Language} (hL : L.hasEquality = true)
    (A : FormulaN L)
    {Γ Δ Λ Θ : Finset (FormulaN L)}
    (T₁ : G1nnfEqProofTree hL Γ (Finset.insert A Δ))
    (T₂ : G1nnfEqProofTree hL (Finset.insert A Λ) Θ)
    (m : Nat)
    (hm : G1nnfEqProofTree.maxPredRank A T₁ T₂ ≤ m)
    (hEqAx : T₁.IsEqualityAxiomRoot)
    (hBaseAx : T₂.IsBaseAxiomRoot)
    (hRank1 : T₁.essentialCutRank ≤ A.degree)
    (hRank2 : T₂.essentialCutRank ≤ A.degree) :
    ∃ T : G1nnfEqProofTree hL (Finset.union Γ Λ) (Finset.union Δ Θ),
      T.essentialCutRank < A.degree + 1 ∧
      T.depth < T₁.depth + T₂.depth + m + 1 := by
  -- REPAIR(T6-33): proof pending
  sorry

/-- Reduction case where the right proof has an equality-axiom leaf at
its root and the left proof has an
ordinary base-system axiom leaf. -/
theorem g1nnfEq_reduction_case_eqAxiomRight {L : Language} (hL : L.hasEquality = true)
    (A : FormulaN L)
    {Γ Δ Λ Θ : Finset (FormulaN L)}
    (T₁ : G1nnfEqProofTree hL Γ (Finset.insert A Δ))
    (T₂ : G1nnfEqProofTree hL (Finset.insert A Λ) Θ)
    (m : Nat)
    (hm : G1nnfEqProofTree.maxPredRank A T₁ T₂ ≤ m)
    (hBaseAx : T₁.IsBaseAxiomRoot)
    (hEqAx : T₂.IsEqualityAxiomRoot)
    (hRank1 : T₁.essentialCutRank ≤ A.degree)
    (hRank2 : T₂.essentialCutRank ≤ A.degree) :
    ∃ T : G1nnfEqProofTree hL (Finset.union Γ Λ) (Finset.union Δ Θ),
      T.essentialCutRank < A.degree + 1 ∧
      T.depth < T₁.depth + T₂.depth + m + 1 := by
  -- REPAIR(T6-33): proof pending
  sorry

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

/-- Theorem 6.4.2 (companion): If no variable occurs both free and bound
anywhere in the end sequent and the essential cut-rank c(T) > 0,
a proof T' of the same sequent can be constructed with
c(T') < c(T) and depth(T') < (m+2)^depth(T), where m is the maximal
rank of literal-cut predicate symbols in T, counting equality literals
with rank 2. The parameter m is computed for this input tree. -/
theorem g1nnfEq_cut_rank_reduction {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ)
    (hPos : T.essentialCutRank > 0)
    (m : Nat)
    (hm : m = G1nnfEqProofTree.maxPredRankTree T) :
    ∃ T' : G1nnfEqProofTree hL Γ Δ,
      T'.essentialCutRank < T.essentialCutRank ∧
      T'.depth < (m + 2) ^ T.depth := by
  -- REPAIR(T6-33): proof pending (hand proof: feasibility-T6-78 §C.4)
  sorry

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

