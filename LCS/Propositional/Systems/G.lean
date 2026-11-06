import LCS.Item
import LCS.Util
import LCS.Propositional.Semantics
import Attach
import LCS.Propositional.Systems.G.ProofsStamp

/-! # Propositional.Systems.G
    Formalization of Chapter 3, Sections 3.4.1-3.4.5.
    Defines sequents, the Gentzen system G', axioms, deduction/proof trees,
    falsifiable/valid sequents, and soundness of G'.
-/

namespace LCS.Propositional.Systems.G

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics

-- ========= Definition 3.4.1: Sequents =========

/-- Definition 3.4.1: A sequent is a pair (Gamma, Delta) of finite
    (possibly empty) sequences of propositions. Gamma is the antecedent and
    Delta is the succedent. A sequent is denoted Gamma -> Delta.
    This type uses `PropFormulaNormalized` per the §3.4.2 standing
    assumption that restricts connectives to {∧, ∨, ⊃, ¬}. The concrete
    formula in Example 3.4.1 also belongs to this grammar. -/
@[blueprint "chap3__definition_3_4_1" (main := true)]
structure Sequent where
  antecedent : List PropFormulaNormalized
  succedent : List PropFormulaNormalized
  deriving DecidableEq, Repr

-- ========= Definition 3.4.2: The Gentzen System G' rules =========

/-- Definition 3.4.2: The one-premise inference rules of the Gentzen
    sequent calculus G'. Indexed by `(premise, conclusion) : Sequent × Sequent`
    so each constructor enforces the structural relationship between premise
    and conclusion — the premise/conclusion sequents are not free parameters
    but are determined by the formula/context inputs per the rule shape.

    The 5 one-premise rules (mirroring the textbook rules that have a
    single upper sequent):
    - andLeft:   Γ, A, B, Δ → Λ     ⊢   Γ, A ∧ B, Δ → Λ
    - orRight:   Γ → Δ, A, B, Λ     ⊢   Γ → Δ, A ∨ B, Λ
    - implRight: A, Γ → B, Δ, Λ     ⊢   Γ → Δ, A ⊃ B, Λ
    - negLeft:   Γ, Δ → A, Λ        ⊢   Γ, ¬A, Δ → Λ
    - negRight:  A, Γ → Δ, Λ        ⊢   Γ → Δ, ¬A, Λ

    Paired with `GentzenStep2` (two-premise rules) below. Together they
    cover all 8 textbook rules of G'. -/
@[blueprint "chap3__definition_3_4_2" (main := true)]
inductive GentzenStep1 : Sequent → Sequent → Type where
  | andLeft (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep1 (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [.conj A B] ++ Δ) Λ)
  | orRight (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep1 (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [.disj A B] ++ Λ))
  | implRight (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep1 (Sequent.mk ([A] ++ Γ) (B :: (Δ ++ Λ)))
                    (Sequent.mk Γ (Δ ++ [.impl A B] ++ Λ))
  | negLeft (Γ Δ Λ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      GentzenStep1 (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk (Γ ++ [.neg A] ++ Δ) Λ)
  | negRight (Γ Δ Λ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      GentzenStep1 (Sequent.mk ([A] ++ Γ) (Δ ++ Λ))
                    (Sequent.mk Γ (Δ ++ [.neg A] ++ Λ))

/-- Definition 3.4.2 (companion): The three two-premise inference rules
    of G' — indexed by `(premise1, premise2, conclusion) : Sequent × Sequent × Sequent`.

    The 3 two-premise rules:
    - andRight: Γ → Δ, A, Λ   and   Γ → Δ, B, Λ     ⊢   Γ → Δ, A ∧ B, Λ
    - orLeft:   Γ, A, Δ → Λ   and   Γ, B, Δ → Λ     ⊢   Γ, A ∨ B, Δ → Λ
    - implLeft: Γ, Δ → A, Λ   and   B, Γ, Δ → Λ     ⊢   Γ, A ⊃ B, Δ → Λ

    Companion of `GentzenStep1` (one-premise). -/
@[blueprint "chap3__definition_3_4_2" (main := true)]
inductive GentzenStep2 : Sequent → Sequent → Sequent → Type where
  | andRight (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep2 (Sequent.mk Γ (Δ ++ [A] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [.conj A B] ++ Λ))
  | orLeft (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep2 (Sequent.mk (Γ ++ [A] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [.disj A B] ++ Δ) Λ)
  | implLeft (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      GentzenStep2 (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk ([B] ++ Γ ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [.impl A B] ++ Δ) Λ)

-- ========= Definition 3.4.5 (indexed): Proof Trees indexed by conclusion =========

/-- Definition 3.4.5: Proof trees indexed by their conclusion sequent, the
    least set of trees with axiom leaves and closed under G' rules. -/
@[blueprint "chap3__definition_3_4_5" (main := true)]
inductive ProofTree : Sequent → Type where
  | axiom_ (s : Sequent)
      (h : ∃ A : PropFormulaNormalized, A ∈ s.antecedent ∧ A ∈ s.succedent) : ProofTree s
  | onePremise {prem conc : Sequent}
      (rule : GentzenStep1 prem conc)
      (t : ProofTree prem) : ProofTree conc
  | twoPremise {prem1 prem2 conc : Sequent}
      (rule : GentzenStep2 prem1 prem2 conc)
      (t1 : ProofTree prem1) (t2 : ProofTree prem2) : ProofTree conc

-- ========= Definition 3.4.5: Deduction Trees =========

/-- Definition 3.4.5 (companion): Indexed deduction trees — the least set
    of trees closed under the G' rules with FREE-FORM leaves (i.e. not
    forced to be axioms). Textbook Def 3.4.5:
    "The set of deduction trees is defined inductively as the least set of
    trees containing all one-node trees (not necessarily labeled with an
    axiom)."
    Parallel of `ProofTree` (indexed, axiom-forced) — proof trees are
    precisely the deduction trees whose leaves are all axioms. -/
@[blueprint "chap3__definition_3_4_5"]
inductive DeductionTree : Sequent → Type where
  | leaf (s : Sequent) : DeductionTree s
  | onePremise {prem conc : Sequent}
      (rule : GentzenStep1 prem conc)
      (t : DeductionTree prem) : DeductionTree conc
  | twoPremise {p1 p2 conc : Sequent}
      (rule : GentzenStep2 p1 p2 conc)
      (t1 : DeductionTree p1) (t2 : DeductionTree p2) :
      DeductionTree conc

-- ========= Definition 3.4.3: Falsifiable and Valid Sequents =========

/-- Definition 3.4.3: A sequent A1, ..., Am -> B1, ..., Bn is falsifiable
    iff there exists a valuation v such that v makes all Ai true and all
    Bj false. -/
@[blueprint "chap3__definition_3_4_3" (main := true)]
def sequentFalsifiable (s : Sequent) : Prop :=
  ∃ v : Valuation,
    (∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) ∧
    (∀ B ∈ s.succedent, evalExtN v B = BoolVal.F)

/-- Definition 3.4.3: A sequent A1, ..., Am -> B1, ..., Bn is valid iff
    for every valuation v, if all Ai are true then some Bj is true. -/
@[blueprint "chap3__definition_3_4_3" (main := true)]
def sequentValid (s : Sequent) : Prop :=
  ∀ v : Valuation,
    (∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) →
    (∃ B, B ∈ s.succedent ∧ evalExtN v B = BoolVal.T)

-- ========= Definition 3.4.4: Axioms =========

/-- Definition 3.4.4: An axiom is any sequent Gamma -> Delta such that
    Gamma and Delta contain some common proposition. -/
@[blueprint "chap3__definition_3_4_4" (main := true)]
def isAxiom (s : Sequent) : Prop :=
  ∃ A : PropFormulaNormalized, A ∈ s.antecedent ∧ A ∈ s.succedent

-- ========= Definition 3.4.5 (companion defs): Conclusion, Provable, Counter-Example =========

namespace ProofTree

/-- Definition 3.4.5 (companion): Returns the sequent labeling the root of
    the indexed proof tree (the type index). -/
@[blueprint "chap3__definition_3_4_5" (main := true)]
def conclusion {s : Sequent} (_ : ProofTree s) : Sequent := s

end ProofTree

/-- Definition 3.4.5: A sequent is provable iff there exists a proof tree
    of which it is the conclusion. -/
@[blueprint "chap3__definition_3_4_5" (main := true)]
def sequentProvable (s : Sequent) : Prop :=
  Nonempty (ProofTree s)

namespace DeductionTree

/-- Definition 3.4.5 (companion): Returns the sequent labeling the root of
    the indexed deduction tree (the type index). -/
@[blueprint "chap3__definition_3_4_5" (main := true)]
def conclusion {s : Sequent} (_ : DeductionTree s) : Sequent := s

/-- Definition 3.4.5 (companion): Collects all leaf sequents of a
    deduction tree. -/
@[blueprint "chap3__definition_3_4_5"]
def leaves : {s : Sequent} → DeductionTree s → List Sequent
  | _, .leaf s => [s]
  | _, .onePremise _ t => t.leaves
  | _, .twoPremise _ t1 t2 => t1.leaves ++ t2.leaves

/-- Definition 3.4.5 (companion): A deduction tree is a proof (tree) when
    all of its leaves are axioms. -/
@[blueprint "chap3__definition_3_4_5"]
def isProof : {s : Sequent} → DeductionTree s → Prop
  | _, .leaf s => isAxiom s
  | _, .onePremise _ t => t.isProof
  | _, .twoPremise _ t1 t2 => t1.isProof ∧ t2.isProof

/-- Definition 3.4.5 (companion): Convert a deduction tree whose leaves
    are all axioms into a proof tree with the same conclusion. -/
@[blueprint "chap3__definition_3_4_5"]
def toProofTree : {s : Sequent} → (dt : DeductionTree s) → dt.isProof →
    ProofTree s
  | _, .leaf s, h => ProofTree.axiom_ s h
  | _, .onePremise rule t, h =>
      ProofTree.onePremise rule (t.toProofTree h)
  | _, .twoPremise rule t1 t2, h =>
      ProofTree.twoPremise rule (t1.toProofTree h.1) (t2.toProofTree h.2)

/-- Definition 3.4.5 (companion): A sequent consists only of propositional
    variables in both antecedent and succedent. -/
@[blueprint "chap3__definition_3_4_5"]
def allVars (s : Sequent) : Prop :=
  (∀ A ∈ s.antecedent, ∃ n, A = PropFormulaNormalized.var n) ∧
  (∀ B ∈ s.succedent, ∃ n, B = PropFormulaNormalized.var n)

/-- Definition 3.4.5 (companion): The antecedent and succedent of a sequent
    are disjoint (share no common formula). -/
@[blueprint "chap3__definition_3_4_5"]
def disjointSequent (s : Sequent) : Prop :=
  ∀ A : PropFormulaNormalized, A ∈ s.antecedent → A ∉ s.succedent

/-- Definition 3.4.5: A counter-example tree is a deduction tree with some
    leaf whose antecedent/succedent are disjoint propositional variables. -/
@[blueprint "chap3__definition_3_4_5" (main := true)]
def isCounterExample {s : Sequent} (dt : DeductionTree s) : Prop :=
  ∃ s' ∈ dt.leaves, allVars s' ∧ disjointSequent s'

end DeductionTree

-- ========= Example 3.4.1: Falsification Search =========

/-- Example 3.4.1: The formula (P => Q) => (neg Q => neg P), used to
    demonstrate the falsification search procedure. -/
@[blueprint "chap3__example_3_4_1" (main := true)]
def exFalsificationSearchFormula : PropFormulaNormalized :=
  .impl (.impl (.var 0) (.var 1)) (.impl (.neg (.var 1)) (.neg (.var 0)))

/-- Example 3.4.1 (companion): The initial sequent -> A for attempting
    to falsify the contrapositive formula. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchInitialSequent : Sequent :=
  Sequent.mk [] [exFalsificationSearchFormula]

/-- The implication decompositions used in the informal search of Example
    3.4.1. The succedent replacement stays in its original position, and the
    antecedent side formula is appended, as in the displayed early example.
    The indexed constructors enforce the parent/child formula relationships.
    The later G′ calculus specifies different insertion positions. -/
@[blueprint "chap3__example_3_4_1"]
inductive InformalImplicationTree : Sequent → Type where
  | leaf (s : Sequent) : InformalImplicationTree s
  | implRight (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized)
      (t : InformalImplicationTree ⟨Γ ++ [A], Δ ++ [B] ++ Λ⟩) :
      InformalImplicationTree ⟨Γ, Δ ++ [.impl A B] ++ Λ⟩
  | implLeft (Γ Δ Λ : List PropFormulaNormalized) (A B : PropFormulaNormalized)
      (t₁ : InformalImplicationTree ⟨Γ ++ Δ, A :: Λ⟩)
      (t₂ : InformalImplicationTree ⟨B :: (Γ ++ Δ), Λ⟩) :
      InformalImplicationTree ⟨Γ ++ [.impl A B] ++ Δ, Λ⟩

namespace InformalImplicationTree

/-- The terminal sequents of the informal implication search. -/
@[blueprint "chap3__example_3_4_1"]
def leaves : {s : Sequent} → InformalImplicationTree s → List Sequent
  | _, .leaf s => [s]
  | _, .implRight _ _ _ _ _ t => t.leaves
  | _, .implLeft _ _ _ _ _ t₁ t₂ => t₁.leaves ++ t₂.leaves

end InformalImplicationTree

/-- Example 3.4.1: The initial one-node tree. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchStage0 :
    InformalImplicationTree exFalsificationSearchInitialSequent :=
  .leaf exFalsificationSearchInitialSequent

/-- Example 3.4.1: Decompose the outer implication. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchStage1 :
    InformalImplicationTree exFalsificationSearchInitialSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  .implRight [] [] [] (.impl p q) (.impl (.neg q) (.neg p))
    (.leaf ⟨[.impl p q], [.impl (.neg q) (.neg p)]⟩)

/-- Example 3.4.1: Split on the true implication P ⊃ Q. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchStage2 :
    InformalImplicationTree exFalsificationSearchInitialSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  .implRight [] [] [] (.impl p q) (.impl (.neg q) (.neg p))
    (.implLeft [] [] [.impl (.neg q) (.neg p)] p q
      (.leaf ⟨[], [p, .impl (.neg q) (.neg p)]⟩)
      (.leaf ⟨[q], [.impl (.neg q) (.neg p)]⟩))

/-- Example 3.4.1: Expand the leftmost leaf while retaining the right leaf. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchStage3 :
    InformalImplicationTree exFalsificationSearchInitialSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  .implRight [] [] [] (.impl p q) (.impl (.neg q) (.neg p))
    (.implLeft [] [] [.impl (.neg q) (.neg p)] p q
      (.implRight [] [p] [] (.neg q) (.neg p)
        (.leaf ⟨[.neg q], [p, .neg p]⟩))
      (.leaf ⟨[q], [.impl (.neg q) (.neg p)]⟩))

/-- Example 3.4.1: The displayed search first splits on the true P ⊃ Q,
    then decomposes ¬Q ⊃ ¬P on each branch. Its terminal sequents are
    ¬Q → P, ¬P and Q, ¬Q → ¬P, closed by semantic contradiction. -/
@[blueprint "chap3__example_3_4_1"]
def exFalsificationSearchTree :
    InformalImplicationTree exFalsificationSearchInitialSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  .implRight [] [] [] (.impl p q) (.impl (.neg q) (.neg p))
    (.implLeft [] [] [.impl (.neg q) (.neg p)] p q
      (.implRight [] [p] [] (.neg q) (.neg p)
        (.leaf ⟨[.neg q], [p, .neg p]⟩))
      (.implRight [q] [] [] (.neg q) (.neg p)
        (.leaf ⟨[q, .neg q], [.neg p]⟩)))

/-- Example 3.4.1: Both displayed terminal sequents are unfalsifiable. -/
@[blueprint "chap3__example_3_4_1"]
theorem exFalsificationSearchLeavesClosed :
    ∀ s ∈ exFalsificationSearchTree.leaves, ¬sequentFalsifiable s 

-- ========= Example 3.4.2: Implies Left Rule Instance =========

/-- Example 3.4.2: The displayed implication-left instance, with arbitrary
    extra propositions A, B, D and propositional symbols P, Q. -/
@[blueprint "chap3__example_3_4_2" (main := true)]
def exImplLeftRuleInstance (A B D : PropFormulaNormalized) (p q : Nat) :
    GentzenStep2
      (Sequent.mk [A, B] [.var p, D])
      (Sequent.mk [.var q, A, B] [D])
      (Sequent.mk [A, .impl (.var p) (.var q), B] [D]) :=
  GentzenStep2.implLeft [A] [B] [D] (.var p) (.var q)

-- ========= Example 3.4.3: Proof Tree and Counter-Example Tree =========

/-- Example 3.4.3: The displayed proof tree first branches on P ⊃ Q.
    Its left branch is P, ¬Q → P; ¬Q → ¬P, P; → P, ¬Q ⊃ ¬P.
    Its right branch is Q → Q, ¬P; ¬Q, Q → ¬P; Q → ¬Q ⊃ ¬P.
    The branching subtree concludes P ⊃ Q → ¬Q ⊃ ¬P, and the final
    implication-right rule concludes → (P ⊃ Q) ⊃ (¬Q ⊃ ¬P). -/
@[blueprint "chap3__example_3_4_3" (main := true)]
def exProofTreeContrapositive :
    ProofTree (Sequent.mk [] [exFalsificationSearchFormula]) :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let leftAxiom : ProofTree ⟨[p, .neg q], [p]⟩ :=
    .axiom_ _ ⟨p, by simp, by simp⟩
  let leftNeg : ProofTree ⟨[.neg q], [.neg p, p]⟩ :=
    .onePremise (.negRight [.neg q] [] [p] p) leftAxiom
  let leftBranch : ProofTree ⟨[], [p, .impl (.neg q) (.neg p)]⟩ :=
    .onePremise (.implRight [] [p] [] (.neg q) (.neg p)) leftNeg
  let rightAxiom : ProofTree ⟨[q], [q, .neg p]⟩ :=
    .axiom_ _ ⟨q, by simp, by simp⟩
  let rightNeg : ProofTree ⟨[.neg q, q], [.neg p]⟩ :=
    .onePremise (.negLeft [] [q] [.neg p] q) rightAxiom
  let rightBranch : ProofTree ⟨[q], [.impl (.neg q) (.neg p)]⟩ :=
    .onePremise (.implRight [q] [] [] (.neg q) (.neg p)) rightNeg
  let subtree : ProofTree ⟨[.impl p q], [.impl (.neg q) (.neg p)]⟩ :=
    .twoPremise (.implLeft [] [] [.impl (.neg q) (.neg p)] p q)
      leftBranch rightBranch
  .onePremise (.implRight [] [] [] (.impl p q) (.impl (.neg q) (.neg p)))
    subtree

/-- Example 3.4.3: A counter-example tree for → (P⊃Q) ∧ (¬P⊃¬Q), whose
    leaf P→Q has disjoint atomic antecedent/succedent (falsifying).

    Tree shape (upward):
      Leaf1: P → Q              (disjoint atoms — counter-example)
      Leaf2: Q → P              (disjoint atoms — counter-example)
      impl:right on Leaf1 → → P⊃Q
      neg:left on Leaf2 → ¬P, Q →
      neg:right → ¬P → ¬Q
      impl:right → → ¬P⊃¬Q
      and:right combines both → → (P⊃Q) ∧ (¬P⊃¬Q) -/
@[blueprint "chap3__example_3_4_3" (main := true)]
def exCounterExampleTreeConjunction :
    DeductionTree (Sequent.mk [] [.conj
      (.impl (PropFormulaNormalized.var 0) (PropFormulaNormalized.var 1))
      (.impl (.neg (PropFormulaNormalized.var 0))
             (.neg (PropFormulaNormalized.var 1)))]) :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let counterLeaf1 : Sequent := Sequent.mk [p] [q]
  let counterLeaf2 : Sequent := Sequent.mk [q] [p]
  let tCounterLeaf1 : DeductionTree counterLeaf1 :=
    DeductionTree.leaf counterLeaf1
  let tCounterLeaf2 : DeductionTree counterLeaf2 :=
    DeductionTree.leaf counterLeaf2
  -- premise1 tree: from P → Q infer → P⊃Q
  let tPrem1 : DeductionTree (Sequent.mk [] [.impl p q]) :=
    DeductionTree.onePremise
      (GentzenStep1.implRight [] [] [] p q) tCounterLeaf1
  -- premise2 tree: from Q → P (neg:left on ¬P) → Q, ¬P → (neg:right) →
  --                ¬P → ¬Q (impl:right) → → ¬P⊃¬Q
  let tNegLeft : DeductionTree (Sequent.mk [q, .neg p] []) :=
    DeductionTree.onePremise
      (GentzenStep1.negLeft [q] [] [] p) tCounterLeaf2
  let tNegRight : DeductionTree (Sequent.mk [.neg p] [.neg q]) :=
    DeductionTree.onePremise
      (GentzenStep1.negRight [.neg p] [] [] q) tNegLeft
  let tPrem2 : DeductionTree (Sequent.mk [] [.impl (.neg p) (.neg q)]) :=
    DeductionTree.onePremise
      (GentzenStep1.implRight [] [] [] (.neg p) (.neg q)) tNegRight
  -- and:right combining both
  DeductionTree.twoPremise
    (GentzenStep2.andRight [] [] [] (.impl p q) (.impl (.neg p) (.neg q)))
    tPrem1 tPrem2

-- ========= Example 3.4.2 (companion mains: principal / side / extra) =========

/-- Example 3.4.2: The principal formula occupies the middle position
    in the conclusion's antecedent. -/
@[blueprint "chap3__example_3_4_2" (main := true)]
theorem exImplLeftPrincipal (A B D : PropFormulaNormalized) (p q : Nat) :
    (PropFormulaNormalized.impl (.var p) (.var q)) ∈
      (Sequent.mk [A, .impl (.var p) (.var q), B] [D]).antecedent 

/-- Example 3.4.2: P is the first succedent formula of premise one;
    Q is the first antecedent formula of premise two. -/
@[blueprint "chap3__example_3_4_2" (main := true)]
theorem exImplLeftSideFormulae (A B D : PropFormulaNormalized) (p q : Nat) :
    (PropFormulaNormalized.var p) ∈ (Sequent.mk [A, B] [.var p, D]).succedent ∧
    (PropFormulaNormalized.var q) ∈ (Sequent.mk [.var q, A, B] [D]).antecedent 

/-- Example 3.4.2: The extra formulae A, B, D occur unchanged in
    both premises and the conclusion. -/
@[blueprint "chap3__example_3_4_2" (main := true)]
theorem exImplLeftExtraFormulae (A B D : PropFormulaNormalized) (p q : Nat) :
    let conc : Sequent := Sequent.mk [A, .impl (.var p) (.var q), B] [D]
    let prem1 : Sequent := Sequent.mk [A, B] [.var p, D]
    let prem2 : Sequent := Sequent.mk [.var q, A, B] [D]
    (A ∈ conc.antecedent ∧ B ∈ conc.antecedent ∧ D ∈ conc.succedent) ∧
    (A ∈ prem1.antecedent ∧ B ∈ prem1.antecedent ∧ D ∈ prem1.succedent) ∧
    (A ∈ prem2.antecedent ∧ B ∈ prem2.antecedent ∧ D ∈ prem2.succedent) 

-- ========= Lemma 3.4.1: Rule Falsification Iff (helpers + indexed versions) =========

-- Helpers for membership in (Γ ++ [x]) ++ Δ








-- Helpers for membership in (Γ ++ [A, B]) ++ Δ (two-element insert)










-- Helpers for ∃ in singleton/pair lists











-- ========= Lemma 3.4.2: Axiom Validity =========

/-- Lemma 3.4.2: Every axiom sequent is valid. If isAxiom s, then
    sequentValid s. Equivalently, no axiom is falsifiable. -/
@[blueprint "chap3__lemma_3_4_2" (main := true)]
theorem axiom_valid (s : Sequent) (h : isAxiom s) : sequentValid s 

-- ========= Lemma 3.4.3: Soundness of G' =========

-- Helper: each one-premise indexed step preserves validity


-- Helper: each two-premise indexed step preserves validity


-- Soundness by induction on indexed ProofTree


/-- Lemma 3.4.3: Soundness of the system G'. If a sequent is provable
    (there exists a proof tree with that sequent as conclusion), then
    it is valid. -/
@[blueprint "chap3__lemma_3_4_3" (main := true)]
theorem soundness_G (s : Sequent) (h : sequentProvable s) :
    sequentValid s 

end LCS.Propositional.Systems.G
