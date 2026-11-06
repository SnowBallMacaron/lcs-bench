import LCS.Item
import LCS.Util
import LCS.Propositional.Syntax
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.NormalForms
import Attach
import LCS.Resolution.GCNF.ProofsStamp

/-! # Resolution.GCNF (Section 4.2)
    Source: Logic for Computer Science, Gallier 2015

    The special Gentzen system GCNF' for sequents in conjunctive normal form.
    Defines literals (as pos/neg of Nat), clauses (as Finsets of literals),
    clause sequents, trivial/nontrivial sequents, and the GCNF' proof system.
-/

namespace LCS.Resolution.GCNF

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.NormalForms

-- ========= Definition 4.2.1: Literals, Clauses, Clause Sequents =========

/-- Definition 4.2.1: A literal is either a propositional symbol (pos P)
    or its negation (neg P). -/
@[blueprint "chap4__definition_4_2_1" (main := true)]
inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving DecidableEq, Repr

/-- Definition 4.2.1: A clause is a (finite) set of literals, representing
    a disjunction B_{i,1} v ... v B_{i,n_i}. -/
@[blueprint "chap4__definition_4_2_1" (main := true)]
abbrev Clause := LCS.Finset Literal

/-- Definition 4.2.1 (companion def): The empty clause, containing no literals. -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.empty : Clause := LCS.Finset.empty

/-- The ordinary §4.2 clause domain; resolution also uses the empty carrier value. -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.isOrdinary (C : Clause) : Prop := C ≠ Clause.empty

/-- Definition 4.2.1 (companion def): Singleton clause containing exactly one literal. -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.single (L : Literal) : Clause := LCS.Finset.singleton L

/-- Definition 4.2.1 (companion def): Convert a list of literals to a clause (set). -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.ofList (L : List Literal) : Clause := LCS.Finset.ofList L

/-- Definition 4.2.1 (companion theorem): Clause.single L equals Clause.ofList [L]. -/
@[blueprint "chap4__definition_4_2_1"]
theorem Clause.single_eq_ofList_singleton (L : Literal) :
    Clause.single L = Clause.ofList [L] 

/-- Definition 4.2.1 (companion theorem): Clause.ofList [L] equals Clause.single L. -/
@[blueprint "chap4__definition_4_2_1"]
theorem Clause.ofList_singleton_eq_single (L : Literal) :
    Clause.ofList [L] = Clause.single L 

/-- Definition 4.2.1 (companion def): Union of two clauses. -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.union (C1 C2 : Clause) : Clause := LCS.Finset.union C1 C2

/-- Definition 4.2.1 (companion def): Remove a literal from a clause. -/
@[blueprint "chap4__definition_4_2_1"]
def Clause.remove (C : Clause) (L : Literal) : Clause := LCS.Finset.erase C L

/-- Definition 4.2.1 (companion type): A clause sequent C_1, ..., C_n -> is a
    set of clauses, with comma interpreted as conjunction. -/
@[blueprint "chap4__definition_4_2_1"]
abbrev ClauseSequent := LCS.Finset Clause

/-- Every antecedent clause is an ordinary nonempty literal disjunction. -/
@[blueprint "chap4__definition_4_2_1"]
def ClauseSequent.isOrdinary (S : ClauseSequent) : Prop :=
  ∀ C ∈ S, C.isOrdinary

/-- Definition 4.2.3 (companion def): Singleton clause sequent containing one clause. -/
@[blueprint "chap4__definition_4_2_3"]
def ClauseSequent.single (C : Clause) : ClauseSequent :=
  LCS.Finset.singleton C

/-- Definition 4.2.3 (companion def): Image of a clause sequent under a function. -/
@[blueprint "chap4__definition_4_2_3"]
def ClauseSequent.mapSet (As : ClauseSequent) (f : Clause → Clause) : ClauseSequent :=
  LCS.Finset.image f As

/-- Definition 4.2.1 (companion def): Convert a list of clauses to a clause sequent. -/
@[blueprint "chap4__definition_4_2_1"]
def ClauseSequent.ofList (L : List Clause) : ClauseSequent :=
  LCS.Finset.ofList L

-- ========= Definition 4.2.3: The System GCNF' =========

/-- Definition 4.2.3 (companion def): Adds a literal B to a clause A, forming
    the clause (A_i v B). -/
@[blueprint "chap4__definition_4_2_3"]
def clauseWithLiteral (A : Clause) (B : Literal) : Clause :=
  LCS.Finset.insert B A

theorem Clause.ordinary_of_mem {C : Clause} {L : Literal} (h : L ∈ C) : C.isOrdinary := by
  intro hEmpty
  exact LCS.Finset.not_mem_empty (hEmpty ▸ h)

@[blueprint "chap4__definition_4_2_1", simp] theorem Clause.single_ordinary (L : Literal) : (Clause.single L).isOrdinary 

@[blueprint "chap4__definition_4_2_1", simp] theorem Clause.ofList_cons_ordinary (L : Literal) (ls : List Literal) :
    (Clause.ofList (L :: ls)).isOrdinary 

@[blueprint "chap4__definition_4_2_1"]
theorem ClauseSequent.ordinary_subset {S T : ClauseSequent}
    (h : S.isOrdinary) (hSub : LCS.Finset.Subset T S) : T.isOrdinary 

@[blueprint "chap4__definition_4_2_1"]
theorem ClauseSequent.ordinary_union {S T : ClauseSequent}
    (hS : S.isOrdinary) (hT : T.isOrdinary) : ClauseSequent.isOrdinary (LCS.Finset.union S T) 

@[blueprint "chap4__definition_4_2_1"]
theorem ClauseSequent.ordinary_single {C : Clause} (h : C.isOrdinary) :
    (ClauseSequent.single C).isOrdinary 

@[blueprint "chap4__definition_4_2_1"]
theorem ClauseSequent.ordinary_ofList {cs : List Clause}
    (h : ∀ C ∈ cs, C.isOrdinary) : ClauseSequent.isOrdinary (LCS.Finset.ofList cs) 

@[blueprint "chap4__definition_4_2_3", simp] theorem clauseWithLiteral_single (A B : Literal) :
    clauseWithLiteral (Clause.single A) B = Clause.ofList [A, B] 

@[blueprint "chap4__definition_4_2_3"]
theorem clauseWithLiteral_ofList (L : Literal) (ls : List Literal) :
    clauseWithLiteral (Clause.ofList ls) L = Clause.ofList (ls ++ [L]) 

@[blueprint "chap4__definition_4_2_1"]
theorem clauseOfList_swap (L M : Literal) :
    Clause.ofList [L, M] = Clause.ofList [M, L] 

/-- Definition 4.2.3: A proof tree in the system GCNF', with axioms =
    trivial sequents and one inference rule. -/
@[blueprint "chap4__definition_4_2_3" (main := true)]
inductive GCNFProofTree : ClauseSequent → Type where
  | axiom_ (S : ClauseSequent)
      (hOrdinary : S.isOrdinary)
      (hTriv : ∃ P : Nat, Clause.single (Literal.pos P) ∈ S ∧ Clause.single (Literal.neg P) ∈ S)
    : GCNFProofTree S
  | rule
      (Gamma : ClauseSequent)
      (As : ClauseSequent)
      (B : Literal)
      (Cs : ClauseSequent)
      (Gamma1 Gamma2 : ClauseSequent)
      (hGamma : Gamma.isOrdinary)
      (hAs : As.isOrdinary)
      (leftTree : GCNFProofTree (LCS.Finset.union Gamma1 Cs))
      (rightTree : GCNFProofTree (LCS.Finset.union Gamma2 (ClauseSequent.single (Clause.single B))))
      (hCsNonempty : ∃ C, C ∈ Cs)
      (hCsSub : LCS.Finset.Subset Cs As)
      (hG1Sub : LCS.Finset.Subset Gamma1 (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))))
      (hG2Sub : LCS.Finset.Subset Gamma2 (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))))
    : GCNFProofTree (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))

@[blueprint "chap4__definition_4_2_3"]
theorem GCNFProofTree.ordinary : {S : ClauseSequent} → GCNFProofTree S → S.isOrdinary
  

-- ========= Definition 4.2.1 (companion defs): Conjugate, Satisfaction =========

namespace Literal

/-- Definition 4.2.1: The conjugate of a literal L. If L = pos P then
    L-bar = neg P, and if L = neg P then L-bar = pos P. -/
@[blueprint "chap4__definition_4_2_1" (main := true)]
def conjugate : Literal → Literal
  | .pos P => .neg P
  | .neg P => .pos P

/-- Definition 4.2.1 (companion def): A literal is satisfied by a valuation
    v iff: pos P ↦ v P = true, neg P ↦ v P = false. -/
@[blueprint "chap4__definition_4_2_1"]
def satisfiedBy : Literal → (Nat → Bool) → Prop
  | .pos P, v => v P = true
  | .neg P, v => v P = false

end Literal

-- ========= Clause and ClauseSequent satisfaction =========

namespace Clause

/-- Definition 4.2.1 (companion def): A clause (disjunction of literals) is
    satisfied by v iff at least one literal in the clause is satisfied. -/
@[blueprint "chap4__definition_4_2_1"]
def satisfiedBy (C : Clause) (v : Nat → Bool) : Prop :=
  ∃ L ∈ C, Literal.satisfiedBy L v

end Clause

namespace ClauseSequent

/-- Definition 4.2.1 (companion def): A clause sequent is satisfied by v iff
    every clause in the sequent is satisfied by v. -/
@[blueprint "chap4__definition_4_2_1"]
def satisfiedBy (S : ClauseSequent) (v : Nat → Bool) : Prop :=
  ∀ C ∈ S, Clause.satisfiedBy C v

/-- Definition 4.2.1 (companion def): A clause sequent is valid iff no valuation
    satisfies all its clauses (unsatisfiability of the conjunction). -/
@[blueprint "chap4__definition_4_2_1"]
def isValid (S : ClauseSequent) : Prop :=
  ¬ ∃ v : Nat → Bool, satisfiedBy S v

/-- Truth of the empty-succedent sequent, as opposed to its antecedent conjunction. -/
@[blueprint "chap4__lemma_4_2_1"]
def sequentSatisfiedBy (S : ClauseSequent) (v : Nat → Bool) : Prop :=
  ¬ satisfiedBy S v

end ClauseSequent

-- ========= Definition 4.2.2: Trivial and Nontrivial Sequents =========

namespace ClauseSequent

/-- Definition 4.2.2: A sequent C_1, ..., C_n -> is trivial if it contains
    both the singleton clause [pos P] and [neg P] for some letter P. -/
@[blueprint "chap4__definition_4_2_2" (main := true)]
def isTrivial (S : ClauseSequent) : Prop :=
  ∃ P : Nat, Clause.single (Literal.pos P) ∈ S ∧ Clause.single (Literal.neg P) ∈ S

/-- Definition 4.2.2: A sequent is nontrivial iff it is not trivial. -/
@[blueprint "chap4__definition_4_2_2" (main := true)]
def isNontrivial (S : ClauseSequent) : Prop :=
  ¬ isTrivial S

end ClauseSequent

-- ========= Definition 4.2.3 (companion defs): clauseWithLiteral, conclusion =========

namespace GCNFProofTree

/-- Definition 4.2.3 (companion def): The clause sequent labeling the root
    (conclusion) of a GCNF' proof tree. -/
@[blueprint "chap4__definition_4_2_3"]
def conclusion {S : ClauseSequent} (_ : GCNFProofTree S) : ClauseSequent :=
  S

/-- Theorem 4.2.1 (companion def): A GCNF' proof tree has minimal axioms iff every
    axiom leaf is an exact complementary pair [pos P], [neg P] →. -/
@[blueprint "chap4__theorem_4_2_1"]
def axiomsMinimal : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ S _ _ => ∃ P : Nat,
      S = LCS.Finset.ofList [Clause.single (Literal.pos P), Clause.single (Literal.neg P)]
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _ =>
    axiomsMinimal left ∧ axiomsMinimal right

/-- Lemma 9.2.1 (companion): A GCNF'-proof has literal-only axioms
    iff every axiom leaf contains only single-literal clauses (i.e., every
    clause C in the axiom's sequent S satisfies ∃ L, C = Clause.single L).
    This is the textbook's condition "all axioms consist of literals" —
    weaker than axiomsMinimal (which requires exact complementary pairs). -/
@[blueprint "chap9__lemma_9_2_1"]
def axiomsAllSingleLiteral : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ S _ _ => ∀ C ∈ S, ∃ L : Literal, C = Clause.single L
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _ =>
    axiomsAllSingleLiteral left ∧ axiomsAllSingleLiteral right



end GCNFProofTree

/-- Lemma 4.2.1 (companion def): A clause sequent is provable in GCNF' iff
    there exists a GCNF' proof tree whose conclusion is that sequent. -/
@[blueprint "chap4__lemma_4_2_1"]
def GCNFProvable (S : ClauseSequent) : Prop :=
  Nonempty (GCNFProofTree S)

namespace GCNFProofTree

/-- The alternative rule mentioned after Definition 4.2.3: both premise
    contexts are drawn from Γ alone, recursively at every inference. -/
def restrictedContexts : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _ _ => True
  | _, .rule Gamma _ _ _ Gamma1 Gamma2 _ _ left right _ _ _ _ =>
    LCS.Finset.Subset Gamma1 Gamma ∧ LCS.Finset.Subset Gamma2 Gamma ∧
      restrictedContexts left ∧ restrictedContexts right

/-- Number of axiom leaves of the actual proof tree. -/
@[blueprint "chap4__theorem_4_3_1"]
def leafCount : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ _ _ => 1
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _ => leafCount left + leafCount right

/-- Number of vertices, including axioms and rule conclusions. -/
@[blueprint "chap4__lemma_4_3_3"]
def nodeCount : {S : ClauseSequent} → GCNFProofTree S → Nat
  | _, .axiom_ _ _ _ => 1
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _ => 1 + nodeCount left + nodeCount right

/-- Implicit weakening changes the root context and retains the same subtrees. -/
@[blueprint "chap4__theorem_4_3_3"]
def weaken {S : ClauseSequent} (t : GCNFProofTree S)
    (Extra : ClauseSequent) (hExtra : Extra.isOrdinary) :
    GCNFProofTree (LCS.Finset.union S Extra) := by
  cases t with
  | axiom_ S hS hTriv =>
    exact .axiom_ _ (ClauseSequent.ordinary_union hS hExtra)
      ⟨hTriv.choose, LCS.Finset.mem_union.mpr (Or.inl hTriv.choose_spec.1),
        LCS.Finset.mem_union.mpr (Or.inl hTriv.choose_spec.2)⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGamma hAs left right hNe hCs hG1 hG2 =>
    have hEq : LCS.Finset.union
        (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) Extra =
        LCS.Finset.union (LCS.Finset.union Gamma Extra)
          (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) := by
      apply LCS.Finset.ext
      intro C
      simp [LCS.Finset.mem_union, or_assoc, or_left_comm, or_comm]
    refine hEq.symm ▸ GCNFProofTree.rule (LCS.Finset.union Gamma Extra) As B Cs Gamma1 Gamma2
      (ClauseSequent.ordinary_union hGamma hExtra) hAs left right hNe hCs ?_ ?_
    · intro C hC
      rw [← hEq]
      exact LCS.Finset.mem_union.mpr (Or.inl (hG1 C hC))
    · intro C hC
      rw [← hEq]
      exact LCS.Finset.mem_union.mpr (Or.inl (hG2 C hC))



@[blueprint "chap4__theorem_4_3_3", simp] theorem leafCount_cast {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) :
    (h ▸ t).leafCount = t.leafCount 



@[simp] theorem nodeCount_cast {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) :
    (h ▸ t).nodeCount = t.nodeCount := by
  cases h
  rfl







end GCNFProofTree

/-- The least finite deduction-tree closure permits arbitrary ordinary sequent leaves. -/
inductive GCNFDeductionTree : ClauseSequent → Type where
  | leaf (S : ClauseSequent) (hOrdinary : S.isOrdinary) : GCNFDeductionTree S
  | rule (Gamma As : ClauseSequent) (B : Literal) (Cs Gamma1 Gamma2 : ClauseSequent)
      (hGamma : Gamma.isOrdinary) (hAs : As.isOrdinary)
      (left : GCNFDeductionTree (LCS.Finset.union Gamma1 Cs))
      (right : GCNFDeductionTree (LCS.Finset.union Gamma2 (ClauseSequent.single (Clause.single B))))
      (hCsNonempty : ∃ C, C ∈ Cs) (hCsSub : LCS.Finset.Subset Cs As)
      (hG1Sub : LCS.Finset.Subset Gamma1 (LCS.Finset.union Gamma
        (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))))
      (hG2Sub : LCS.Finset.Subset Gamma2 (LCS.Finset.union Gamma
        (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) :
      GCNFDeductionTree (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))

-- ========= Lemma 4.2.2 (supporting defs): Normal form predicates =========

/-- Lemma 4.2.2 (companion def): Normalized-formula version of isClause. -/
@[blueprint "chap4__lemma_4_2_2"]
def isClauseN : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg (.var _) => True
  | .disj B C => isClauseN B ∧ isClauseN C
  | _ => False

namespace ProofTree

/-- Lemma 4.2.2 (companion def): A Gentzen sequent is a clause sequent iff every
    antecedent formula is a clause and the succedent is empty. -/
@[blueprint "chap4__lemma_4_2_2"]
def isClauseSequent (s : Sequent) : Prop :=
  s.succedent = [] ∧
  ∀ A ∈ s.antecedent, isClauseN A

/-- No disjunction-left inference occurs in this entire subtree. -/
@[blueprint "chap4__lemma_4_2_2"]
def noOrLeft : {s : Sequent} → LCS.Propositional.Systems.G.ProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => noOrLeft t
  | _, .twoPremise rule t1 t2 =>
    match rule with
    | .orLeft _ _ _ _ _ => False
    | _ => noOrLeft t1 ∧ noOrLeft t2

/-- On every leaf-to-root path, every negation-left occurrence comes before
    every disjunction-left occurrence: a negation-left premise subtree contains
    no disjunction-left inference. -/
@[blueprint "chap4__lemma_4_2_2"]
def negLeftPrecedesOrLeft : {s : Sequent} → LCS.Propositional.Systems.G.ProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise rule t =>
    negLeftPrecedesOrLeft t ∧
    match rule with
    | .negLeft _ _ _ _ => noOrLeft t
    | _ => True
  | _, .twoPremise _ t1 t2 =>
    negLeftPrecedesOrLeft t1 ∧ negLeftPrecedesOrLeft t2

end ProofTree

-- ========= Example 4.2.1: GCNF' Proof Tree Example =========
/-- Example 4.2.1 (companion def): The textbook's clause sequent
    {P, ¬Q}, {¬S, ¬Q}, S, {¬S, Q} → with arbitrary propositional indices P, Q, R (R denotes S). -/
@[blueprint "chap4__example_4_2_1"]
def exGCNFClauseSet (P Q R : Nat) : ClauseSequent :=
  LCS.Finset.ofList
    [ Clause.ofList [Literal.pos P, Literal.neg Q]
    , Clause.ofList [Literal.neg R, Literal.neg Q]
    , Clause.single (Literal.pos R)
    , Clause.ofList [Literal.neg R, Literal.pos Q] ]

/-- Example 4.2.1: A concrete GCNF' proof tree for the textbook sequent
    {P, ¬Q}, {¬S, ¬Q}, S, {¬S, Q} → (page 116). -/
@[blueprint "chap4__example_4_2_1" (main := true)]
def exGCNFProofTree (P Q R : Nat) : GCNFProofTree (exGCNFClauseSet P Q R) := by
  -- P, Q, R denote arbitrary propositional indices; R is the displayed S.
  -- Outer rule: B = ¬Q, residual family {P, ¬S}, context {S, {¬S, Q}}.
  -- Its two principal clauses are {P, ¬Q} and {¬S, ¬Q}.
  -- Conclusion = Gamma ∪ mapSet = exGCNFClauseSet
  let outerGamma : ClauseSequent :=
    LCS.Finset.ofList [Clause.single (Literal.pos R), Clause.ofList [Literal.neg R, Literal.pos Q]]
  let outerAs : ClauseSequent :=
    LCS.Finset.ofList [Clause.single (Literal.pos P), Clause.single (Literal.neg R)]
  let outerB := Literal.neg Q
  -- Only the residual ¬S enters the left premise, the axiom ¬S, S →.
  let outerCs : ClauseSequent := LCS.Finset.singleton (Clause.single (Literal.neg R))
  let outerGamma1 : ClauseSequent := LCS.Finset.singleton (Clause.single (Literal.pos R))
  -- The right premise is the full outer context together with ¬Q.
  let outerGamma2 : ClauseSequent := outerGamma
  -- Verify conclusion equality
  have hConc : LCS.Finset.union outerGamma (ClauseSequent.mapSet outerAs (fun A => clauseWithLiteral A outerB))
    = exGCNFClauseSet P Q R := by
    apply LCS.Finset.ext; intro C
    simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]
  -- Left subtree: the axiom ¬S, S →.
  have hLeftEq : LCS.Finset.union outerGamma1 outerCs =
    LCS.Finset.ofList [Clause.single (Literal.neg R), Clause.single (Literal.pos R)] := by
    apply LCS.Finset.ext; intro C
    simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]
  -- The right subtree derives ¬Q, S, {¬S, Q} →.
  -- Inner rule: B = Q, residual family {¬S}, context {¬Q, S}.
  let innerGamma : ClauseSequent :=
    LCS.Finset.ofList [Clause.single (Literal.neg Q), Clause.single (Literal.pos R)]
  let innerAs : ClauseSequent := LCS.Finset.singleton (Clause.single (Literal.neg R))
  let innerB := Literal.pos Q
  let innerCs := innerAs
  let innerGamma1 : ClauseSequent := LCS.Finset.singleton (Clause.single (Literal.pos R))
  let innerGamma2 : ClauseSequent := LCS.Finset.singleton (Clause.single (Literal.neg Q))
  have hRightEq : LCS.Finset.union outerGamma2 (ClauseSequent.single (Clause.single outerB))
    = LCS.Finset.union innerGamma (ClauseSequent.mapSet innerAs (fun A => clauseWithLiteral A innerB)) := by
    apply LCS.Finset.ext; intro C
    simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]
  -- Inner left: the axiom S, ¬S →.
  have hInnerLeftEq : LCS.Finset.union innerGamma1 innerCs =
    LCS.Finset.ofList [Clause.single (Literal.neg R), Clause.single (Literal.pos R)] := by
    apply LCS.Finset.ext; intro C
    simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]
  -- Inner right: the axiom ¬Q, Q →.
  have hInnerRightEq : LCS.Finset.union innerGamma2 (ClauseSequent.single (Clause.single innerB)) =
    LCS.Finset.ofList [Clause.single (Literal.neg Q), Clause.single (Literal.pos Q)] := by
    apply LCS.Finset.ext; intro C
    simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]
  exact hConc ▸ GCNFProofTree.rule outerGamma outerAs outerB outerCs outerGamma1 outerGamma2
    (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp) (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp)
    (hLeftEq ▸ GCNFProofTree.axiom_ _ (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp) ⟨R, by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm], by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]⟩)
    (hRightEq ▸ GCNFProofTree.rule innerGamma innerAs innerB innerCs innerGamma1 innerGamma2
      (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp) (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (hInnerLeftEq ▸ GCNFProofTree.axiom_ _ (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp) ⟨R, by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm], by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]⟩)
      (hInnerRightEq ▸ GCNFProofTree.axiom_ _ (by apply ClauseSequent.ordinary_ofList; intro C hC; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC; rcases hC with rfl | rfl <;> simp) ⟨Q, by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm], by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]⟩)
      ⟨Clause.single (Literal.neg R), by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]⟩
      (by intro a ha; exact ha)
      (by intro a ha; rw [LCS.Finset.mem_singleton] at ha; subst ha; simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm])
      (by intro a ha; rw [LCS.Finset.mem_singleton] at ha; subst ha; simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]))
    ⟨Clause.single (Literal.neg R), by simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm]⟩
    (by intro a ha; rw [LCS.Finset.mem_singleton] at ha; subst ha; simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm])
    (by intro a ha; rw [LCS.Finset.mem_singleton] at ha; subst ha; simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm])
    (by intro a ha; rw [LCS.Finset.mem_ofList] at ha; simp [List.mem_cons] at ha; rcases ha with rfl | rfl <;> simp [outerGamma, outerAs, outerB, outerCs, outerGamma1, outerGamma2, innerGamma, innerAs, innerB, innerCs, innerGamma1, innerGamma2, exGCNFClauseSet, ClauseSequent.mapSet, ClauseSequent.single, LCS.Finset.mem_image, LCS.Finset.mem_ofList, LCS.Finset.mem_union, clauseWithLiteral_single, or_comm, or_left_comm, or_assoc, eq_comm])

-- ========= Helpers for LCS.Finset.image membership =========



-- ========= Lemma 4.2.1: Axiom Validity and Rule Preservation =========

theorem mem_image_iff (f : Clause → Clause) (s : ClauseSequent) (x : Clause) :
    x ∈ LCS.Finset.image f s ↔ ∃ a ∈ s, f a = x :=
-- BEGIN PROOF
  LCS.Finset.mem_image

/-- Lemma 4.2.1: Every axiom of GCNF' is valid, and for every valuation v, if
    v satisfies both premises of a GCNF' rule then v satisfies the conclusion. -/
@[blueprint "chap4__lemma_4_2_1" (main := true)]
theorem gcnf_axiom_valid :
    (∀ (S : ClauseSequent), ClauseSequent.isTrivial S →
      ClauseSequent.isValid S) ∧
    (∀ (Gamma As : ClauseSequent) (B : Literal) (Cs Gamma1 Gamma2 : ClauseSequent)
      (v : Nat → Bool),
      (∃ C, C ∈ Cs) → LCS.Finset.Subset Cs As →
      LCS.Finset.Subset Gamma1 (LCS.Finset.union Gamma
        (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) →
      LCS.Finset.Subset Gamma2 (LCS.Finset.union Gamma
        (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) →
      ClauseSequent.sequentSatisfiedBy (LCS.Finset.union Gamma1 Cs) v →
      ClauseSequent.sequentSatisfiedBy
        (LCS.Finset.union Gamma2 (ClauseSequent.single (Clause.single B))) v →
      ClauseSequent.sequentSatisfiedBy
        (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) v) 

-- ========= Soundness of GCNF' (Corollary of Lemma 4.2.1) =========

/-- Lemma 4.2.1 (companion — corollary, GCNF' soundness): Every sequent
    provable in GCNF' is valid. -/
@[blueprint "chap4__lemma_4_2_1"]
theorem gcnf_soundness (S : ClauseSequent) (h : GCNFProvable S) :
    ClauseSequent.isValid S 

-- ========= Lemma 4.2.2: Normal Form for G' Proofs =========

-- The proof constructs a new G' proof tree for a valid clause sequent
-- that satisfies the normal form predicate negLeftPrecedesOrLeft.
-- We build a fresh proof tree by induction on the total formula complexity
-- of the sequent. The construction specializes to clause-compatible
-- sequents: antecedent formulas are either variables, negated variables,
-- or disjunctions of clause-parts; succedent formulas are variables.
-- Backward search splits all disjunctions before moving negative literals
-- to the succedent, giving the required leaf-to-root rule order.

-- A "clause-compatible" sequent: antecedent formulas are clause-like
-- (isClause or var), and succedent formulas are variables.
-- This invariant is preserved when decomposing clause sequents via
-- negLeft (for neg (var n)) and orLeft.
def isClauseCompatible (s : Sequent) : Prop :=
  (∀ A ∈ s.antecedent, isClauseN A ∨ ∃ n, A = .var n) ∧
  (∀ B ∈ s.succedent, ∃ n, B = .var n)

-- Clause sequents are clause-compatible


-- Formula complexity for the induction measure










-- negLeft backward validity


-- orLeft backward validity (left branch)


-- orLeft backward validity (right branch)


-- Valid all-variable sequent has a common formula (axiom)


-- Find a non-variable formula in a list


-- Classify a clause-compatible formula with positive fmlaSize


-- seqSize decrease for negLeft: premise has smaller size


-- seqSize decrease for orLeft: each premise has smaller size




-- Clause-compatibility is preserved by negLeft for neg (var n)


-- Clause-compatibility is preserved by orLeft




-- Helper: listSize L = 0 implies all formula sizes are 0






-- Core theorem: given any proof tree for a clause sequent, there exists
-- a proof tree satisfying negLeftPrecedesOrLeft. Uses soundness to get
-- validity, then builds a new tree via build_normal_form_proof.


/-- Lemma 4.2.2: Every G' proof for a clause sequent can be transformed
    into one where neg:left precedes orLeft on every leaf-to-root path. -/
@[blueprint "chap4__lemma_4_2_2" (main := true)]
theorem gPrime_proof_normal_form
    (S : LCS.Propositional.Systems.G.Sequent)
    (pt : LCS.Propositional.Systems.G.ProofTree S)
    (hClause : ProofTree.isClauseSequent S) :
    ∃ pt' : LCS.Propositional.Systems.G.ProofTree S,
      ProofTree.negLeftPrecedesOrLeft pt' 

-- ========= Permutation invariance =========



-- ========= Helpers for Completeness of GCNF' =========

open Classical















-- ========= Well-founded completeness =========















/-- Helper: membership in ClauseSequent.single unfolds to equality. -/
theorem mem_csingle (C D : Clause) : C ∈ ClauseSequent.single D ↔ C = D := by
-- BEGIN PROOF
  show C ∈ LCS.Finset.singleton D ↔ C = D
  exact LCS.Finset.mem_singleton C D

/-- Helper: if every clause is a singleton and the sequent is valid,
    then the sequent is trivial. -/
theorem singletons_valid_imp_trivial (S : ClauseSequent)
    (hSingle : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L)
    (hValid : ClauseSequent.isValid S) :
    ClauseSequent.isTrivial S := by
-- BEGIN PROOF
  suffices h : ¬ClauseSequent.isTrivial S → False from
    Classical.byContradiction fun hNT => h hNT
  intro hNontriv
  apply hValid
  refine ⟨fun P => decide (Clause.single (Literal.pos P) ∈ S), fun C hC => ?_⟩
  obtain ⟨L, hCL⟩ := hSingle C hC
  subst hCL
  refine ⟨L, (LCS.Finset.mem_singleton L L).mpr rfl, ?_⟩
  cases L with
  | pos P =>
    simp only [Literal.satisfiedBy]
    have hdec : decide (Clause.single (Literal.pos P) ∈ S) = true :=
      decide_eq_true hC
    simp [hdec]
  | neg P =>
    simp only [Literal.satisfiedBy]
    have hNotPos : ¬(Clause.single (Literal.pos P) ∈ S) := fun hpos =>
      hNontriv ⟨P, hpos, hC⟩
    have hdec : decide (Clause.single (Literal.pos P) ∈ S) = false :=
      decide_eq_false hNotPos
    simp [hdec]

/-- Helper: if v satisfies Gamma ∪ As, then v satisfies
    Gamma ∪ mapSet As (clauseWithLiteral · B) (each clause gets an extra literal). -/
theorem sat_union_extends (Gamma : ClauseSequent) (As : ClauseSequent)
    (B : Literal) (v : Nat → Bool)
    (hSat : ClauseSequent.satisfiedBy (LCS.Finset.union Gamma As) v) :
    ClauseSequent.satisfiedBy
      (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) v := by
-- BEGIN PROOF
  intro C hC
  rw [LCS.Finset.mem_union] at hC
  rcases hC with hCG | hCMap
  · exact hSat C ((LCS.Finset.mem_union_exp C Gamma As).mpr (Or.inl hCG))
  · obtain ⟨A, hAAs, rfl⟩ := (mem_image_iff _ _ _).mp hCMap
    have hAsat := hSat A ((LCS.Finset.mem_union_exp A Gamma As).mpr (Or.inr hAAs))
    obtain ⟨L, hLmem, hLsat⟩ := hAsat
    exact ⟨L, (LCS.Finset.mem_insert_exp B L A).mpr (Or.inr hLmem), hLsat⟩

/-- Helper: the left premise (with As directly) is valid if the
    conclusion is. -/
theorem gcnf_left_valid (Gamma : ClauseSequent) (As : ClauseSequent)
    (B : Literal)
    (hValid : ClauseSequent.isValid
      (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) :
    ClauseSequent.isValid (LCS.Finset.union Gamma As) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  exact hValid ⟨v, sat_union_extends Gamma As B v hSat⟩

/-- Helper: the right premise is valid if the conclusion is. -/
theorem gcnf_right_valid (Gamma : ClauseSequent)
    (As : ClauseSequent) (B : Literal)
    (hValid : ClauseSequent.isValid
      (LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) :
    ClauseSequent.isValid (LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B))) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  apply hValid
  refine ⟨v, fun C hC => ?_⟩
  rw [LCS.Finset.mem_union] at hC
  rcases hC with hCG | hCMap
  · exact hSat C ((LCS.Finset.mem_union_exp C Gamma (ClauseSequent.single (Clause.single B))).mpr (Or.inl hCG))
  · obtain ⟨A, _, rfl⟩ := (mem_image_iff _ _ _).mp hCMap
    have hBsat := hSat (Clause.single B)
      ((LCS.Finset.mem_union_exp (Clause.single B) Gamma (ClauseSequent.single (Clause.single B))).mpr
        (Or.inr ((LCS.Finset.mem_singleton (Clause.single B) (Clause.single B)).mpr rfl)))
    obtain ⟨L, hLmem, hLsat⟩ := hBsat
    have hLeqB : L = B := (LCS.Finset.mem_singleton L B).mp hLmem
    exact ⟨L, (LCS.Finset.mem_insert_exp B L A).mpr (Or.inl hLeqB), hLsat⟩

/-- Helper: convert a list of literal-lists to a ClauseSequent. -/
def litListsToClauseSeq (ll : List (List Literal)) : ClauseSequent :=
  LCS.Finset.ofList (ll.map Clause.ofList)

/-- Helper: total number of literals across all clauses in a list-of-lists. -/
def totalLitCount (ll : List (List Literal)) : Nat :=
  ll.foldl (fun acc ls => acc + ls.length) 0

theorem foldl_shift (a b : Nat) (ll : List (List Literal)) :
    List.foldl (fun acc ls => acc + ls.length) (a + b) ll =
    a + List.foldl (fun acc ls => acc + ls.length) b ll := by
-- BEGIN PROOF
  induction ll generalizing a b with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [show a + b + hd.length = a + (b + hd.length) from by omega]
    exact ih a (b + hd.length)

theorem totalLitCount_cons (ls : List Literal) (rest : List (List Literal)) :
    totalLitCount (ls :: rest) = ls.length + totalLitCount rest := by
-- BEGIN PROOF
  unfold totalLitCount
  simp only [List.foldl]
  rw [Nat.zero_add]
  exact foldl_shift ls.length 0 rest

/-- Helper: replacing one element in ll with a shorter list decreases totalLitCount. -/
theorem totalLitCount_replace_lt
    (pre : List (List Literal)) (ls : List Literal) (suf : List (List Literal))
    (ls' : List Literal) (hlt : ls'.length < ls.length) :
    totalLitCount (pre ++ ls' :: suf) < totalLitCount (pre ++ ls :: suf) := by
-- BEGIN PROOF
  induction pre with
  | nil =>
    simp only [List.nil_append]
    rw [totalLitCount_cons, totalLitCount_cons]
    omega
  | cons hd tl ih =>
    simp only [List.cons_append]
    rw [totalLitCount_cons, totalLitCount_cons]
    omega

/-- Helper: clauseWithLiteral (Clause.ofList rest) L = Clause.ofList (L :: rest). -/
theorem clauseWithLiteral_ofList_cons (L : Literal) (rest : List Literal) :
    clauseWithLiteral (Clause.ofList rest) L = Clause.ofList (L :: rest) := by
-- BEGIN PROOF
  unfold clauseWithLiteral Clause.ofList
  apply LCS.Finset.ext; intro l
  rw [LCS.Finset.mem_insert, LCS.Finset.mem_ofList, LCS.Finset.mem_ofList]
  exact ⟨fun h => h.elim (fun heq => List.mem_cons.mpr (Or.inl heq))
                          (fun hr => List.mem_cons.mpr (Or.inr hr)),
         fun h => List.mem_cons.mp h |>.elim Or.inl Or.inr⟩

/-- Helper: Clause.ofList [L] = Clause.single L. -/
theorem ofList_singleton_eq (L : Literal) :
    Clause.ofList [L] = Clause.single L := by
-- BEGIN PROOF
  apply LCS.Finset.ext; intro l
  simp [Clause.ofList, Clause.single, LCS.Finset.mem_ofList, LCS.Finset.mem_singleton, List.mem_cons]

/-- Helper: the LCS.Finset.ofList decomposition: replacing a clause in a list. -/
@[blueprint "chap4__example_4_2_1"]
theorem ofList_replace_eq_union
    (pre : List Clause) (suf : List Clause) (C : Clause) :
    LCS.Finset.ofList (pre ++ C :: suf) =
    LCS.Finset.union (LCS.Finset.ofList (pre ++ suf)) (ClauseSequent.single C) 















-- ========= Helper: clauseWithLiteral identity and exact-pair axiom construction =========















-- ========= Axiom minimization for GCNF' proofs =========











-- ========= Theorem 4.2.1: Completeness of GCNF' =========

/-- Helper: if the sequent from a list is valid, then so is the sequent with
    a clause replaced by a smaller clause (in the "left branch" sense). -/
theorem ofList_left_valid
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (hValid : ClauseSequent.isValid (LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf))) :
    ClauseSequent.isValid (LCS.Finset.ofList (pre ++ A :: suf)) := by
-- BEGIN PROOF
  let Gamma := LCS.Finset.ofList (pre ++ suf)
  have h1 : LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) :=
    ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  have h2 : LCS.Finset.ofList (pre ++ A :: suf) = LCS.Finset.union Gamma (ClauseSequent.single A) :=
    ofList_replace_eq_union pre suf A
  rw [h2]
  have h3 : LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      LCS.Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply LCS.Finset.ext; intro C
    constructor
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'
        rw [mem_csingle]; exact hCA'.symm
  rw [h1, h3] at hValid
  exact gcnf_left_valid Gamma (ClauseSequent.single A) B hValid

/-- Helper: if the sequent from a list is valid, then so is the sequent with
    a clause replaced by a singleton (in the "right branch" sense). -/
theorem ofList_right_valid
    (pre : List Clause) (suf : List Clause)
    (A : Clause) (B : Literal)
    (hValid : ClauseSequent.isValid (LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf))) :
    ClauseSequent.isValid (LCS.Finset.ofList (pre ++ Clause.single B :: suf)) := by
-- BEGIN PROOF
  let Gamma := LCS.Finset.ofList (pre ++ suf)
  have h1 : LCS.Finset.ofList (pre ++ clauseWithLiteral A B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) :=
    ofList_replace_eq_union pre suf (clauseWithLiteral A B)
  have h2 : LCS.Finset.ofList (pre ++ Clause.single B :: suf) =
      LCS.Finset.union Gamma (ClauseSequent.single (Clause.single B)) :=
    ofList_replace_eq_union pre suf (Clause.single B)
  rw [h2]
  have h3 : LCS.Finset.union Gamma (ClauseSequent.single (clauseWithLiteral A B)) =
      LCS.Finset.union Gamma (ClauseSequent.mapSet (ClauseSequent.single A) (fun x => clauseWithLiteral x B)) := by
    apply LCS.Finset.ext; intro C
    constructor
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        rw [mem_csingle] at hC
        exact (mem_image_iff _ _ _).mpr ⟨A, (mem_csingle A A).mpr rfl, hC.symm⟩
    · intro hC
      rw [LCS.Finset.mem_union] at hC ⊢
      rcases hC with hG | hC
      · exact Or.inl hG
      · right
        obtain ⟨A', hA', hCA'⟩ := (mem_image_iff _ _ _).mp hC
        rw [(mem_csingle A' A).mp hA'] at hCA'
        rw [mem_csingle]; exact hCA'.symm
  rw [h1, h3] at hValid
  exact gcnf_right_valid Gamma (ClauseSequent.single A) B hValid

/-- Helper: Clause.ofList C.toList = C for any clause. In the LCS.Finset
    representation C.val is a Multiset; `toList` picks (via Classical.choose)
    one list representative, and ofList on that list returns C. -/
theorem ofList_toList_eq (C : Clause) : Clause.ofList C.toList = C := by
-- BEGIN PROOF
  unfold Clause.ofList
  apply LCS.Finset.ext; intro a
  rw [LCS.Finset.mem_ofList, LCS.Finset.mem_toList]

/-- Adding literal L to the singleton clause {L} yields {L} again. -/
theorem clauseWithLiteral_single_self (L : Literal) :
    clauseWithLiteral (Clause.single L) L = Clause.single L := by
-- BEGIN PROOF
  apply LCS.Finset.ext; intro l
  show l ∈ LCS.Finset.insert L (Clause.single L) ↔ l ∈ Clause.single L
  rw [LCS.Finset.mem_insert]
  constructor
  · intro h
    rcases h with rfl | hL
    · exact (LCS.Finset.mem_singleton l l).mpr rfl
    · exact hL
  · intro h
    exact Or.inr h

/-- The exact complementary pair set for a given P. -/
def pairSet (P : Nat) : ClauseSequent :=
  LCS.Finset.ofList [Clause.single (Literal.pos P), Clause.single (Literal.neg P)]

/-- The pair set is trivial. -/
theorem pairSet_trivial (P : Nat) : ClauseSequent.isTrivial (pairSet P) :=
-- BEGIN PROOF
  ⟨P,
    (LCS.Finset.mem_ofList_exp _ _).mpr (List.mem_cons.mpr (Or.inl rfl)),
    (LCS.Finset.mem_ofList_exp _ _).mpr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))⟩

/-- Construct an exact-pair axiom proof tree. -/
def pairAxiom (P : Nat) : GCNFProofTree (pairSet P) :=
  GCNFProofTree.axiom_ (pairSet P) (by
    apply ClauseSequent.ordinary_ofList
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> exact Clause.single_ordinary _) (pairSet_trivial P)

/-- Theorem 4.2.1: (Completeness of GCNF') Every valid clause sequent is
    provable in GCNF' with minimal axioms when nontrivial. -/
@[blueprint "chap4__theorem_4_2_1" (main := true)]
theorem gcnf_completeness (S : ClauseSequent)
    (hValid : ClauseSequent.isValid S)
    (hNe : ∀ C ∈ S, C ≠ Clause.empty) :
    GCNFProvable S ∧
    (ClauseSequent.isNontrivial S →
      ∃ t : GCNFProofTree S, t.axiomsMinimal) 

/-- The ordinary disjunction-only system after absorbing negation-left into
    trivial axioms. Both displayed disjuncts are whole ordinary clauses. -/
@[blueprint "chap4__example_4_2_1"]
inductive OrdinaryClauseProof : ClauseSequent → Type where
  | axiom_ (S : ClauseSequent) (hOrdinary : S.isOrdinary) (hTrivial : S.isTrivial) :
      OrdinaryClauseProof S
  | orLeft (Gamma : ClauseSequent) (A B : Clause)
      (left : OrdinaryClauseProof (LCS.Finset.union Gamma (ClauseSequent.single A)))
      (right : OrdinaryClauseProof (LCS.Finset.union Gamma (ClauseSequent.single B))) :
      OrdinaryClauseProof
        (LCS.Finset.union Gamma (ClauseSequent.single (LCS.Finset.union A B)))

namespace OrdinaryClauseProof

@[blueprint "chap4__example_4_2_1"]
def leafCount : {S : ClauseSequent} → OrdinaryClauseProof S → Nat
  | _, .axiom_ _ _ _ => 1
  | _, .orLeft _ _ _ left right => left.leafCount + right.leafCount

@[blueprint "chap4__example_4_2_1"]
def nodeCount : {S : ClauseSequent} → OrdinaryClauseProof S → Nat
  | _, .axiom_ _ _ _ => 1
  | _, .orLeft _ _ _ left right => 1 + left.nodeCount + right.nodeCount

@[blueprint "chap4__example_4_2_1"]
def orLeftOfList (pre suf : List Clause) (A B : Clause)
    (left : OrdinaryClauseProof (LCS.Finset.ofList (pre ++ A :: suf)))
    (right : OrdinaryClauseProof (LCS.Finset.ofList (pre ++ B :: suf))) :
    OrdinaryClauseProof (LCS.Finset.ofList (pre ++ LCS.Finset.union A B :: suf)) :=
  (ofList_replace_eq_union pre suf (LCS.Finset.union A B)).symm ▸
    (.orLeft (LCS.Finset.ofList (pre ++ suf)) A B
      ((ofList_replace_eq_union pre suf A) ▸ left)
      ((ofList_replace_eq_union pre suf B) ▸ right))



@[simp] theorem leafCount_cast {S T : ClauseSequent} (h : S = T)
    (t : OrdinaryClauseProof S) : (h ▸ t).leafCount = t.leafCount := by cases h; rfl



@[simp] theorem nodeCount_cast {S T : ClauseSequent} (h : S = T)
    (t : OrdinaryClauseProof S) : (h ▸ t).nodeCount = t.nodeCount := by cases h; rfl

end OrdinaryClauseProof

/-- A union containing an ordinary disjunct is an ordinary clause. -/
@[blueprint "chap4__definition_4_2_1"]
theorem Clause.union_ordinary_left {A : Clause} (hA : A.isOrdinary) (B : Clause) :
    Clause.isOrdinary (LCS.Finset.union A B) 

/-- The full ordinary G′ comparison diagram of Example 4.2.1, with trivial
    leaves absorbing their negation-left closures. Repeated clause occurrences
    in T₂ contract according to the section's set convention. -/
@[blueprint "chap4__example_4_2_1"]
def exOrdinaryProofTree (P Q R : Nat) : OrdinaryClauseProof (exGCNFClauseSet P Q R) := by
  let p := Clause.single (Literal.pos P)
  let q := Clause.single (Literal.pos Q)
  let nq := Clause.single (Literal.neg Q)
  let r := Clause.single (Literal.pos R)
  let nr := Clause.single (Literal.neg R)
  let x := LCS.Finset.union nr nq
  let y := LCS.Finset.union nr q
  have op : p.isOrdinary := Clause.single_ordinary _
  have oq : q.isOrdinary := Clause.single_ordinary _
  have onq : nq.isOrdinary := Clause.single_ordinary _
  have or : r.isOrdinary := Clause.single_ordinary _
  have onr : nr.isOrdinary := Clause.single_ordinary _
  have oy : Clause.isOrdinary y := Clause.union_ordinary_left onr q
  let a : OrdinaryClauseProof (LCS.Finset.ofList [p, nr, r, y]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · exact op
      · exact onr
      · exact or
      · exact oy
    )) (by
      refine ⟨R, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let b : OrdinaryClauseProof (LCS.Finset.ofList [p, nq, r, nr]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · exact op
      · exact onq
      · exact or
      · exact onr
    )) (by
      refine ⟨R, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let c : OrdinaryClauseProof (LCS.Finset.ofList [p, nq, r, q]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · exact op
      · exact onq
      · exact or
      · exact oq
    )) (by
      refine ⟨Q, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let d : OrdinaryClauseProof (LCS.Finset.ofList [nq, nr, r, y]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · exact onq
      · exact onr
      · exact or
      · exact oy
    )) (by
      refine ⟨R, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let e : OrdinaryClauseProof (LCS.Finset.ofList [nq, r, nr]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl
      · exact onq
      · exact or
      · exact onr
    )) (by
      refine ⟨R, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let f : OrdinaryClauseProof (LCS.Finset.ofList [nq, r, q]) :=
    .axiom_ _ (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl
      · exact onq
      · exact or
      · exact oq
    )) (by
      refine ⟨Q, ?_, ?_⟩ <;>
        simp [p, q, nq, r, nr, LCS.Finset.mem_ofList])
  let t1Right := OrdinaryClauseProof.orLeftOfList [p, nq, r] [] nr q b c
  let t1 := OrdinaryClauseProof.orLeftOfList [p] [r, y] nr nq a t1Right
  let t2Right := OrdinaryClauseProof.orLeftOfList [nq, r] [] nr q e f
  have hDuplicate : LCS.Finset.ofList [nq, r, y] = LCS.Finset.ofList [nq, nq, r, y] := by
    apply LCS.Finset.ext; intro C
    simp [LCS.Finset.mem_ofList, or_assoc]
  let t2 := OrdinaryClauseProof.orLeftOfList [nq] [r, y] nr nq d (hDuplicate ▸ t2Right)
  let result := OrdinaryClauseProof.orLeftOfList [] [x, r, y] p nq t1 t2
  have hRoot : LCS.Finset.ofList [LCS.Finset.union p nq, x, r, y] = exGCNFClauseSet P Q R := by
    have pair (L M : Literal) : LCS.Finset.union (Clause.single L) (Clause.single M) =
        Clause.ofList [L, M] := by
      apply LCS.Finset.ext; intro K
      simp [Clause.single, Clause.ofList, LCS.Finset.mem_union, LCS.Finset.mem_singleton,
        LCS.Finset.mem_ofList]
    simp only [p, q, nq, r, nr, x, y, pair, exGCNFClauseSet]
  exact hRoot ▸ result

/-- The two displayed proof trees have respectively three and six axiom leaves. -/
@[blueprint "chap4__example_4_2_1"]
theorem exProof_leaf_comparison (P Q R : Nat) :
    (exGCNFProofTree P Q R).leafCount = 3 ∧
    (exOrdinaryProofTree P Q R).leafCount = 6 

/-- Counting the displayed vertices gives five versus eleven. -/
@[blueprint "chap4__example_4_2_1"]
theorem exProof_node_comparison (P Q R : Nat) :
    (exGCNFProofTree P Q R).nodeCount = 5 ∧
    (exOrdinaryProofTree P Q R).nodeCount = 11 

namespace OrdinaryClauseProof

/-- Ordinary disjunction proofs retain the ordinary-clause domain at every root. -/
theorem ordinary : {S : ClauseSequent} → OrdinaryClauseProof S → S.isOrdinary
  | _, .axiom_ _ h _ => h
  | _, .orLeft Gamma A B left _ => by
    have h := ordinary left
    apply ClauseSequent.ordinary_union
    · exact ClauseSequent.ordinary_subset h (fun C hC => LCS.Finset.mem_union.mpr (Or.inl hC))
    · apply ClauseSequent.ordinary_single
      apply Clause.union_ordinary_left
      exact h A (LCS.Finset.mem_union.mpr (Or.inr ((LCS.Finset.mem_singleton _ _).mpr rfl)))

/-- Weakening adds the same ordinary context at every displayed node. -/
def weaken : {S : ClauseSequent} → OrdinaryClauseProof S →
    (Extra : ClauseSequent) → Extra.isOrdinary →
    OrdinaryClauseProof (LCS.Finset.union S Extra)
  | _, .axiom_ S hS hTriv, Extra, hExtra =>
    .axiom_ _ (ClauseSequent.ordinary_union hS hExtra)
      ⟨hTriv.choose, LCS.Finset.mem_union.mpr (Or.inl hTriv.choose_spec.1),
        LCS.Finset.mem_union.mpr (Or.inl hTriv.choose_spec.2)⟩
  | _, .orLeft Gamma A B left right, Extra, hExtra => by
    have commute (C : Clause) :
        LCS.Finset.union (LCS.Finset.union Gamma (ClauseSequent.single C)) Extra =
        LCS.Finset.union (LCS.Finset.union Gamma Extra) (ClauseSequent.single C) := by
      apply LCS.Finset.ext; intro D
      simp [LCS.Finset.mem_union, or_assoc, or_left_comm, or_comm]
    exact (commute (LCS.Finset.union A B)).symm ▸
      .orLeft (LCS.Finset.union Gamma Extra) A B
        (commute A ▸ left.weaken Extra hExtra) (commute B ▸ right.weaken Extra hExtra)



/-- List presentation of the same context weakening. -/
def weakenOfList {cs : List Clause} (t : OrdinaryClauseProof (LCS.Finset.ofList cs))
    (extra : List Clause) (hExtra : ∀ C ∈ extra, C.isOrdinary) :
    OrdinaryClauseProof (LCS.Finset.ofList (cs ++ extra)) := by
  have h : LCS.Finset.union (LCS.Finset.ofList cs) (LCS.Finset.ofList extra) =
      LCS.Finset.ofList (cs ++ extra) := by
    apply LCS.Finset.ext; intro C
    simp [LCS.Finset.mem_union, LCS.Finset.mem_ofList]
  exact h ▸ t.weaken (LCS.Finset.ofList extra) (ClauseSequent.ordinary_ofList hExtra)



/-- Expand all m separate disjunctions before closing any branch. The all-A
    branch uses `left`; each of the other 2^m−1 branches uses a weakened copy
    of `right`. The shared clause B is an arbitrary ordinary disjunction. -/
def expandBatch (Gamma : List Clause) (B : Clause) (hB : B.isOrdinary) :
    (As : List Clause) → (∀ A ∈ As, A.isOrdinary) →
    OrdinaryClauseProof (LCS.Finset.ofList (Gamma ++ As)) →
    OrdinaryClauseProof (LCS.Finset.ofList (Gamma ++ [B])) →
    OrdinaryClauseProof (LCS.Finset.ofList (Gamma ++ As.map (fun A => LCS.Finset.union A B)))
  | [], _, left, _ => left
  | A :: As, hAs, left, right => by
    have hA : A.isOrdinary := hAs A (by simp)
    have hTail : ∀ C ∈ As, C.isOrdinary := fun C hC => hAs C (by simp [hC])
    have hOneA : ∀ C ∈ [A], C.isOrdinary := by simpa using hA
    have hOneB : ∀ C ∈ [B], C.isOrdinary := by simpa using hB
    have swap : LCS.Finset.ofList ((Gamma ++ [B]) ++ [A]) =
        LCS.Finset.ofList ((Gamma ++ [A]) ++ [B]) := by
      apply LCS.Finset.ext; intro C
      simp [LCS.Finset.mem_ofList, or_assoc, or_left_comm, or_comm]
    let l := expandBatch (Gamma ++ [A]) B hB As hTail
      ((congrArg LCS.Finset.ofList (List.append_assoc Gamma [A] As)).symm ▸ left)
      (swap ▸ right.weakenOfList [A] hOneA)
    let r := expandBatch (Gamma ++ [B]) B hB As hTail
      (right.weakenOfList As hTail) (right.weakenOfList [B] hOneB)
    exact orLeftOfList Gamma (As.map (fun C => LCS.Finset.union C B)) A B
      (congrArg LCS.Finset.ofList (List.append_assoc Gamma [A] _) ▸ l)
      (congrArg LCS.Finset.ofList (List.append_assoc Gamma [B] _) ▸ r)
termination_by As => As.length



end OrdinaryClauseProof

/-- The preliminary shared-context batch system. Unlike GCNF′, the shared
    right disjunct may itself be any ordinary clause. Its rule stores the two
    premise trees once, irrespective of the size of the principal family. -/
inductive BatchedClauseProof : ClauseSequent → Type where
  | axiom_ (S : ClauseSequent) (hOrdinary : S.isOrdinary) (hTrivial : S.isTrivial) :
      BatchedClauseProof S
  | rule (Gamma As : List Clause) (B : Clause)
      (hAsNonempty : As ≠ []) (hAs : ∀ A ∈ As, A.isOrdinary) (hB : B.isOrdinary)
      (left : BatchedClauseProof (LCS.Finset.ofList (Gamma ++ As)))
      (right : BatchedClauseProof (LCS.Finset.ofList (Gamma ++ [B]))) :
      BatchedClauseProof (LCS.Finset.ofList (Gamma ++ As.map (fun A => LCS.Finset.union A B)))

namespace BatchedClauseProof

/-- A batch counts as one inference with two premise trees. -/
def leafCount : {S : ClauseSequent} → BatchedClauseProof S → Nat
  | _, .axiom_ _ _ _ => 1
  | _, .rule _ _ _ _ _ _ left right => left.leafCount + right.leafCount

/-- Expand every batch into the ordinary disjunction-left proof it abbreviates. -/
def toOrdinary : {S : ClauseSequent} → BatchedClauseProof S → OrdinaryClauseProof S
  | _, .axiom_ S hOrdinary hTrivial => .axiom_ S hOrdinary hTrivial
  | _, .rule Gamma As B _ hAs hB left right =>
    OrdinaryClauseProof.expandBatch Gamma B hB As hAs left.toOrdinary right.toOrdinary



/-- Every batch proof concludes an ordinary clause sequent. -/
theorem ordinary {S : ClauseSequent} (t : BatchedClauseProof S) : S.isOrdinary :=
  t.toOrdinary.ordinary

end BatchedClauseProof

end LCS.Resolution.GCNF
