import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Semantics.TruthFunctions
import Attach
import LCS.Propositional.Systems.G.NormalForms.ProofsStamp

/-! # Propositional.Systems.G.NormalForms
    Formalization of Chapter 3, Sections 3.4.8-3.4.9.
    Defines CNF, DNF, NNF, and conversion algorithms.
-/

namespace LCS.Propositional.Systems.G.NormalForms

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Semantics.TruthFunctions

-- ========= Local logEquivN for PropFormulaNormalized =========

/-- Definition 3.4.a (companion): Logical equivalence for normalized formulas.
    A and B are logically equivalent iff for all valuations v, evalExtN v A = evalExtN v B.
    This is the semantic counterpart of the §3.4.2 abbreviation (A ≡ B). -/
@[blueprint "chap3__definition_3_4_a"]
def logEquivN (A B : PropFormulaNormalized) : Prop :=
  ∀ v : Valuation, hEquiv (evalExtN v A) (evalExtN v B) = BoolVal.T

theorem tautological_equiv_iff_equal_evalN (A B : PropFormulaNormalized) :
    logEquivN A B ↔ ∀ v : Valuation, evalExtN v A = evalExtN v B := by
-- BEGIN PROOF
  constructor
  · intro h v
    have hv := h v
    simp only [hEquiv] at hv
    cases heqA : evalExtN v A <;> cases heqB : evalExtN v B <;> simp_all
  · intro h v
    simp only [hEquiv]
    rw [h v]
    cases evalExtN v B <;> rfl

-- ========= Definition 3.4.7: Literals, Clauses, CNF, DNF =========

namespace PropFormulaNormalized

/-- Definition 3.4.7: A proposition is a literal if it is a propositional
    symbol P or the negation ¬P of a propositional symbol. Literals are the
    atomic building blocks of CNF and DNF. -/
@[blueprint "chap3__definition_3_4_7" (main := true)]
def isLiteral : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg (.var _) => True
  | _ => False

/-- Definition 3.4.7 (companion): A clause is a disjunction of literals.
    A single literal counts as a clause, and (B ∨ C) is a clause when B
    and C are clauses, with arbitrary binary grouping. -/
@[blueprint "chap3__definition_3_4_7"]
def isClause : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg (.var _) => True
  | .disj B C => isClause B ∧ isClause C
  | _ => False

/-- Definition 3.4.7 (companion): A proposition is in conjunctive normal
    form (CNF) if it is a conjunction of clauses. A single clause counts
    as CNF, and (B ∧ C) is in CNF when B and C are in CNF. -/
@[blueprint "chap3__definition_3_4_7"]
def isCNF : PropFormulaNormalized → Prop
  | .conj B C => isCNF B ∧ isCNF C
  | A => isClause A

/-- Definition 3.4.7 (companion): A conjunctive term is a conjunction of
    literals. A single literal counts as a conjunctive term, and (B ∧ C)
    is a conjunctive term when B and C are conjunctive terms. -/
@[blueprint "chap3__definition_3_4_7"]
def isConjunctiveTerm : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg (.var _) => True
  | .conj B C => isConjunctiveTerm B ∧ isConjunctiveTerm C
  | _ => False

/-- Definition 3.4.7 (companion): A proposition is in disjunctive normal
    form (DNF) if it is a disjunction of conjunctive terms. A single
    conjunctive term counts as DNF, and (B ∨ C) is in DNF when B and C are in DNF. -/
@[blueprint "chap3__definition_3_4_7"]
def isDNF : PropFormulaNormalized → Prop
  | .disj B C => isDNF B ∧ isDNF C
  | A => isConjunctiveTerm A

-- ========= Definition 3.4.8: Negation Normal Form (NNF) =========

/-- Definition 3.4.8: The set of propositions in negation normal form
    (NNF) is the inductive closure of {P, ¬P | P ∈ PS} under the
    constructors C_∨ and C_∧. A proposition is in NNF if: (1) it is a
    propositional variable P; (2) it is ¬P for a variable P; (3) it is
    (A ∨ B) where A and B are in NNF; (4) it is (A ∧ B) where A and B
    are in NNF. -/
@[blueprint "chap3__definition_3_4_8" (main := true)]
def isNNF : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg (.var _) => True
  | .disj A B => isNNF A ∧ isNNF B
  | .conj A B => isNNF A ∧ isNNF B
  | _ => False

end PropFormulaNormalized

-- ========= Example 3.4.5: CNF via Search Tree =========

/-- Example 3.4.5: The formula (¬P ⊃ Q) ⊃ (¬R ⊃ S), used to
    demonstrate CNF extraction from a counter-example tree.
    P = var 0, Q = var 1, R = var 2, S = var 3. -/
@[blueprint "chap3__example_3_4_5" (main := true)]
def exCNFviaSearchFormula : PropFormulaNormalized :=
  .impl (.impl (.neg (.var 0)) (.var 1)) (.impl (.neg (.var 2)) (.var 3))

/-- Example 3.4.5 (companion): The CNF equivalent
    (¬Q ∨ R ∨ S) ∧ (¬P ∨ R ∨ S), obtained from the nonaxiom leaf
    sequents of the counter-example tree. -/
@[blueprint "chap3__example_3_4_5"]
def exCNFresult : PropFormulaNormalized :=
  .conj
    (.disj (.disj (.neg (.var 1)) (.var 2)) (.var 3))
    (.disj (.disj (.neg (.var 0)) (.var 2)) (.var 3))

-- ========= Example 3.4.6: DNF via Search Tree =========

/-- Example 3.4.6: The same formula (¬P ⊃ Q) ⊃ (¬R ⊃ S), placed on
    the left of the sequent to extract DNF. -/
@[blueprint "chap3__example_3_4_6" (main := true)]
def exDNFviaSearchFormula : PropFormulaNormalized :=
  .impl (.impl (.neg (.var 0)) (.var 1)) (.impl (.neg (.var 2)) (.var 3))

/-- Example 3.4.6 (companion): The DNF equivalent
    S ∨ R ∨ (¬P ∧ ¬Q), obtained from nonaxiom leaf sequents. -/
@[blueprint "chap3__example_3_4_6"]
def exDNFresult : PropFormulaNormalized :=
  .disj (.disj (.var 3) (.var 2)) (.conj (.neg (.var 0)) (.neg (.var 1)))

/-- Example 3.4.5: The displayed counterexample tree, with every rule application explicit. -/
@[blueprint "chap3__example_3_4_5"]
def exCNFSearchTree : DeductionTree ⟨[], [exCNFviaSearchFormula]⟩ :=
  let p : PropFormulaNormalized := .var 0
  let q : PropFormulaNormalized := .var 1
  let r : PropFormulaNormalized := .var 2
  let s : PropFormulaNormalized := .var 3
  let leftLeaf : DeductionTree ⟨[p], [r, s]⟩ := .leaf _
  let leftNegRight : DeductionTree ⟨[], [r, s, .neg p]⟩ :=
    .onePremise (.negRight [] [r, s] [] p) leftLeaf
  let leftNegLeft : DeductionTree ⟨[.neg r], [s, .neg p]⟩ :=
    .onePremise (.negLeft [] [] [s, .neg p] r) leftNegRight
  let leftBranch : DeductionTree ⟨[], [.neg p, .impl (.neg r) s]⟩ :=
    .onePremise (.implRight [] [.neg p] [] (.neg r) s) leftNegLeft
  let rightLeaf : DeductionTree ⟨[q], [r, s]⟩ := .leaf _
  let rightNegLeft : DeductionTree ⟨[.neg r, q], [s]⟩ :=
    .onePremise (.negLeft [] [q] [s] r) rightLeaf
  let rightBranch : DeductionTree ⟨[q], [.impl (.neg r) s]⟩ :=
    .onePremise (.implRight [q] [] [] (.neg r) s) rightNegLeft
  let subtree : DeductionTree ⟨[.impl (.neg p) q], [.impl (.neg r) s]⟩ :=
    .twoPremise (.implLeft [] [] [.impl (.neg r) s] (.neg p) q)
      leftBranch rightBranch
  .onePremise (.implRight [] [] [] (.impl (.neg p) q) (.impl (.neg r) s))
    subtree


/-- Example 3.4.6: The displayed counterexample tree, with every rule application explicit. -/
@[blueprint "chap3__example_3_4_6"]
def exDNFSearchTree : DeductionTree ⟨[exDNFviaSearchFormula], []⟩ :=
  let p : PropFormulaNormalized := .var 0
  let q : PropFormulaNormalized := .var 1
  let r : PropFormulaNormalized := .var 2
  let s : PropFormulaNormalized := .var 3
  let leftLeaf : DeductionTree ⟨[], [p, q]⟩ := .leaf _
  let leftNeg : DeductionTree ⟨[.neg p], [q]⟩ :=
    .onePremise (.negLeft [] [] [q] p) leftLeaf
  let leftBranch : DeductionTree ⟨[], [.impl (.neg p) q]⟩ :=
    .onePremise (.implRight [] [] [] (.neg p) q) leftNeg
  let middleLeaf : DeductionTree ⟨[r], []⟩ := .leaf _
  let middleNeg : DeductionTree ⟨[], [.neg r]⟩ :=
    .onePremise (.negRight [] [] [] r) middleLeaf
  let rightBranch : DeductionTree ⟨[.impl (.neg r) s], []⟩ :=
    .twoPremise (.implLeft [] [] [] (.neg r) s) middleNeg (.leaf ⟨[s], []⟩)
  .twoPremise (.implLeft [] [] [] (.impl (.neg p) q) (.impl (.neg r) s))
    leftBranch rightBranch

-- ========= Example 3.4.7: CNF via NNF Conversion =========

/-- Example 3.4.7: The formula (¬P ⊃ Q) ⊃ (¬R ⊃ S), used to
    demonstrate the NNF-based CNF conversion method. -/
@[blueprint "chap3__example_3_4_7" (main := true)]
def exCNFviaNNFFormula : PropFormulaNormalized :=
  .impl (.impl (.neg (.var 0)) (.var 1)) (.impl (.neg (.var 2)) (.var 3))

/-- Example 3.4.7 (companion): After eliminating ⊃ using
    (B ⊃ C) ≃ (¬B ∨ C), we get (¬(¬¬P ∨ Q)) ∨ (¬¬R ∨ S). -/
@[blueprint "chap3__example_3_4_7"]
def exImplEliminated : PropFormulaNormalized :=
  .disj
    (.neg (.disj (.neg (.neg (.var 0))) (.var 1)))
    (.disj (.neg (.neg (.var 2))) (.var 3))

/-- Example 3.4.7 (companion): After converting to NNF using double
    negation and De Morgan's laws, we obtain (¬P ∧ ¬Q) ∨ (R ∨ S). -/
@[blueprint "chap3__example_3_4_7"]
def exNNFConverted : PropFormulaNormalized :=
  .disj (.conj (.neg (.var 0)) (.neg (.var 1))) (.disj (.var 2) (.var 3))

/-- Example 3.4.7 (companion): After applying distributivity to
    (¬P ∧ ¬Q) ∨ (R ∨ S), we obtain the CNF
    (¬P ∨ R ∨ S) ∧ (¬Q ∨ R ∨ S). -/
@[blueprint "chap3__example_3_4_7"]
def exCNFviaNNFResult : PropFormulaNormalized :=
  .conj
    (.disj (.disj (.neg (.var 0)) (.var 2)) (.var 3))
    (.disj (.disj (.neg (.var 1)) (.var 2)) (.var 3))

-- ========= Lemma 3.4.5: CNF Transformation Identities =========















-- ========= Helpers: logEquivN transitivity =========



-- ========= Helpers: NNF conversion via polarity parameter =========

def toNNFaux : Bool → PropFormulaNormalized → PropFormulaNormalized
  | true, .var n => .var n
  | false, .var n => .neg (.var n)
  | true, .neg A => toNNFaux false A
  | false, .neg A => toNNFaux true A
  | true, .conj A B => .conj (toNNFaux true A) (toNNFaux true B)
  | false, .conj A B => .disj (toNNFaux false A) (toNNFaux false B)
  | true, .disj A B => .disj (toNNFaux true A) (toNNFaux true B)
  | false, .disj A B => .conj (toNNFaux false A) (toNNFaux false B)
  | true, .impl A B => .disj (toNNFaux false A) (toNNFaux true B)
  | false, .impl A B => .conj (toNNFaux true A) (toNNFaux false B)

abbrev toNNF (A : PropFormulaNormalized) : PropFormulaNormalized := toNNFaux true A









-- ========= Helpers: CNF/DNF existence proofs =========

-- Combine normal forms with arbitrary binary grouping.












-- Helper: convert NNF to CNF




-- Combine normal forms with arbitrary binary grouping.
























-- ========= Lemma 3.4.5: CNF Transformation Theorem =========

/-- The source's restriction to the connectives ∨, ∧, and ¬. -/
@[blueprint "chap3__lemma_3_4_5"]
def usesOnlyAndOrNot : PropFormulaNormalized → Prop
  | .var _ => True
  | .neg A => usesOnlyAndOrNot A
  | .conj A B | .disj A B => usesOnlyAndOrNot A ∧ usesOnlyAndOrNot B
  | .impl _ _ => False

/-- Finite application of exactly the seven identities of Lemma 3.4.5,
    in either direction and inside ∧/∨/¬ contexts. The formula indices
    record the actual endpoints of the syntactic derivation. -/
@[blueprint "chap3__lemma_3_4_5"]
inductive CNFRewrite : PropFormulaNormalized → PropFormulaNormalized → Prop where
  | doubleNeg (A) : CNFRewrite (.neg (.neg A)) A
  | deMorganConj (A B) : CNFRewrite (.neg (.conj A B)) (.disj (.neg A) (.neg B))
  | deMorganDisj (A B) : CNFRewrite (.neg (.disj A B)) (.conj (.neg A) (.neg B))
  | distributeLeft (A B C) : CNFRewrite (.disj A (.conj B C))
      (.conj (.disj A B) (.disj A C))
  | distributeRight (A B C) : CNFRewrite (.disj (.conj B C) A)
      (.conj (.disj B A) (.disj C A))
  | assocConj (A B C) : CNFRewrite (.conj (.conj A B) C) (.conj A (.conj B C))
  | assocDisj (A B C) : CNFRewrite (.disj (.disj A B) C) (.disj A (.disj B C))
  | refl (A) : CNFRewrite A A
  | symm {A B} : CNFRewrite A B → CNFRewrite B A
  | trans {A B C} : CNFRewrite A B → CNFRewrite B C → CNFRewrite A C
  | neg {A B} : CNFRewrite A B → CNFRewrite (.neg A) (.neg B)
  | conj {A A' B B'} : CNFRewrite A A' → CNFRewrite B B' →
      CNFRewrite (.conj A B) (.conj A' B')
  | disj {A A' B B'} : CNFRewrite A A' → CNFRewrite B B' →
      CNFRewrite (.disj A B) (.disj A' B')

theorem CNFRewrite.sound {A B : PropFormulaNormalized} (h : CNFRewrite A B) :
    logEquivN A B := by
  apply (tautological_equiv_iff_equal_evalN A B).mpr
  intro v
  induction h with
  | doubleNeg A =>
    simp only [evalExtN]
    cases evalExtN v A <;> rfl
  | deMorganConj A B | deMorganDisj A B =>
    simp only [evalExtN]
    cases evalExtN v A <;> cases evalExtN v B <;> rfl
  | distributeLeft A B C | distributeRight A B C | assocConj A B C | assocDisj A B C =>
    simp only [evalExtN]
    cases evalExtN v A <;> cases evalExtN v B <;> cases evalExtN v C <;> rfl
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | neg _ ih => exact congrArg hNeg ih
  | conj _ _ ih₁ ih₂ => simp only [evalExtN, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [evalExtN, ih₁, ih₂]









/-- Lemma 3.4.5: A proposition using only ∨, ∧, and ¬ can be transformed
    into an equivalent CNF by the seven listed identities. -/
@[blueprint "chap3__lemma_3_4_5" (main := true)]
theorem cnf_transformation (A : PropFormulaNormalized) (hA : usesOnlyAndOrNot A) :
    ∃ A' : PropFormulaNormalized,
      PropFormulaNormalized.isCNF A' ∧ CNFRewrite A A' ∧ logEquivN A A' 

-- ========= Lemma 3.4.4: NNF Existence =========

/-- Lemma 3.4.4: Every proposition is equivalent to a proposition
    in NNF. The proof eliminates implication and equivalence
    connectives using functional completeness and tautological
    equivalences, then pushes negations inward using double
    negation and De Morgan laws. -/
@[blueprint "chap3__lemma_3_4_4" (main := true)]
theorem nnf_existence (A : PropFormulaNormalized) :
    ∃ A' : PropFormulaNormalized, PropFormulaNormalized.isNNF A' ∧ logEquivN A A' 

-- ========= Theorem 3.4.2: CNF and DNF Existence =========

/-- Theorem 3.4.2 (CNF): For every proposition A, there exists a
    proposition A' in CNF such that A and A' are logically
    equivalent. -/
@[blueprint "chap3__theorem_3_4_2" (main := true)]
theorem cnf_existence (A : PropFormulaNormalized) :
    ∃ A' : PropFormulaNormalized, PropFormulaNormalized.isCNF A' ∧ logEquivN A A' 

/-- Theorem 3.4.2 (DNF): For every proposition A, there exists a
    proposition A'' in DNF such that A and A'' are logically
    equivalent. -/
@[blueprint "chap3__theorem_3_4_2" (main := true)]
theorem dnf_existence (A : PropFormulaNormalized) :
    ∃ A'' : PropFormulaNormalized,
      PropFormulaNormalized.isDNF A'' ∧ logEquivN A A'' 

/-- Theorem 3.4.2: For every proposition A, a proposition A' in CNF can be
    found such that A ≡ A', and similarly a proposition A'' in DNF can be
    found such that A ≡ A''. -/
@[blueprint "chap3__theorem_3_4_2" (main := true)]
theorem theorem_3_4_2 (A : PropFormulaNormalized) :
    (∃ A', PropFormulaNormalized.isCNF A' ∧ logEquivN A A') ∧
    (∃ A'', PropFormulaNormalized.isDNF A'' ∧ logEquivN A A'') 

-- ========= Example 3.4.5: CNF Verification Theorems =========

/-- Example 3.4.5 (companion): The result formula exCNFresult is
    in conjunctive normal form. -/
@[blueprint "chap3__example_3_4_5"]
theorem exCNFresult_isCNF : PropFormulaNormalized.isCNF exCNFresult 

/-- Example 3.4.5 (companion): The CNF formula exCNFresult is
    logically equivalent to the original formula
    exCNFviaSearchFormula. -/
@[blueprint "chap3__example_3_4_5"]
theorem exCNFresult_equiv :
    logEquivN exCNFviaSearchFormula exCNFresult 

-- ========= Example 3.4.6: DNF Verification Theorems =========

/-- Example 3.4.6 (companion): The result formula exDNFresult is
    in disjunctive normal form. -/
@[blueprint "chap3__example_3_4_6"]
theorem exDNFresult_isDNF : PropFormulaNormalized.isDNF exDNFresult 

/-- Example 3.4.6 (companion): The DNF formula exDNFresult is
    logically equivalent to the original formula
    exDNFviaSearchFormula. -/
@[blueprint "chap3__example_3_4_6"]
theorem exDNFresult_equiv :
    logEquivN exDNFviaSearchFormula exDNFresult 

-- ========= Example 3.4.7: NNF and CNF Verification Theorems =========

/-- Example 3.4.7 (companion): The formula exNNFConverted is in
    negation normal form. -/
@[blueprint "chap3__example_3_4_7"]
theorem exNNFConverted_isNNF :
    PropFormulaNormalized.isNNF exNNFConverted 

/-- Example 3.4.7 (companion): The formula exCNFviaNNFResult is
    in conjunctive normal form. -/
@[blueprint "chap3__example_3_4_7"]
theorem exCNFviaNNFResult_isCNF :
    PropFormulaNormalized.isCNF exCNFviaNNFResult 

/-- Example 3.4.7 (companion): The CNF formula exCNFviaNNFResult
    is logically equivalent to the original formula
    exCNFviaNNFFormula. -/
@[blueprint "chap3__example_3_4_7"]
theorem exCNFviaNNFResult_equiv :
    logEquivN exCNFviaNNFFormula exCNFviaNNFResult 

/-- Example 3.4.7: Eliminating implication gives the displayed formula. -/
@[blueprint "chap3__example_3_4_7"]
theorem exImplEliminated_equiv : logEquivN exCNFviaNNFFormula exImplEliminated 

/-- Example 3.4.7: The displayed NNF is obtained by the permitted identities. -/
@[blueprint "chap3__example_3_4_7"]
theorem exNNFConverted_rewrite : CNFRewrite exImplEliminated exNNFConverted 

/-- Example 3.4.7: The displayed CNF follows by distribution. -/
@[blueprint "chap3__example_3_4_7"]
theorem exCNFviaNNFResult_rewrite : CNFRewrite exNNFConverted exCNFviaNNFResult 

/-- Example 3.4.7: The first CNF in the nonuniqueness example. -/
@[blueprint "chap3__example_3_4_7"]
def exCNFNonuniqueFirst : PropFormulaNormalized :=
  .conj (.disj (.var 0) (.var 1)) (.disj (.neg (.var 0)) (.var 2))

/-- Example 3.4.7: Adding the clause Q ∨ R gives a different CNF. -/
@[blueprint "chap3__example_3_4_7"]
def exCNFNonuniqueSecond : PropFormulaNormalized :=
  .conj exCNFNonuniqueFirst (.disj (.var 1) (.var 2))

/-- Example 3.4.7: The displayed distinct CNFs are logically equivalent. -/
@[blueprint "chap3__example_3_4_7"]
theorem exCNF_nonuniqueness :
    PropFormulaNormalized.isCNF exCNFNonuniqueFirst ∧
    PropFormulaNormalized.isCNF exCNFNonuniqueSecond ∧
    exCNFNonuniqueFirst ≠ exCNFNonuniqueSecond ∧
    logEquivN exCNFNonuniqueFirst exCNFNonuniqueSecond 

/-- Example 3.4.5: The two nonaxiom leaves in displayed tree order. -/
@[blueprint "chap3__example_3_4_5"]
theorem exCNFSearchTree_leaves : exCNFSearchTree.leaves =
    [⟨[.var 0], [.var 2, .var 3]⟩, ⟨[.var 1], [.var 2, .var 3]⟩] 

/-- Example 3.4.6: The three nonaxiom leaves in displayed tree order. -/
@[blueprint "chap3__example_3_4_6"]
theorem exDNFSearchTree_leaves : exDNFSearchTree.leaves =
    [⟨[], [.var 0, .var 1]⟩, ⟨[.var 2], []⟩, ⟨[.var 3], []⟩] 

/-- Example 3.4.5: Neither displayed leaf is an axiom. -/
@[blueprint "chap3__example_3_4_5"]
theorem exCNFSearchTree_nonaxiom_leaves : ∀ s ∈ exCNFSearchTree.leaves, ¬ isAxiom s 

/-- Example 3.4.6: None of the displayed leaves is an axiom. -/
@[blueprint "chap3__example_3_4_6"]
theorem exDNFSearchTree_nonaxiom_leaves : ∀ s ∈ exDNFSearchTree.leaves, ¬ isAxiom s 

/-- Example 3.4.5: Every formula in every displayed leaf is atomic. -/
@[blueprint "chap3__example_3_4_5"]
theorem exCNFSearchTree_atomic_leaves :
    ∀ s ∈ exCNFSearchTree.leaves, ∀ A ∈ s.antecedent ++ s.succedent,
      ∃ n, A = .var n 

/-- Example 3.4.6: Every formula in every displayed leaf is atomic. -/
@[blueprint "chap3__example_3_4_6"]
theorem exDNFSearchTree_atomic_leaves :
    ∀ s ∈ exDNFSearchTree.leaves, ∀ A ∈ s.antecedent ++ s.succedent,
      ∃ n, A = .var n 

end LCS.Propositional.Systems.G.NormalForms
