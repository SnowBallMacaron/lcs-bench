import LCS.Item
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import Attach
import LCS.FirstOrder.SemanticsN.ProofsStamp

/-! # FirstOrder.SemanticsN
    Semantics for FormulaN (§5.3.8+ normalized formulae).
    Self-contained on FormulaN. Uses Structure, Assignment, termEval
    from Basic.lean (via transitive import through SyntaxN).
-/

namespace LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- FormulaN evaluation
-- ===================================================================

/-- Definition 5.3.6.a: The function A_M : [V → M] → Prop defined by
recursion on normalized formulae. The atomic clauses define A_M pointwise
on assignments; the non-atomic clauses lift the connectives per Def 5.3.4
(andM, orM, implM, negM), and the quantifier clauses quantify over domain
elements via assignUpdate. -/
@[blueprint "chap5__definition_5_3_6"]
def formulaEvalN {L : Language} (M : Structure L) :
    FormulaN L → Assignment M → Prop
  | .predN P ts => fun s => M.interpPred P (fun i => termEval M s (ts i))
  | .eq_ _ t1 t2 => fun s => termEval M s t1 = termEval M s t2
  | .neg A => negM (formulaEvalN M A)
  | .conj A B => andM (formulaEvalN M A) (formulaEvalN M B)
  | .disj A B => orM (formulaEvalN M A) (formulaEvalN M B)
  | .impl A B => implM (formulaEvalN M A) (formulaEvalN M B)
  | .all i A =>
      fun s => ∀ a : M.carrier, formulaEvalN M A (assignUpdate s i a)
  | .ex i A =>
      fun s => ∃ a : M.carrier, formulaEvalN M A (assignUpdate s i a)

-- ===================================================================
-- Satisfaction, validity, etc.
-- ===================================================================

/-- Definition 5.3.7 (companion — N variant): A formula is satisfiable in M iff some assignment makes it true. -/
@[blueprint "chap5__definition_5_3_7"]
def satisfiableInN {L : Language} (M : Structure L)
    (A : FormulaN L) : Prop :=
  ∃ s : Assignment M, formulaEvalN M A s

/-- Definition 5.3.7.a: A formula is satisfiable iff satisfiable in some structure. -/
@[blueprint "chap5__definition_5_3_7"]
def satisfiableN {L : Language} (A : FormulaN L) : Prop :=
  ∃ (M : Structure L), satisfiableInN M A

/-- Definition 5.3.7 (companion — N variant): A formula is valid in M iff true under every assignment. -/
@[blueprint "chap5__definition_5_3_7"]
def validInN {L : Language} (M : Structure L)
    (A : FormulaN L) : Prop :=
  ∀ s : Assignment M, formulaEvalN M A s

/-- Definition 5.3.7 (companion — N variant): A formula is universally valid iff valid in every structure. -/
@[blueprint "chap5__definition_5_3_7"]
def universallyValidN {L : Language} (A : FormulaN L) : Prop :=
  ∀ (M : Structure L), validInN M A

-- ===================================================================
-- Coincidence lemmas (term and formula evaluation depends only on FV)
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Part1, LCS.FirstOrder.SemanticsN.Substitution, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
/-- Term evaluation depends only on the values of free variables.
Proof-body helper for coincidenceLemmaN. -/
theorem termCoincidence {L : Language} (S : Structure L)
    (t : Term L) (s1 s2 : Assignment S)
    (h : ∀ y, y ∈ termFV t → s1 y = s2 y) :
    termEval S s1 t = termEval S s2 t := by
-- BEGIN PROOF
  induction t with
  | var x => simp [termEval]; exact h x rfl
  | const c => simp [termEval]
  | func f ts ih =>
    simp [termEval]; congr 1; funext j
    exact ih j (fun y hy => h y ⟨j, hy⟩)

/-- Lemma 5.3.3: Coincidence lemma for FormulaN: if two assignments agree on FV(A),
then A evaluates the same under both. -/
@[blueprint "chap5__lemma_5_3_3_a" (main := true)]
theorem coincidenceLemmaN {L : Language} (M : Structure L)
    (A : FormulaN L) (s1 s2 : Assignment M)
    (h : ∀ y, y ∈ formulaFVN A → s1 y = s2 y) :
    formulaEvalN M A s1 ↔ formulaEvalN M A s2 

-- ===================================================================
-- Formula predicates for FormulaN
-- ===================================================================

/-- Theorem 5.4.1 (companion — N variant): A FormulaN contains no eq_
sub-formula (language without equality). -/
@[blueprint "chap5__theorem_5_6_1"]
def formulaNoEq {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => False
  | .neg A => formulaNoEq A
  | .conj A B => formulaNoEq A ∧ formulaNoEq B
  | .disj A B => formulaNoEq A ∧ formulaNoEq B
  | .impl A B => formulaNoEq A ∧ formulaNoEq B
  | .all _ A => formulaNoEq A
  | .ex _ A => formulaNoEq A

-- retained: used by LCS.CutElim.Interpolation.KeyLemma, LCS.CutElim.Interpolation.QuantifierCases, LCS.FirstOrder.Completeness.InfiniteSearch, LCS.FirstOrder.Gentzen.Hintikka.Construction
/-- formulaSubstN preserves formulaNoEq. Proof-body helper. -/
theorem formulaSubstN_noEq {L : Language} (A : FormulaN L) (t : Term L) (x : Nat)
    (h : formulaNoEq A) : formulaNoEq (formulaSubstN A t x) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => exact h.elim
  | neg A ih => simp [formulaSubstN, formulaNoEq]; exact ih h
  | conj A B ihA ihB => simp [formulaSubstN, formulaNoEq]; exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => simp [formulaSubstN, formulaNoEq]; exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => simp [formulaSubstN, formulaNoEq]; exact ⟨ihA h.1, ihB h.2⟩
  | all y A ih =>
    simp only [formulaSubstN]
    split
    · simp only [formulaNoEq]; exact ih h
    · exact h
  | ex y A ih =>
    simp only [formulaSubstN]
    split
    · simp only [formulaNoEq]; exact ih h
    · exact h

/-- Theorem 5.5.1 (companion — N variant): A FormulaN is quantifier-free. -/
@[blueprint "chap5__theorem_5_5_1"]
def isQuantifierFree {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => isQuantifierFree A
  | .conj A B => isQuantifierFree A ∧ isQuantifierFree B
  | .disj A B => isQuantifierFree A ∧ isQuantifierFree B
  | .impl A B => isQuantifierFree A ∧ isQuantifierFree B
  | .all _ _ => False
  | .ex _ _ => False

-- ===================================================================
-- Set-level satisfaction and model predicates
-- ===================================================================

/-- Definition 5.3.7 (companion — N variant): A set of FormulaN is satisfiable iff there exists a structure and
assignment making all formulas true. -/
@[blueprint "chap5__definition_5_3_7"]
def satisfiableSetN {L : Language} (Gamma : Set (FormulaN L)) : Prop :=
  ∃ (M : Structure L) (s : Assignment M),
    ∀ A, A ∈ Gamma → formulaEvalN M A s

/-- Definition 5.3.7 (companion — N variant): A set of FormulaN is satisfiable in a specific structure M. -/
@[blueprint "chap5__definition_5_3_7"]
def satisfiableSetInN {L : Language} (M : Structure L)
    (Gamma : Set (FormulaN L)) : Prop :=
  ∃ (s : Assignment M), ∀ A, A ∈ Gamma → formulaEvalN M A s

/-- Theorem 5.5.3 (companion — N variant): A set of FormulaN is finitely satisfiable iff every nonempty
finite subset is satisfiable. -/
@[blueprint "chap5__theorem_5_5_3"]
def finiteSubsetSatisfiableN {L : Language}
    (Gamma : Set (FormulaN L)) : Prop :=
  ∀ (cs : List (FormulaN L)),
    cs ≠ [] →
    (∀ c, c ∈ cs → c ∈ Gamma) →
    satisfiableSetN (fun A => A ∈ cs)

/-- Theorem 5.4.1 (companion — N variant): A structure has a finite domain (surjection from Fin n for some n). -/
@[blueprint "chap5__theorem_5_4_1"]
def isFiniteDomain {L : Language} (M : Structure L) : Prop :=
  ∃ (n : Nat) (f : Fin n → M.carrier), Function.Surjective f

/-- Theorem 5.4.1 (companion — N variant): A structure has a countable domain (surjection from Nat). -/
@[blueprint "chap5__theorem_5_4_1"]
def isCountableDomain {L : Language} (M : Structure L) : Prop :=
  ∃ (f : Nat → M.carrier), Function.Surjective f

/-- Theorem 5.6.2 (companion — N variant): A structure has an at-most-countable
domain (alias for isCountableDomain). Appears in the statement of
`lowenheim_skolem_eq` (Thm 5.6.2) and the countable-model variant of
`consistent_implies_satisfiable_eq` (Thm 5.6.4). -/
@[blueprint "chap5__theorem_5_6_2"]
abbrev isAtMostCountable {L : Language} (M : Structure L) : Prop :=
  isCountableDomain M

end LCS.FirstOrder.SemanticsN
