import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.Herbrand.PrenexForm.Part1.ProofsStamp

section
namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

/-- Definition 7.2.1 (companion type): An enumeration of the two quantifier kinds: universal (forall) and existential (exists). Each Q_i in the quantifier prefix of a prenex formula belongs to {forall, exists}. -/
@[blueprint "chap7__definition_7_2_1"]
inductive QuantifierKind : Type where
  /-- Universal quantifier (forall) -/
  | universal : QuantifierKind
  /-- Existential quantifier (exists) -/
  | existential : QuantifierKind

-- ===================================================================
-- Example 7.2.1 (companion type): ExPred_7_2_1
-- ===================================================================

/-- Example 7.2.1 (companion type): Predicate symbols for Example 7.2.1: unary P, unary Q, and binary R. These are the nonlogical predicate symbols used in the example formula A = forall x(P(x) or not exists y(Q(y) and R(x,y))) or not(P(y) and not forall x P(x)). -/
@[blueprint "chap7__example_7_2_1"]
inductive ExPred_7_2_1 : Type where
  /-- Unary predicate P -/
  | P : ExPred_7_2_1
  /-- Unary predicate Q -/
  | Q : ExPred_7_2_1
  /-- Binary predicate R -/
  | R : ExPred_7_2_1

-- ===================================================================
-- Definition 7.2.1 (companion): isPrenex
-- ===================================================================

/-- Definition 7.2.1: A formula is a prenex formula (or in prenex form) iff either it contains no quantifiers, or it is of the form Q_1 x_1 ... Q_n x_n B where B is quantifier-free. Defined recursively: isPrenex A holds if FirstOrder.SemanticsN.isQuantifierFree A, or A = all x B with isPrenex B, or A = ex x B with isPrenex B. -/
@[blueprint "chap7__definition_7_2_1" (main := true)]
def isPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => isPrenex A
  | .ex _ A => isPrenex A
  | A => FirstOrder.SemanticsN.isQuantifierFree A

-- ===================================================================
-- Definition 7.2.1 (companion): prenexMatrix
-- ===================================================================

/-- Definition 7.2.1 (companion def): Extracts the quantifier-free matrix B from a formula by stripping all leading quantifiers. For a prenex formula Q_1 x_1 ... Q_n x_n B, this returns B. -/

@[blueprint "chap7__definition_7_2_1"]
def prenexMatrix {L : Language} : FormulaN L → FormulaN L
  | .all _ A => prenexMatrix A
  | .ex _ A => prenexMatrix A
  | A => A

-- ===================================================================
-- Definition 7.2.1 (companion): prenexPrefix
-- ===================================================================

/-- Definition 7.2.1 (companion def): Extracts the quantifier prefix as a list of (quantifier kind, variable) pairs. For a prenex formula Q_1 x_1 ... Q_n x_n B, this returns [(Q_1, x_1), ..., (Q_n, x_n)]. -/
@[blueprint "chap7__definition_7_2_1"]
def prenexPrefix {L : Language} :
    FormulaN L → List (QuantifierKind × Nat)
  | .all x A => (QuantifierKind.universal, x) :: prenexPrefix A
  | .ex x A => (QuantifierKind.existential, x) :: prenexPrefix A
  | _ => []

end LCS.Herbrand.PrenexForm
end

section
namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
namespace QuantifierKind

/-- Theorem 7.2.1 (required helper): Swaps universal and existential quantifier kinds. For each Q_i, let R_i = forall if Q_i = exists and R_i = exists if Q_i = forall. Used in the negation case of prenex conversion. -/
@[blueprint "chap7__theorem_7_2_1"]
def dual : QuantifierKind → QuantifierKind
  | .universal => .existential
  | .existential => .universal

end QuantifierKind
end LCS.Herbrand.PrenexForm
end

section
namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

/-- Theorem 7.2.1 (required helper): Infrastructure for the constructive proof of Thm 7.2.1. Rebuilds a formula from a quantifier prefix list and a quantifier-free body: for each (Q_i, x_i) in the prefix (outermost first), prepend `FormulaN.all x_i` or `FormulaN.ex x_i` according to Q_i, finally wrapping the body. -/
@[blueprint "chap7__theorem_7_2_1"]
def toPrenexHelper {L : Language} :
    List (QuantifierKind × Nat) → FormulaN L → FormulaN L
  | [], body => body
  | (QuantifierKind.universal, x) :: rest, body =>
    FormulaN.all x (toPrenexHelper rest body)
  | (QuantifierKind.existential, x) :: rest, body =>
    FormulaN.ex x (toPrenexHelper rest body)

/-- Theorem 7.2.1 (required helper): Dual the quantifier kinds in a
    prefix list (used for negation case of prenex conversion). -/
@[blueprint "chap7__theorem_7_2_1"]
def dualPrefix :
    List (QuantifierKind × Nat) → List (QuantifierKind × Nat) :=
  List.map (fun (q, x) => (q.dual, x))

/-- Theorem 7.2.1 (required helper): Infrastructure for the constructive proof of Thm 7.2.1. The raw prenex conversion function that transforms a formula into prenex form by extracting quantifier prefixes and combining them. This function assumes the input has been rectified (all bound variables are distinct), so concatenating prefixes is sound. - Atomic formulae: returned unchanged. - Negation: dualize prefix, negate matrix. - Disjunction: concatenate prefixes, disjoin matrices. - Conjunction: concatenate prefixes, conjoin matrices. - Implication: dualize left prefix, concatenate with right, build implication of matrices. - Universal/existential: prepend quantifier to prenex of body. -/
@[blueprint "chap7__theorem_7_2_1"]
def toPrenexRaw {L : Language} : FormulaN L → FormulaN L
  | .predN P ts => .predN P ts
  | .eq_ hL t1 t2 => .eq_ hL t1 t2
  | .neg A =>
    let pA := toPrenexRaw A
    toPrenexHelper (dualPrefix (prenexPrefix pA))
      (.neg (prenexMatrix pA))
  | .conj A B =>
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    toPrenexHelper
      (prenexPrefix pA ++ prenexPrefix pB)
      (.conj (prenexMatrix pA) (prenexMatrix pB))
  | .disj A B =>
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    toPrenexHelper
      (prenexPrefix pA ++ prenexPrefix pB)
      (.disj (prenexMatrix pA) (prenexMatrix pB))
  | .impl A B =>
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    toPrenexHelper
      (dualPrefix (prenexPrefix pA) ++
        prenexPrefix pB)
      (.impl (prenexMatrix pA) (prenexMatrix pB))
  | .all x A =>
    let pA := toPrenexRaw A
    .all x pA
  | .ex x A =>
    let pA := toPrenexRaw A
    .ex x pA

-- ===================================================================
-- rectifyAuxN / rectifyN: FormulaN versions of rectifyAux / rectify
-- ===================================================================

/-- Theorem 7.2.1 (required helper): rectifyAux for FormulaN: renames
    bound variables to fresh names. -/
@[blueprint "chap7__theorem_7_2_1"]
def rectifyAuxN {L : Language} : FormulaN L → (Nat → Nat) → Nat → FormulaN L × Nat
  | .predN P ts, sigma, n => (.predN P (fun j => termVarMap sigma (ts j)), n)
  | .eq_ hL t1 t2, sigma, n => (.eq_ hL (termVarMap sigma t1) (termVarMap sigma t2), n)
  | .neg A, sigma, n => let (A', n') := rectifyAuxN A sigma n; (.neg A', n')
  | .conj A B, sigma, n =>
    let (A', n') := rectifyAuxN A sigma n
    let (B', n'') := rectifyAuxN B sigma n'
    (.conj A' B', n'')
  | .disj A B, sigma, n =>
    let (A', n') := rectifyAuxN A sigma n
    let (B', n'') := rectifyAuxN B sigma n'
    (.disj A' B', n'')
  | .impl A B, sigma, n =>
    let (A', n') := rectifyAuxN A sigma n
    let (B', n'') := rectifyAuxN B sigma n'
    (.impl A' B', n'')
  | .all i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxN A sigma' (n + 1)
    (.all n A', n')
  | .ex i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxN A sigma' (n + 1)
    (.ex n A', n')

/-- Theorem 7.2.1 (required helper): Infrastructure for the constructive proof of Thm 7.2.1. rectify for FormulaN: produces a rectified formula where all bound variables are distinct and fresh. -/
@[blueprint "chap7__theorem_7_2_1"]
def rectifyN {L : Language} (A : FormulaN L) : FormulaN L :=
  (rectifyAuxN A id (formulaMaxVarN A + 1)).1

/-- Theorem 7.2.1 (required helper): The constructive prenex conversion function. First rectifies the input formula (renaming bound variables to be distinct), then applies toPrenexRaw. Rectification ensures that when quantifier prefixes from different branches are concatenated, there is no variable shadowing. -/
@[blueprint "chap7__theorem_7_2_1"]
def toPrenex {L : Language} (A : FormulaN L) : FormulaN L :=
  toPrenexRaw (rectifyN A)

-- ===================================================================
-- Example 7.2.1: Language and formula definitions
-- ===================================================================

/-- Example 7.2.1 (companion def): The arity function for ExPred_7_2_1:
    P has arity 1, Q has arity 1, R has arity 2. -/
@[blueprint "chap7__example_7_2_1"]
def exPredArity_7_2_1 : ExPred_7_2_1 → Nat
  | .P => 1
  | .Q => 1
  | .R => 2

/-- Example 7.2.1 (companion def): Language with predicates P (arity 1),
    Q (arity 1), R (arity 2), no function or constant symbols. -/
@[blueprint "chap7__example_7_2_1"]
def exLang_7_2_1 : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPred_7_2_1
  predArity := exPredArity_7_2_1

-- Variable assignments for Example 7.2.1: x = 0, y = 1, v = 2, z = 3

/-- Example 7.2.1: The original formula A (x = 0, y = 1):
    A = forall x(P(x) or not exists y(Q(y) and R(x, y))) or not(P(y) and not forall x P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exampleFormula_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
        (FormulaN.neg
          (FormulaN.ex 1
            (FormulaN.conj
              (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
              (FormulaN.predN ExPred_7_2_1.R
                (vec2 (Term.var 0) (Term.var 1))))))))
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
        (FormulaN.neg
          (FormulaN.all 0
            (FormulaN.predN ExPred_7_2_1.P
              (fun _ => Term.var 0))))))

/-- Example 7.2.1: Prenex form of not exists y(Q(y) and R(x, y)):
    forall y not(Q(y) and R(x, y)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep1_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 1
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
        (FormulaN.predN ExPred_7_2_1.R
          (vec2 (Term.var 0) (Term.var 1)))))

/-- Example 7.2.1: Prenex form of forall x(P(x) or not exists y(Q(y) and R(x, y))):
    forall x forall y(P(x) or not(Q(y) and R(x, y))). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep2_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.all 1
      (FormulaN.disj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
        (FormulaN.neg
          (FormulaN.conj
            (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
            (FormulaN.predN ExPred_7_2_1.R
              (vec2 (Term.var 0) (Term.var 1)))))))

/-- Example 7.2.1: Prenex form of not forall x P(x):
    exists x not P(x). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep3_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.ex 0
    (FormulaN.neg
      (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0)))

/-- Example 7.2.1: Prenex form of (P(y) and not forall x P(x)):
    exists x(P(y) and not P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep4_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.ex 0
    (FormulaN.conj
      (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
      (FormulaN.neg
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))))

/-- Example 7.2.1: Prenex form of not(P(y) and not forall x P(x)):
    forall x not(P(y) and not P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep5_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
        (FormulaN.neg
          (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0)))))

/-- Example 7.2.1: Final prenex form of A (y -> v = 2, x -> z = 3; y = 1 remains free):
    forall x forall v forall z((P(x) or not(Q(v) and R(x, v))) or not(P(y) and not P(z))). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexFinal_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.all 2
      (FormulaN.all 3
        (FormulaN.disj
          (FormulaN.disj
            (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
            (FormulaN.neg
              (FormulaN.conj
                (FormulaN.predN ExPred_7_2_1.Q
                  (fun _ => Term.var 2))
                (FormulaN.predN ExPred_7_2_1.R
                  (vec2 (Term.var 0) (Term.var 2))))))
          (FormulaN.neg
            (FormulaN.conj
              (FormulaN.predN ExPred_7_2_1.P
                (fun _ => Term.var 1))
              (FormulaN.neg
                (FormulaN.predN ExPred_7_2_1.P
                  (fun _ => Term.var 3))))))))

/-- Example 7.2.1: The prenex form of exampleFormula_7_2_1 is exPrenexFinal_7_2_1. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenex_equiv_7_2_1 :
    foLogEquivN exampleFormula_7_2_1 exPrenexFinal_7_2_1 

end LCS.Herbrand.PrenexForm
end

section
namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

-- retained: used by LCS.Herbrand.NNFHauptsatz.Soundness
/-- When x is not free in formula F, changing the assignment at x does
    not affect the evaluation of F. A direct consequence of the
    coincidence lemma (Lemma 5.3.3). -/
theorem formulaEval_assignUpdate_irrelevant {L : Language}
    {M : Structure L} (s : Assignment M) (x : Nat) (a : M.carrier)
    (F : FormulaN L) (hfree : ¬ Membership.mem (formulaFVN F) x) :
    formulaEvalN M F (assignUpdate s x a) ↔ formulaEvalN M F s :=
-- BEGIN PROOF
  coincidenceLemmaN M F (assignUpdate s x a) s (fun y hy => by
    unfold assignUpdate; split
    · rename_i heq; subst heq; exact absurd hy hfree
    · rfl)

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- A quantifier-free formula is prenex. The isPrenex predicate reduces
    to FirstOrder.SemanticsN.isQuantifierFree for non-quantifier formulas. -/
theorem qf_isPrenex {L : Language} (A : FormulaN L)
    (h : FirstOrder.SemanticsN.isQuantifierFree A) : isPrenex A := by
-- BEGIN PROOF
  cases A <;> first | exact h | exact h.elim

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- The matrix obtained by stripping quantifiers from a prenex formula
    is quantifier-free. -/
theorem prenexMatrix_isQF {L : Language} (A : FormulaN L)
    (h : isPrenex A) : FirstOrder.SemanticsN.isQuantifierFree (prenexMatrix A) := by
-- BEGIN PROOF
  induction A with
  | all _ A ih => exact ih h
  | ex _ A ih => exact ih h
  | _ => exact h

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Applying toPrenexHelper to a quantifier prefix and a quantifier-free
    body produces a prenex formula. -/
theorem toPrenexHelper_isPrenex {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body : FormulaN L)
    (hqf : FirstOrder.SemanticsN.isQuantifierFree body) :
    isPrenex (toPrenexHelper prefix_ body) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper]; exact qf_isPrenex body hqf
  | cons p rest ih =>
    match p with
    | (QuantifierKind.universal, x) =>
      simp [toPrenexHelper, isPrenex]; exact ih
    | (QuantifierKind.existential, x) =>
      simp [toPrenexHelper, isPrenex]; exact ih

-- Lemma 7.2.1(a) first sentence: Universal/existential implication left

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): Prenex equivalences -- quantifier extraction rules for pulling quantifiers through connectives. forall x(A impl B) equiv (exists x A impl B), where x does not occur free in B. The universal quantifier on the antecedent of an implication can be pulled out as an existential when x is not free in B. -/
theorem prenex_equiv_a_univ_impl_left {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.all x (FormulaN.impl A B))
      (FormulaN.impl (FormulaN.ex x A) B) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h ⟨a, hA⟩
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mp (h a hA)
  · intro h a hA
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr (h ⟨a, hA⟩)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): exists x(A impl B) equiv (forall x A impl B), where x does not occur free in B. The existential quantifier on the antecedent of an implication can be pulled out as a universal when x is not free in B. -/
theorem prenex_equiv_a_ex_impl_left {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.ex x (FormulaN.impl A B))
      (FormulaN.impl (FormulaN.all x A) B) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨a, h⟩ hAll
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mp (h (hAll a))
  · intro h
    by_cases hall : ∀ a : M.carrier, formulaEvalN M A (assignUpdate s x a)
    · have hb := h hall
      obtain ⟨w⟩ := M.carrierNonempty
      exact ⟨w, fun _ =>
        (formulaEval_assignUpdate_irrelevant s x _ B hfree).mpr hb⟩
    · obtain ⟨a, hna⟩ := Classical.not_forall.mp hall
      exact ⟨a, fun ha => absurd ha hna⟩

-- Lemma 7.2.1(a) second sentence: Universal/existential implication right

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): forall x(A impl B) equiv (A impl forall x B), where x does not occur free in A. The universal quantifier on the consequent of an implication can be pulled out when x is not free in A. -/
theorem prenex_equiv_b_univ_impl_right {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN
      (FormulaN.all x (FormulaN.impl A B))
      (FormulaN.impl A (FormulaN.all x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h hA a
    have := h a
    exact this ((formulaEval_assignUpdate_irrelevant s x a A hfree).mpr hA)
  · intro h a hA
    have hA' := (formulaEval_assignUpdate_irrelevant s x a A hfree).mp hA
    exact h hA' a

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): exists x(A impl B) equiv (A impl exists x B), where x does not occur free in A. The existential quantifier on the consequent of an implication can be pulled out when x is not free in A. -/
theorem prenex_equiv_b_ex_impl_right {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN
      (FormulaN.ex x (FormulaN.impl A B))
      (FormulaN.impl A (FormulaN.ex x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨a, h⟩ hA
    exact ⟨a, h ((formulaEval_assignUpdate_irrelevant s x a A hfree).mpr hA)⟩
  · intro h
    by_cases hA : formulaEvalN M A s
    · obtain ⟨a, hb⟩ := h hA
      exact ⟨a, fun _ => hb⟩
    · obtain ⟨w⟩ := M.carrierNonempty
      exact ⟨w, fun ha =>
        absurd ((formulaEval_assignUpdate_irrelevant s x w A hfree).mp ha) hA⟩

-- Lemma 7.2.1(b): Negation pull

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (b) (companion): not forall x A equiv exists x not A. The negation of a universal quantifier is equivalent to an existential quantifier with negated body. No side conditions. -/
theorem prenex_equiv_c_neg_all {L : Language}
    (x : Nat) (A : FormulaN L) :
    foLogEquivN
      (FormulaN.neg (FormulaN.all x A))
      (FormulaN.ex x (FormulaN.neg A)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨Classical.not_forall.mp, Classical.not_forall.mpr⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (b) (companion): not exists x A equiv forall x not A. The negation of an existential quantifier is equivalent to a universal quantifier with negated body. No side conditions. -/
theorem prenex_equiv_c_neg_ex {L : Language}
    (x : Nat) (A : FormulaN L) :
    foLogEquivN
      (FormulaN.neg (FormulaN.ex x A))
      (FormulaN.all x (FormulaN.neg A)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨not_exists.mp, not_exists.mpr⟩

-- Lemma 7.2.1(c): Free-variable pull from disjunction/conjunction

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (forall x A or B) equiv forall x(A or B), where x does not occur free in B. A universal quantifier can be pulled out of a disjunction when the variable is not free in the other disjunct. -/
theorem prenex_equiv_d_univ_disj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.disj (FormulaN.all x A) B)
      (FormulaN.all x (FormulaN.disj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h a
    match h with
    | Or.inl hAll => exact Or.inl (hAll a)
    | Or.inr hB => exact Or.inr ((formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB)
  · intro h
    by_cases hB : formulaEvalN M B s
    · exact Or.inr hB
    · exact Or.inl (fun a => (h a).elim id (fun hb =>
        absurd ((formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb) hB))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (forall x A and B) equiv forall x(A and B), where x does not occur free in B. A universal quantifier can be pulled out of a conjunction when the variable is not free in the other conjunct. -/
theorem prenex_equiv_d_univ_conj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.conj (FormulaN.all x A) B)
      (FormulaN.all x (FormulaN.conj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨hAll, hB⟩ a
    exact ⟨hAll a, (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB⟩
  · intro h
    exact ⟨fun a => (h a).1,
           (formulaEval_assignUpdate_irrelevant s x (Classical.choice M.carrierNonempty)
              B hfree).mp (h (Classical.choice M.carrierNonempty)).2⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (exists x A or B) equiv exists x(A or B), where x does not occur free in B. An existential quantifier can be pulled out of a disjunction when the variable is not free in the other disjunct. -/
theorem prenex_equiv_d_ex_disj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.disj (FormulaN.ex x A) B)
      (FormulaN.ex x (FormulaN.disj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h
    match h with
    | Or.inl ⟨a, ha⟩ => exact ⟨a, Or.inl ha⟩
    | Or.inr hB => exact ⟨Classical.choice M.carrierNonempty,
        Or.inr ((formulaEval_assignUpdate_irrelevant s x _ B hfree).mpr hB)⟩
  · intro ⟨a, h⟩
    match h with
    | Or.inl ha => exact Or.inl ⟨a, ha⟩
    | Or.inr hb => exact Or.inr ((formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (exists x A and B) equiv exists x(A and B), where x does not occur free in B. An existential quantifier can be pulled out of a conjunction when the variable is not free in the other conjunct. -/
theorem prenex_equiv_d_ex_conj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.conj (FormulaN.ex x A) B)
      (FormulaN.ex x (FormulaN.conj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨⟨a, ha⟩, hB⟩
    exact ⟨a, ha, (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB⟩
  · intro ⟨a, ha, hb⟩
    exact ⟨⟨a, ha⟩, (formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb⟩

-- Lemma 7.2.1(d): Distributive





-- Lemma 7.2.1(e): alpha-renaming

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (e) (companion): forall x A equiv forall y A[y/x], where y is free for x in A and y does not occur free in A unless y = x. Allows renaming the bound variable of a universal quantifier. -/
theorem prenex_equiv_f_univ_rename {L : Language}
    (x y : Nat) (A : FormulaN L)
    (hfreeFor : isFreeForN (Term.var y) x A)
    (hnotFree : ¬ Membership.mem (formulaFVN A) y ∨ y = x) :
    foLogEquivN
      (FormulaN.all x A)
      (FormulaN.all y (formulaSubstN A (Term.var y) x)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  have key : ∀ (a : M.carrier),
      formulaEvalN M A (assignUpdate s x a) ↔
      formulaEvalN M (formulaSubstN A (Term.var y) x) (assignUpdate s y a) := by
    intro a
    rw [formulaSubstEvalDirectN (assignUpdate s y a) A (Term.var y) x hfreeFor]
    simp only [termEval, assignUpdate, ite_true]
    exact coincidenceLemmaN M A _ _ (fun z hz => by
      unfold assignUpdate
      by_cases hzx : z = x
      · simp [hzx]
      · simp [hzx]
        by_cases hzy : z = y
        · subst hzy; exact absurd hz (hnotFree.elim id (fun heq => absurd heq hzx))
        · simp [hzy])
  exact ⟨fun h a => (key a).mp (h a), fun h a => (key a).mpr (h a)⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (e) (companion): exists x A equiv exists y A[y/x], where y is free for x in A and y does not occur free in A unless y = x. Allows renaming the bound variable of an existential quantifier. -/
theorem prenex_equiv_f_ex_rename {L : Language}
    (x y : Nat) (A : FormulaN L)
    (hfreeFor : isFreeForN (Term.var y) x A)
    (hnotFree : ¬ Membership.mem (formulaFVN A) y ∨ y = x) :
    foLogEquivN
      (FormulaN.ex x A)
      (FormulaN.ex y (formulaSubstN A (Term.var y) x)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  have key : ∀ (a : M.carrier),
      formulaEvalN M A (assignUpdate s x a) ↔
      formulaEvalN M (formulaSubstN A (Term.var y) x) (assignUpdate s y a) := by
    intro a
    rw [formulaSubstEvalDirectN (assignUpdate s y a) A (Term.var y) x hfreeFor]
    simp only [termEval, assignUpdate, ite_true]
    exact coincidenceLemmaN M A _ _ (fun z hz => by
      unfold assignUpdate
      by_cases hzx : z = x
      · simp [hzx]
      · simp [hzx]
        by_cases hzy : z = y
        · subst hzy; exact absurd hz (hnotFree.elim id (fun heq => absurd heq hzx))
        · simp [hzy])
  exact ⟨fun ⟨a, ha⟩ => ⟨a, (key a).mp ha⟩, fun ⟨a, ha⟩ => ⟨a, (key a).mpr ha⟩⟩

-- ===================================================================
-- Lemma 7.2.1 (unified bundle): All prenex equivalences
-- ===================================================================

/-- Lemma 7.2.1: The following formulae are valid. (a) forall x(A impl B) equiv (exists x A impl B) and exists x(A impl B) equiv (forall x A impl B), where x does not occur free in B. forall x(A impl B) equiv (A impl forall x B) and exists x(A impl B) equiv (A impl exists x B), where x does not occur free in A. (b) not forall x A equiv exists x not A and not exists x A equiv forall x not A. (c) (forall x A or B) equiv forall x(A or B), (forall x A and B) equiv forall x(A and B), (exists x A or B) equiv exists x(A or B), and (exists x A and B) equiv exists x(A and B), where x does not occur free in B. (d) forall x(A and B) equiv forall x A and forall x B, and exists x(A or B) equiv exists x A or exists x B. (e) forall x A equiv forall y A[y/x] and exists x A equiv exists y A[y/x], where y is free for x in A, and y does not occur free in A unless y = x (i.e., y is not in FV(A) - {x}). The bundle simply assembles the 14 individual equivalences already proved as `prenex_equiv_*` helpers in this file. -/
@[blueprint "chap7__lemma_7_2_1" (main := true)]
theorem lemma_7_2_1 {L : Language} :
    -- (a) implication, first sentence: x ∉ FV(B)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.all x (FormulaN.impl A B))
          (FormulaN.impl (FormulaN.ex x A) B)) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.ex x (FormulaN.impl A B))
          (FormulaN.impl (FormulaN.all x A) B)) ∧
    -- (a) implication, second sentence: x ∉ FV(A)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN A) x →
        foLogEquivN
          (FormulaN.all x (FormulaN.impl A B))
          (FormulaN.impl A (FormulaN.all x B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN A) x →
        foLogEquivN
          (FormulaN.ex x (FormulaN.impl A B))
          (FormulaN.impl A (FormulaN.ex x B))) ∧
    -- (b) negation pull
    (∀ (x : Nat) (A : FormulaN L),
        foLogEquivN
          (FormulaN.neg (FormulaN.all x A))
          (FormulaN.ex x (FormulaN.neg A))) ∧
    (∀ (x : Nat) (A : FormulaN L),
        foLogEquivN
          (FormulaN.neg (FormulaN.ex x A))
          (FormulaN.all x (FormulaN.neg A))) ∧
    -- (c) free-variable pull from disj/conj, x ∉ FV(B)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.disj (FormulaN.all x A) B)
          (FormulaN.all x (FormulaN.disj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.conj (FormulaN.all x A) B)
          (FormulaN.all x (FormulaN.conj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.disj (FormulaN.ex x A) B)
          (FormulaN.ex x (FormulaN.disj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.conj (FormulaN.ex x A) B)
          (FormulaN.ex x (FormulaN.conj A B))) ∧
    -- (d) distributive
    (∀ (x : Nat) (A B : FormulaN L),
        foLogEquivN
          (FormulaN.all x (FormulaN.conj A B))
          (FormulaN.conj (FormulaN.all x A) (FormulaN.all x B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        foLogEquivN
          (FormulaN.ex x (FormulaN.disj A B))
          (FormulaN.disj (FormulaN.ex x A) (FormulaN.ex x B))) ∧
    -- (e) alpha-renaming: y free for x in A, y ∉ FV(A) - {x}
    (∀ (x y : Nat) (A : FormulaN L),
        isFreeForN (Term.var y) x A →
        (¬ Membership.mem (formulaFVN A) y ∨ y = x) →
        foLogEquivN
          (FormulaN.all x A)
          (FormulaN.all y (formulaSubstN A (Term.var y) x))) ∧
    (∀ (x y : Nat) (A : FormulaN L),
        isFreeForN (Term.var y) x A →
        (¬ Membership.mem (formulaFVN A) y ∨ y = x) →
        foLogEquivN
          (FormulaN.ex x A)
          (FormulaN.ex y (formulaSubstN A (Term.var y) x))) 

-- ===================================================================
-- Example 7.2.1: The five displayed intermediate equivalences
-- ===================================================================

/-- Example 7.2.1 (companion): ¬∃y(Q(y)∧R(x,y)) is equivalent to the
stored ∀y¬(Q(y)∧R(x,y)); x=0 remains free and y=1 remains bound. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep1_equiv_7_2_1 :
    foLogEquivN
      (.neg (.ex 1 (.conj
        (.predN ExPred_7_2_1.Q (fun _ => .var 1))
        (.predN ExPred_7_2_1.R (vec2 (.var 0) (.var 1))))))
      exPrenexStep1_7_2_1 

/-- Example 7.2.1 (companion): The complete displayed left subformula
∀x(P(x)∨¬∃y(Q(y)∧R(x,y))) is equivalent to stored step 2, with prefix ∀x∀y. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep2_equiv_7_2_1 :
    foLogEquivN
      (.all 0 (.disj (.predN ExPred_7_2_1.P (fun _ => .var 0))
        (.neg (.ex 1 (.conj
          (.predN ExPred_7_2_1.Q (fun _ => .var 1))
          (.predN ExPred_7_2_1.R (vec2 (.var 0) (.var 1))))))))
      exPrenexStep2_7_2_1 

/-- Example 7.2.1 (companion): ¬∀xP(x) is equivalent to the stored ∃x¬P(x),
retaining the printed binder x=0. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep3_equiv_7_2_1 :
    foLogEquivN
      (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0))))
      exPrenexStep3_7_2_1 

/-- Example 7.2.1 (companion): P(y)∧¬∀xP(x) is equivalent to the stored
∃x(P(y)∧¬P(x)); y=1 stays free outside the x=0 binder. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep4_equiv_7_2_1 :
    foLogEquivN
      (.conj (.predN ExPred_7_2_1.P (fun _ => .var 1))
        (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0)))))
      exPrenexStep4_7_2_1 

/-- Example 7.2.1 (companion): ¬(P(y)∧¬∀xP(x)) is equivalent to the stored
∀x¬(P(y)∧¬P(x)), retaining its free y and printed x scope. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep5_equiv_7_2_1 :
    foLogEquivN
      (.neg (.conj (.predN ExPred_7_2_1.P (fun _ => .var 1))
        (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0))))))
      exPrenexStep5_7_2_1 



-- ===================================================================
-- Theorem 7.2.1 (infrastructure): Variable bound utilities
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Upper bound on all variable indices occurring in a term. -/
def Term.varBound {L : Language} : Term L → Nat
  | .var i => i + 1
  | .const _ => 0
  | .func f ts => finMax (L.funArity f) (fun j => Term.varBound (ts j))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Upper bound on all variable indices (free, bound, and in terms)
    occurring in a formula. Any variable v with v ≥ varBound A does
    not appear anywhere in A. -/
def formulaVarBound {L : Language} : FormulaN L → Nat
  | .predN _ ts => finMax _ (fun j => Term.varBound (ts j))
  | .eq_ hL t1 t2 => max (Term.varBound t1) (Term.varBound t2)
  | .neg A => formulaVarBound A
  | .conj A B => max (formulaVarBound A) (formulaVarBound B)
  | .disj A B => max (formulaVarBound A) (formulaVarBound B)
  | .impl A B => max (formulaVarBound A) (formulaVarBound B)
  | .all x A => max (x + 1) (formulaVarBound A)
  | .ex x A => max (x + 1) (formulaVarBound A)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
theorem termFV_bounded {L : Language} (t : Term L) (v : Nat)
    (hv : v ≥ Term.varBound t) : ¬ Membership.mem (termFV t) v := by
-- BEGIN PROOF
  induction t with
  | var i =>
    simp [Term.varBound] at hv; intro h; subst h; omega
  | const _ => intro h; exact h
  | func f ts ih =>
    intro h; simp [termFV] at h; obtain ⟨j, hj⟩ := h
    exact ih j (Nat.le_trans (finMax_ge _ (fun j => Term.varBound (ts j)) j)
      (by simp [Term.varBound] at hv; exact hv)) hj

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variables above the varBound of a formula are not free in that formula. -/
theorem formulaFV_bounded {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v ≥ formulaVarBound A) : ¬ Membership.mem (formulaFVN A) v := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro h; simp [formulaFVN] at h; obtain ⟨j, hj⟩ := h
    exact termFV_bounded (ts j) v
      (Nat.le_trans (finMax_ge _ (fun j => Term.varBound (ts j)) j)
        (by simp [formulaVarBound] at hv; exact hv)) hj
  | eq_ hL t1 t2 =>
    intro h; cases h with
    | inl h1 => exact termFV_bounded t1 v (by simp [formulaVarBound] at hv; omega) h1
    | inr h2 => exact termFV_bounded t2 v (by simp [formulaVarBound] at hv; omega) h2
  | neg A ih =>
    simp [formulaVarBound] at hv; exact ih hv
  | conj A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | disj A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | impl A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | all x A ih =>
    intro h; exact ih (by simp [formulaVarBound] at hv; omega) h.1
  | ex x A ih =>
    intro h; exact ih (by simp [formulaVarBound] at hv; omega) h.1

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- A variable above the varBound of a formula is free-for substitution. -/
theorem isFreeFor_fresh {L : Language} (A : FormulaN L) (x y : Nat)
    (hy : y ≥ formulaVarBound A) : isFreeForN (Term.var y) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => simp [isFreeForN]
  | neg A ih =>
    simp [isFreeForN]; exact ih (by simp [formulaVarBound] at hy; exact hy)
  | conj A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | disj A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | impl A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | all z A ih =>
    simp [isFreeForN]; right
    exact ⟨by intro heq; subst heq; simp [formulaVarBound] at hy; omega,
           ih (by simp [formulaVarBound] at hy; omega)⟩
  | ex z A ih =>
    simp [isFreeForN]; right
    exact ⟨by intro heq; subst heq; simp [formulaVarBound] at hy; omega,
           ih (by simp [formulaVarBound] at hy; omega)⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the quantifier-free property. -/
theorem subst_preserves_qf {L : Language} (A : FormulaN L) (y x : Nat)
    (hqf : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree (formulaSubstN A (Term.var y) x) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree]
  | neg A ih =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ih hqf
  | conj A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | disj A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | impl A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | all _ _ => exact absurd hqf id
  | ex _ _ => exact absurd hqf id

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the prenex property. -/
theorem subst_preserves_prenex {L : Language} (A : FormulaN L) (y x : Nat)
    (hp : isPrenex A) :
    isPrenex (formulaSubstN A (Term.var y) x) := by
-- BEGIN PROOF
  induction A with
  | all z B ih =>
    simp [formulaSubstN]; split
    · exact hp
    · simp [isPrenex]; exact ih hp
  | ex z B ih =>
    simp [formulaSubstN]; split
    · exact hp
    · simp [isPrenex]; exact ih hp
  | _ => exact subst_preserves_qf _ y x hp

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- The number of leading quantifiers in a formula. -/
def numLeadingQ {L : Language} : FormulaN L → Nat
  | .all _ A => 1 + numLeadingQ A
  | .ex _ A => 1 + numLeadingQ A
  | _ => 0

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- A formula with positive numLeadingQ is either all or ex. -/
theorem numLeadingQ_pos {L : Language} (Q : FormulaN L)
    (h : numLeadingQ Q > 0) :
    (∃ x body, Q = .all x body) ∨ (∃ x body, Q = .ex x body) := by
-- BEGIN PROOF
  cases Q <;> simp [numLeadingQ] at h
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the number of leading quantifiers. -/
theorem subst_preserves_numLeadingQ {L : Language}
    (A : FormulaN L) (y x : Nat) :
    numLeadingQ (formulaSubstN A (Term.var y) x) =
    numLeadingQ A := by
-- BEGIN PROOF
  induction A with
  | all z B ih =>
    simp [formulaSubstN]; split
    · rfl
    · simp [numLeadingQ]; exact ih
  | ex z B ih =>
    simp [formulaSubstN]; split
    · rfl
    · simp [numLeadingQ]; exact ih
  | _ => simp [formulaSubstN, numLeadingQ]

-- ===================================================================
-- Theorem 7.2.1 (infrastructure): Prenex combining helpers
-- ===================================================================

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Negation of a prenex formula has a prenex equivalent. -/
theorem negPrenex_equiv {L : Language} (B : FormulaN L)
    (hp : isPrenex B) :
    ∃ C : FormulaN L, isPrenex C ∧ foLogEquivN (FormulaN.neg B) C := by
-- BEGIN PROOF
  induction B with
  | all x A ih =>
    obtain ⟨C, hpC, heC⟩ := ih hp
    exact ⟨FormulaN.ex x C, hpC,
      foLogEquivN_trans (prenex_equiv_c_neg_all x A) (foLogEquivN_ex x heC)⟩
  | ex x A ih =>
    obtain ⟨C, hpC, heC⟩ := ih hp
    exact ⟨FormulaN.all x C, hpC,
      foLogEquivN_trans (prenex_equiv_c_neg_ex x A) (foLogEquivN_all x heC)⟩
  | neg A _ =>
    exact ⟨.neg (.neg A),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | conj A1 A2 _ _ =>
    exact ⟨.neg (.conj A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | disj A1 A2 _ _ =>
    exact ⟨.neg (.disj A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | impl A1 A2 _ _ =>
    exact ⟨.neg (.impl A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | predN P ts => exact ⟨.neg (.predN P ts), trivial, foLogEquivN_refl _⟩
  | eq_ hL t1 t2 => exact ⟨.neg (.eq_ hL t1 t2), trivial, foLogEquivN_refl _⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull a universal quantifier out of the right side of conjunction. -/
theorem prenex_conj_right_all {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.conj A (FormulaN.all x B))
      (FormulaN.all x (FormulaN.conj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_conj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_univ_conj x B A hfree)
      (foLogEquivN_all x (foLogEquivN_conj_comm B A)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull an existential quantifier out of the right side of conjunction. -/
theorem prenex_conj_right_ex {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.conj A (FormulaN.ex x B))
      (FormulaN.ex x (FormulaN.conj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_conj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_ex_conj x B A hfree)
      (foLogEquivN_ex x (foLogEquivN_conj_comm B A)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull a universal quantifier out of the right side of disjunction. -/
theorem prenex_disj_right_all {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.disj A (FormulaN.all x B))
      (FormulaN.all x (FormulaN.disj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_disj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_univ_disj x B A hfree)
      (foLogEquivN_all x (foLogEquivN_disj_comm B A)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull an existential quantifier out of the right side of disjunction. -/
theorem prenex_disj_right_ex {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.disj A (FormulaN.ex x B))
      (FormulaN.ex x (FormulaN.disj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_disj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_ex_disj x B A hfree)
      (foLogEquivN_ex x (foLogEquivN_disj_comm B A)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Conjunction of two prenex formulas has a prenex equivalent.
    By well-founded induction on the total number of leading quantifiers. -/
theorem conjPrenex {L : Language} (P1 P2 : FormulaN L)
    (hp1 : isPrenex P1) (hp2 : isPrenex P2) :
    ∃ C : FormulaN L, isPrenex C ∧
      foLogEquivN (FormulaN.conj P1 P2) C := by
-- BEGIN PROOF
  -- Induction on total number of leading quantifiers
  suffices h : ∀ n, ∀ Q1 Q2 : FormulaN L,
      isPrenex Q1 → isPrenex Q2 →
      numLeadingQ Q1 + numLeadingQ Q2 ≤ n →
      ∃ C, isPrenex C ∧ foLogEquivN (.conj Q1 Q2) C from
    h _ P1 P2 hp1 hp2 (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro Q1 Q2 hq1 hq2 hn
    -- Both have 0 leading quantifiers. conj of two prenex-without-quantifiers is prenex.
    have hqf1 : FirstOrder.SemanticsN.isQuantifierFree Q1 := by
      cases Q1 <;> simp [numLeadingQ] at hn <;> exact hq1
    have hqf2 : FirstOrder.SemanticsN.isQuantifierFree Q2 := by
      cases Q2 <;> simp [numLeadingQ] at hn <;> exact hq2
    exact ⟨.conj Q1 Q2, ⟨hqf1, hqf2⟩, foLogEquivN_refl _⟩
  | succ k ih =>
    intro Q1 Q2 hq1 hq2 hn
    -- Case split: if Q1 has leading quantifiers, pull from left.
    -- Otherwise, pull from Q2.
    by_cases h1 : numLeadingQ Q1 > 0
    · -- Q1 has at least one leading quantifier
      rcases numLeadingQ_pos Q1 h1 with ⟨x, body1, rfl⟩ | ⟨x, body1, rfl⟩
      · -- Q1 = all x body1
        let y := max (formulaVarBound (.all x body1)) (formulaVarBound Q2)
        have hfreeFor := isFreeFor_fresh body1 x y
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        have hnotFree : ¬ Membership.mem (formulaFVN body1) y ∨ y = x :=
          Or.inl (formulaFV_bounded body1 y
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        have hRename := prenex_equiv_f_univ_rename x y body1 hfreeFor hnotFree
        have hyFresh := formulaFV_bounded Q2 y (Nat.le_max_right _ _)
        have hPull := prenex_equiv_d_univ_conj y
          (formulaSubstN body1 (Term.var y) x) Q2 hyFresh
        have hpSub := subst_preserves_prenex body1 y x hq1
        have hBound : numLeadingQ (formulaSubstN body1 (Term.var y) x) +
            numLeadingQ Q2 ≤ k := by
          rw [subst_preserves_numLeadingQ]
          simp [numLeadingQ] at hn; omega
        obtain ⟨C, hpC, heC⟩ := ih _ _ hpSub hq2 hBound
        exact ⟨.all y C, hpC,
          foLogEquivN_trans
            (foLogEquivN_conj hRename (foLogEquivN_refl Q2))
            (foLogEquivN_trans hPull (foLogEquivN_all y heC))⟩
      · -- Q1 = ex x body1
        let y := max (formulaVarBound (.ex x body1)) (formulaVarBound Q2)
        have hfreeFor := isFreeFor_fresh body1 x y
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        have hnotFree : ¬ Membership.mem (formulaFVN body1) y ∨ y = x :=
          Or.inl (formulaFV_bounded body1 y
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        have hRename := prenex_equiv_f_ex_rename x y body1 hfreeFor hnotFree
        have hyFresh := formulaFV_bounded Q2 y (Nat.le_max_right _ _)
        have hPull := prenex_equiv_d_ex_conj y
          (formulaSubstN body1 (Term.var y) x) Q2 hyFresh
        have hpSub := subst_preserves_prenex body1 y x hq1
        have hBound : numLeadingQ (formulaSubstN body1 (Term.var y) x) +
            numLeadingQ Q2 ≤ k := by
          rw [subst_preserves_numLeadingQ]
          simp [numLeadingQ] at hn; omega
        obtain ⟨C, hpC, heC⟩ := ih _ _ hpSub hq2 hBound
        exact ⟨.ex y C, hpC,
          foLogEquivN_trans
            (foLogEquivN_conj hRename (foLogEquivN_refl Q2))
            (foLogEquivN_trans hPull (foLogEquivN_ex y heC))⟩
    · -- Q1 has no leading quantifiers (numLeadingQ Q1 = 0)
      by_cases h2 : numLeadingQ Q2 > 0
      · -- Q2 has at least one leading quantifier. Pull from right.
        rcases numLeadingQ_pos Q2 h2 with ⟨y, body2, rfl⟩ | ⟨y, body2, rfl⟩
        · -- Q2 = all y body2
          let z := max (formulaVarBound Q1) (formulaVarBound (.all y body2))
          have hfreeFor := isFreeFor_fresh body2 y z
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          have hnotFree : ¬ Membership.mem (formulaFVN body2) z ∨ z = y :=
            Or.inl (formulaFV_bounded body2 z
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          have hRename := prenex_equiv_f_univ_rename y z body2 hfreeFor hnotFree
          have hzFresh := formulaFV_bounded Q1 z (Nat.le_max_left _ _)
          have hPull := prenex_conj_right_all z Q1
            (formulaSubstN body2 (Term.var z) y) hzFresh
          have hpSub := subst_preserves_prenex body2 z y hq2
          have hBound : numLeadingQ Q1 +
              numLeadingQ (formulaSubstN body2 (Term.var z) y) ≤ k := by
            rw [subst_preserves_numLeadingQ]
            simp [numLeadingQ] at hn; omega
          obtain ⟨C, hpC, heC⟩ := ih Q1 _ hq1 hpSub hBound
          exact ⟨.all z C, hpC,
            foLogEquivN_trans
              (foLogEquivN_conj (foLogEquivN_refl Q1) hRename)
              (foLogEquivN_trans hPull (foLogEquivN_all z heC))⟩
        · -- Q2 = ex y body2
          let z := max (formulaVarBound Q1) (formulaVarBound (.ex y body2))
          have hfreeFor := isFreeFor_fresh body2 y z
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          have hnotFree : ¬ Membership.mem (formulaFVN body2) z ∨ z = y :=
            Or.inl (formulaFV_bounded body2 z
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          have hRename := prenex_equiv_f_ex_rename y z body2 hfreeFor hnotFree
          have hzFresh := formulaFV_bounded Q1 z (Nat.le_max_left _ _)
          have hPull := prenex_conj_right_ex z Q1
            (formulaSubstN body2 (Term.var z) y) hzFresh
          have hpSub := subst_preserves_prenex body2 z y hq2
          have hBound : numLeadingQ Q1 +
              numLeadingQ (formulaSubstN body2 (Term.var z) y) ≤ k := by
            rw [subst_preserves_numLeadingQ]
            simp [numLeadingQ] at hn; omega
          obtain ⟨C, hpC, heC⟩ := ih Q1 _ hq1 hpSub hBound
          exact ⟨.ex z C, hpC,
            foLogEquivN_trans
              (foLogEquivN_conj (foLogEquivN_refl Q1) hRename)
              (foLogEquivN_trans hPull (foLogEquivN_ex z heC))⟩
      · -- Both Q1 and Q2 have 0 leading quantifiers: both qf
        exact ih Q1 Q2 hq1 hq2 (by omega)

end LCS.Herbrand.PrenexForm
end

