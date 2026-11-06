import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.MaxQuantSubformulae
import LCS.Herbrand.NNFHauptsatz.RuleCore
import Attach
import LCS.Herbrand.NNFHauptsatz.QuantifierPolarity.ProofsStamp

/-! # Herbrand.NNFHauptsatz.QuantifierPolarity

Example 7.4.1: the rule applicable to a quantified subformula depends on the parity
of the negative subformulae containing it; in NNF this problem does not arise.
-/

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

-- ===================================================================
-- Example 7.4.1 (companion type): QPolExPred
-- ===================================================================

/-- Example 7.4.1 (companion type): Predicate symbols for the
quantifier polarity example: P (unary) and Q (unary). -/
@[blueprint "chap7__example_7_4_1"]
inductive QPolExPred : Type where
  | P : QPolExPred
  | Q : QPolExPred

-- ===================================================================
-- Example 7.4.1 (companion type): QPolExConst
-- ===================================================================

/-- Example 7.4.1 (companion type): Constant symbols for the
quantifier polarity example: a and b. -/
@[blueprint "chap7__example_7_4_1"]
inductive QPolExConst : Type where
  | a : QPolExConst
  | b : QPolExConst

-- ===================================================================
-- Example 7.4.1 (companion def): qPolExLang
-- ===================================================================

/-- Example 7.4.1 (companion def): A language with unary predicates
P and Q, constants a and b, no function symbols, and no equality. -/
@[blueprint "chap7__example_7_4_1"]
def qPolExLang : Language where
  hasEquality := false
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := QPolExConst
  predSymbols := QPolExPred
  predArity := fun
    | .P => 1
    | .Q => 1

-- ===================================================================
-- Example 7.4.1: quantifierPolarityExFormula
-- ===================================================================

/-- Example 7.4.1: The formula A = P(a) or not(Q(b) and forall x Q(x)). Demonstrates the quantifier rule polarity problem: the subformula forall x Q(x) is under a negation, so the correct rule to apply is exists-left, not forall-left. Variables: x = 0. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExFormula : FormulaN qPolExLang :=
  FormulaN.disj
    (FormulaN.predN QPolExPred.P
      (fun _ => Term.const QPolExConst.a))
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN QPolExPred.Q
          (fun _ => Term.const QPolExConst.b))
        (FormulaN.all 0
          (FormulaN.predN QPolExPred.Q
            (fun _ => Term.var 0)))))

-- ===================================================================
-- Example 7.4.1 (companion def): quantifierPolarityExNNF
-- ===================================================================

/-- Example 7.4.1 (companion def): The logically equivalent NNF form P(a) or (not Q(b) or exists x not Q(x)). In NNF, only atoms are negated, so the quantifier directly indicates the applicable rule without ambiguity from negation parity. Variables: x = 0. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExNNF : FormulaN qPolExLang :=
  FormulaN.disj
    (FormulaN.predN QPolExPred.P
      (fun _ => Term.const QPolExConst.a))
    (FormulaN.disj
      (FormulaN.neg
        (FormulaN.predN QPolExPred.Q
          (fun _ => Term.const QPolExConst.b)))
      (FormulaN.ex 0
        (FormulaN.neg
          (FormulaN.predN QPolExPred.Q
            (fun _ => Term.var 0)))))

-- ATTACH-BLOCKER: global set_option

section QuantifierPolarity
set_option backward.isDefEq.respectTransparency false

/-- Quantifier heads, independent of sequent side. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolarityQuantifierHead where
  | universal | existential
  deriving DecidableEq

@[blueprint "chap7__example_7_4_1"]
def PolarityQuantifierHead.dual : PolarityQuantifierHead → PolarityQuantifierHead
  | .universal => .existential
  | .existential => .universal

@[blueprint "chap7__example_7_4_1"]
def PolarityQuantifierHead.formula {L : Language} :
    PolarityQuantifierHead → Nat → FormulaN L → FormulaN L
  | .universal => FormulaN.all
  | .existential => FormulaN.ex

/-- The side of the whole antecedent/succedent formula; normalization does
not move that formula to the other side. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolaritySequentSide where
  | antecedent | succedent
  deriving DecidableEq

/-- The four quantifier inference kinds of Definition 7.4.3. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolarityRuleKind where
  | allLeft | allRight | exLeft | exRight
  deriving DecidableEq

@[blueprint "chap7__example_7_4_1"]
def polarityRuleKind (side : PolaritySequentSide) (head : PolarityQuantifierHead)
    (negative : Bool) : PolarityRuleKind :=
  match side, (if negative then head.dual else head) with
  | .antecedent, .universal => .allLeft
  | .succedent, .universal => .allRight
  | .antecedent, .existential => .exLeft
  | .succedent, .existential => .exRight

/-- A selected quantified occurrence through a propositional context.
The Boolean index is odd negative-context parity: negation and the antecedent
of an implication flip it. Implication is read as its usual negation/disjunction
abbreviation. Paths stop at quantifiers, as required for G2 maximal occurrences.
Distinct branch constructors retain distinct occurrences of equal formulae. -/
@[blueprint "chap7__example_7_4_1"]
inductive QuantifierContextOccurrence {L : Language} :
    FormulaN L → PolarityQuantifierHead → Nat → FormulaN L → Bool → Type where
  | all (x : Nat) (B : FormulaN L) :
      QuantifierContextOccurrence (.all x B) .universal x B false
  | ex (x : Nat) (B : FormulaN L) :
      QuantifierContextOccurrence (.ex x B) .existential x B false
  | neg {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.neg A) k x B (!n)
  | conjLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.conj A C) k x B n
  | conjRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.conj C A) k x B n
  | disjLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.disj A C) k x B n
  | disjRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.disj C A) k x B n
  | implLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.impl A C) k x B (!n)
  | implRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.impl C A) k x B n

/-- The surviving binary branch address after negations are pushed inward.
Negation nodes disappear; implication retains its left/right branch positions. -/
@[blueprint "chap7__example_7_4_1"]
def QuantifierContextOccurrence.nnfAddress {L : Language} {A : FormulaN L}
    {k x B n} : QuantifierContextOccurrence A k x B n → MaxQuantifierOccurrenceAddress
  | .all .. | .ex .. => []
  | .neg o => o.nnfAddress
  | .conjLeft o _ | .disjLeft o _ | .implLeft o _ => .left :: o.nnfAddress
  | .conjRight _ o | .disjRight _ o | .implRight _ o => .right :: o.nnfAddress

-- ATTACH-BLOCKER: section options: helper requires front context
/-- Exact normalized occurrence and selected formula, for either incoming
polarity. The address constraint prevents selecting an unrelated equal subformula. -/
theorem QuantifierContextOccurrence.normalization {L : Language} {A : FormulaN L}
    {k x B n} (o : QuantifierContextOccurrence A k x B n) (positive : Bool) :
    ∃ q : MaxQuantifierOccurrence (FormulaN.toNNFAux positive A),
      q.address = o.nnfAddress ∧
      q.selected = (if positive != n then k else k.dual).formula x
        (FormulaN.toNNFAux (positive != n) B) := by
  induction o generalizing positive with
  | all x B =>
    cases positive
    · exact ⟨.ex x _, rfl, rfl⟩
    · exact ⟨.all x _, rfl, rfl⟩
  | ex x B =>
    cases positive
    · exact ⟨.all x _, rfl, rfl⟩
    · exact ⟨.ex x _, rfl, rfl⟩
  | @neg A k x B n o ih =>
    cases positive <;> cases n
    · exact ih true
    · exact ih true
    · exact ih false
    · exact ih false
  | conjLeft o C ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | conjRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
  | disjLeft o C ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | disjRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
  | @implLeft A k x B n o C ih =>
    cases positive <;> cases n
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | implRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩

/-- Read the rule kind directly from the normalized selected quantifier and
its sequent side. Non-quantifier heads have no quantifier rule kind. -/
@[blueprint "chap7__example_7_4_1"]
def normalizedQuantifierRuleKind {L : Language} (side : PolaritySequentSide) :
    FormulaN L → Option PolarityRuleKind
  | .all _ _ => some (match side with | .antecedent => .allLeft | .succedent => .allRight)
  | .ex _ _ => some (match side with | .antecedent => .exLeft | .succedent => .exRight)
  | _ => none

/-- Section 7.4.1 / Example 7.4.1: the exact selected occurrence normalizes
to the same surviving address. Its rule kind is determined by its quantifier
head, its formula's sequent side, and negative-context parity. Odd parity
dualizes the quantifier; even parity preserves it. This classifies the NNF
inference kind, not a legal application to the original non-NNF formula. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierOccurrence_ruleKind {L : Language} (_hL : L.withoutEquality)
    {A : FormulaN L} {k x B negative}
    (o : QuantifierContextOccurrence A k x B negative) (side : PolaritySequentSide) :
    ∃ q : MaxQuantifierOccurrence A.toNNF,
      q.address = o.nnfAddress ∧
      q.selected = (if negative then k.dual else k).formula x (FormulaN.toNNFAux (!negative) B) ∧
      normalizedQuantifierRuleKind side q.selected = some (polarityRuleKind side k negative) 

/-- The exact negative universal occurrence in the antecedent formula of
Example 7.4.1: disjunction-right, negation, conjunction-right. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExOccurrence :
    QuantifierContextOccurrence quantifierPolarityExFormula .universal 0
      (FormulaN.predN QPolExPred.Q (fun _ => Term.var 0)) true :=
  .disjRight _ (.neg (.conjRight _ (.all 0 _)))

/-- Example 7.4.1: normalization of the antecedent formula itself gives the
printed NNF formula, whose selected quantifier requires exists-left. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierPolarityEx_ruleKind :
    quantifierPolarityExFormula.toNNF = quantifierPolarityExNNF ∧
    ∃ q : MaxQuantifierOccurrence quantifierPolarityExNNF,
      q.address = [.right, .right] ∧
      q.selected = FormulaN.ex 0 (FormulaN.neg
        (FormulaN.predN QPolExPred.Q (fun _ => Term.var 0))) ∧
      normalizedQuantifierRuleKind .antecedent q.selected = some .exLeft 

/-- Example 7.4.1: the printed NNF is equivalent to the antecedent formula,
without negating that whole antecedent or changing its sequent side. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierPolarityEx_equiv :
    LCS.FirstOrder.Semantics.Equivalence.foLogEquivN
      quantifierPolarityExFormula quantifierPolarityExNNF 
end QuantifierPolarity
end LCS.Herbrand.NNFHauptsatz
end
