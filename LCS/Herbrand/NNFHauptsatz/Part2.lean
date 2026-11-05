import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Part1
import Attach
import LCS.Herbrand.NNFHauptsatz.Part2.ProofsStamp

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

/-- General QF recursion for both ordinary and equality consumers. Conjunction
and disjunction descend through their children; a quantifier returns its whole
formula as a singleton. Atoms, negations and implications return the empty set.
The function is total, including on formulae outside NNF. -/
@[blueprint "chap7__definition_7_4_4"]
def maxQuantSubformulaeCore {L : Language} : FormulaN L → Set (FormulaN L)
  | .predN _ _       => ∅
  | .eq_ _ _ _       => ∅
  | .neg _           => ∅
  | .disj A B        => maxQuantSubformulaeCore A ∪ maxQuantSubformulaeCore B
  | .conj A B        => maxQuantSubformulaeCore A ∪ maxQuantSubformulaeCore B
  | .all x B         => sng (FormulaN.all x B)
  | .ex x B          => sng (FormulaN.ex x B)
  | .impl _ _        => ∅

/-- Definition 7.4.1: In an equality-free language, QF(A) for a formula A in
NNF is empty for literals, a union for conjunction/disjunction, and the singleton
of A for either quantifier. The totalized operation preserves these five clauses
on the source domain; it does not descend into quantified bodies. -/
@[blueprint "chap7__definition_7_4_1" (main := true)]
def maxQuantSubformulae {L : Language} (_hL : L.withoutEquality)
    (A : FormulaN L) : Set (FormulaN L) := maxQuantSubformulaeCore A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Section 7.4.1: Every formula over an equality-free language has an NNF
formula logically equivalent to it. Both conclusions of Lemma 6.4.1 are retained. -/
theorem nnf_equivalence {L : Language} (_hL : L.withoutEquality) (A : FormulaN L) :
    ∃ B : FormulaN L, B.isNNF ∧ LCS.FirstOrder.Semantics.Equivalence.foLogEquivN A B :=
  LCS.CutElim.Hauptsatz.nnf_equivalence A

end LCS.Herbrand.NNFHauptsatz
end

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
namespace MaxQuantifierOccurrence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The formula selected by an occurrence path belongs to the set-valued
`QF(A)` API. -/
theorem selected_mem {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    Membership.mem (maxQuantSubformulaeCore A) occurrence.selected := by
  induction occurrence with
  | all _ _ => rfl
  | ex _ _ => rfl
  | conjLeft _ _ ih => exact Or.inl ih
  | conjRight _ _ ih => exact Or.inr ih
  | disjLeft _ _ ih => exact Or.inl ih
  | disjRight _ _ ih => exact Or.inr ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every member of the set-valued `QF(A)` API has at least one exact
occurrence witness.  Duplicate syntax may yield several witnesses, so this is
an existential rather than a canonical choice. -/
theorem exists_of_mem {L : Language} {A Q : FormulaN L}
    (hQ : Membership.mem (maxQuantSubformulaeCore A) Q) :
    ∃ occurrence : MaxQuantifierOccurrence A, occurrence.selected = Q := by
  induction A with
  | predN _ _ => exact False.elim hQ
  | eq_ _ _ _ => exact False.elim hQ
  | neg _ _ => exact False.elim hQ
  | conj A B ihA ihB =>
      rcases hQ with hQ | hQ
      · rcases ihA hQ with ⟨occurrence, hSelected⟩
        exact ⟨.conjLeft occurrence B, hSelected⟩
      · rcases ihB hQ with ⟨occurrence, hSelected⟩
        exact ⟨.conjRight A occurrence, hSelected⟩
  | disj A B ihA ihB =>
      rcases hQ with hQ | hQ
      · rcases ihA hQ with ⟨occurrence, hSelected⟩
        exact ⟨.disjLeft occurrence B, hSelected⟩
      · rcases ihB hQ with ⟨occurrence, hSelected⟩
        exact ⟨.disjRight A occurrence, hSelected⟩
  | impl _ _ _ _ => exact False.elim hQ
  | all x B _ => exact ⟨.all x B, hQ.symm⟩
  | ex x B _ => exact ⟨.ex x B, hQ.symm⟩





end MaxQuantifierOccurrence
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Example 7.4.2 (companion type): Constant symbols for the QF
computation example. The constant b is needed for the formula Q(b). -/
@[blueprint "chap7__example_7_4_2"]
inductive QFExConst : Type where
  | b : QFExConst

-- ===================================================================
-- Example 7.4.2 (companion def): qfExLang
-- ===================================================================

/-- Example 7.4.2 (companion def): Language for the QF computation example with predicates P (unary), Q (unary), R (binary), one constant b, no function symbols, and no equality. -/
@[blueprint "chap7__example_7_4_2"]
def qfExLang : Language where
  hasEquality := false
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := QFExConst
  predSymbols := NnfExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 2

-- ===================================================================
-- Example 7.4.2 (companion def): qfExVec1
-- ===================================================================

/-- Example 7.4.2 (companion def): Build a Fin 1 -> Term from a single
variable index in the qfExLang. -/
@[blueprint "chap7__example_7_4_2"]
def qfExVec1 (n : Nat) : Fin 1 → Term qfExLang
  | ⟨0, _⟩ => .var n

-- ===================================================================
-- Example 7.4.2 (companion def): qfExVec2
-- ===================================================================

/-- Example 7.4.2 (companion def): Build a Fin 2 -> Term from two variable
indices in the qfExLang. -/
@[blueprint "chap7__example_7_4_2"]
def qfExVec2 (n m : Nat) : Fin 2 → Term qfExLang
  | ⟨0, _⟩ => .var n
  | ⟨1, _⟩ => .var m

-- ===================================================================
-- Example 7.4.2: qfExFormula
-- ===================================================================

/-- Example 7.4.2: The NNF formula A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))) or exists z P(z). Variables: u = 0, x = 1, y = 2, z = 3. Constant b from QFExConst. -/
@[blueprint "chap7__example_7_4_2"]
def qfExFormula : FormulaN qfExLang :=
  FormulaN.disj
    (FormulaN.disj
      (FormulaN.all 0 (FormulaN.predN .P (qfExVec1 0)))
      (FormulaN.conj
        (FormulaN.predN .Q (fun _ => Term.const QFExConst.b))
        (FormulaN.all 1
          (FormulaN.disj
            (FormulaN.neg (FormulaN.predN .P (qfExVec1 1)))
            (FormulaN.all 2 (FormulaN.predN .R (qfExVec2 1 2)))))))
    (FormulaN.ex 3 (FormulaN.predN .P (qfExVec1 3)))

-- ===================================================================
-- Definition 7.4.2 (companion def): isSubformulaOf
-- ===================================================================



-- ===================================================================
-- Definition 7.4.2: replaceMaxQuantSub — A[C/B]
-- ===================================================================

/-- General syntax-directed replacement for ordinary and equality consumers.
The target is compared at conjunctions, disjunctions and quantifiers; other
constructors are left unchanged. The replacement formula is arbitrary. -/
@[blueprint "chap7__definition_7_4_4"]
def replaceMaxQuantSubCore {L : Language} [DecidableEq (FormulaN L)]
    (A : FormulaN L) (B : FormulaN L) (C : FormulaN L) :
    FormulaN L :=
  match A with
  | .disj A1 A2 =>
    if FormulaN.disj A1 A2 = B then C
    else FormulaN.disj (replaceMaxQuantSubCore A1 B C)
                      (replaceMaxQuantSubCore A2 B C)
  | .conj A1 A2 =>
    if FormulaN.conj A1 A2 = B then C
    else FormulaN.conj (replaceMaxQuantSubCore A1 B C)
                      (replaceMaxQuantSubCore A2 B C)
  | .all x D =>
    if FormulaN.all x D = B then C else FormulaN.all x D
  | .ex x D =>
    if FormulaN.ex x D = B then C else FormulaN.ex x D
  | other => other

/-- Definition 7.4.2: For equality-free A in NNF and a maximal quantified
subformula B, A[C/B] replaces B by arbitrary C. On the source's distinct-binding
domain, recursion through conjunction/disjunction leaves the other branch
unchanged. The general occurrence lemmas establish this correspondence. -/
@[blueprint "chap7__definition_7_4_2" (main := true)]
def replaceMaxQuantSub {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] (A B C : FormulaN L) : FormulaN L :=
  replaceMaxQuantSubCore A B C

-- ATTACH-BLOCKER: private declaration
/-- Internal bridge helper: the legacy syntax-directed replacement is the
identity when its quantified target is absent from `QF(A)`. -/
private theorem replaceMaxQuantSub_eq_self_of_not_mem
    {L : Language} [DecidableEq (FormulaN L)]
    (A B C : FormulaN L)
    (hBquant :
      (∃ x D, B = FormulaN.all x D) ∨
        ∃ x D, B = FormulaN.ex x D)
    (hNotMem : ¬ Membership.mem (maxQuantSubformulaeCore A) B) :
    replaceMaxQuantSubCore A B C = A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ => rfl
  | impl _ _ => rfl
  | disj A1 A2 ih1 ih2 =>
      simp only [replaceMaxQuantSubCore]
      have hne : ¬ (FormulaN.disj A1 A2 = B) := by
        rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;>
          subst heq <;> intro h <;> cases h
      simp [hne]
      exact ⟨ih1 (fun hm => hNotMem (Or.inl hm)),
        ih2 (fun hm => hNotMem (Or.inr hm))⟩
  | conj A1 A2 ih1 ih2 =>
      simp only [replaceMaxQuantSubCore]
      have hne : ¬ (FormulaN.conj A1 A2 = B) := by
        rcases hBquant with ⟨x, D, heq⟩ | ⟨x, D, heq⟩ <;>
          subst heq <;> intro h <;> cases h
      simp [hne]
      exact ⟨ih1 (fun hm => hNotMem (Or.inl hm)),
        ih2 (fun hm => hNotMem (Or.inr hm))⟩
  | all x D =>
      simp only [replaceMaxQuantSubCore]
      simp [show ¬ (FormulaN.all x D = B) from
        fun heq => hNotMem (by subst heq; rfl)]
  | ex x D =>
      simp only [replaceMaxQuantSubCore]
      simp [show ¬ (FormulaN.ex x D = B) from
        fun heq => hNotMem (by subst heq; rfl)]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- When the selected quantified formula has a unique maximal occurrence, the
occurrence-sensitive replacement agrees with the legacy syntax-directed
replacement. -/
theorem MaxQuantifierOccurrence.replace_eq_replaceMaxQuantSub_of_unique
    {L : Language} [DecidableEq (FormulaN L)] {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L) (hUnique : occurrence.IsUnique) :
    occurrence.replace replacement =
      replaceMaxQuantSubCore A occurrence.selected replacement := by
  induction occurrence with
  | all _ _ =>
      simp [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected, replaceMaxQuantSubCore]
  | ex _ _ =>
      simp [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected, replaceMaxQuantSubCore]
  | conjLeft occurrence B ih =>
      have hInnerUnique : occurrence.IsUnique := by
        intro other hSelected
        have hEq := hUnique
          (MaxQuantifierOccurrence.conjLeft other B) hSelected
        cases hEq
        rfl
      have hNotMem :
          ¬ Membership.mem (maxQuantSubformulaeCore B)
            occurrence.selected := by
        intro hMem
        rcases MaxQuantifierOccurrence.exists_of_mem hMem with
          ⟨other, hSelected⟩
        have hEq := hUnique
          (MaxQuantifierOccurrence.conjRight _ other) hSelected
        cases hEq
      have hUnchanged :
          replaceMaxQuantSubCore B occurrence.selected replacement = B :=
        replaceMaxQuantSub_eq_self_of_not_mem
          B occurrence.selected replacement
          (MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence)
          hNotMem
      simp only [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected]
      simp only [replaceMaxQuantSubCore]
      split
      · rename_i hEq
        rcases MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence with
          ⟨x, D, hSelected⟩ | ⟨x, D, hSelected⟩ <;>
            rw [hSelected] at hEq <;> cases hEq
      · rw [ih hInnerUnique, hUnchanged]
  | conjRight A occurrence ih =>
      have hInnerUnique : occurrence.IsUnique := by
        intro other hSelected
        have hEq := hUnique
          (MaxQuantifierOccurrence.conjRight A other) hSelected
        cases hEq
        rfl
      have hNotMem :
          ¬ Membership.mem (maxQuantSubformulaeCore A)
            occurrence.selected := by
        intro hMem
        rcases MaxQuantifierOccurrence.exists_of_mem hMem with
          ⟨other, hSelected⟩
        have hEq := hUnique
          (MaxQuantifierOccurrence.conjLeft other _) hSelected
        cases hEq
      have hUnchanged :
          replaceMaxQuantSubCore A occurrence.selected replacement = A :=
        replaceMaxQuantSub_eq_self_of_not_mem
          A occurrence.selected replacement
          (MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence)
          hNotMem
      simp only [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected]
      simp only [replaceMaxQuantSubCore]
      split
      · rename_i hEq
        rcases MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence with
          ⟨x, D, hSelected⟩ | ⟨x, D, hSelected⟩ <;>
            rw [hSelected] at hEq <;> cases hEq
      · rw [ih hInnerUnique, hUnchanged]
  | disjLeft occurrence B ih =>
      have hInnerUnique : occurrence.IsUnique := by
        intro other hSelected
        have hEq := hUnique
          (MaxQuantifierOccurrence.disjLeft other B) hSelected
        cases hEq
        rfl
      have hNotMem :
          ¬ Membership.mem (maxQuantSubformulaeCore B)
            occurrence.selected := by
        intro hMem
        rcases MaxQuantifierOccurrence.exists_of_mem hMem with
          ⟨other, hSelected⟩
        have hEq := hUnique
          (MaxQuantifierOccurrence.disjRight _ other) hSelected
        cases hEq
      have hUnchanged :
          replaceMaxQuantSubCore B occurrence.selected replacement = B :=
        replaceMaxQuantSub_eq_self_of_not_mem
          B occurrence.selected replacement
          (MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence)
          hNotMem
      simp only [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected]
      simp only [replaceMaxQuantSubCore]
      split
      · rename_i hEq
        rcases MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence with
          ⟨x, D, hSelected⟩ | ⟨x, D, hSelected⟩ <;>
            rw [hSelected] at hEq <;> cases hEq
      · rw [ih hInnerUnique, hUnchanged]
  | disjRight A occurrence ih =>
      have hInnerUnique : occurrence.IsUnique := by
        intro other hSelected
        have hEq := hUnique
          (MaxQuantifierOccurrence.disjRight A other) hSelected
        cases hEq
        rfl
      have hNotMem :
          ¬ Membership.mem (maxQuantSubformulaeCore A)
            occurrence.selected := by
        intro hMem
        rcases MaxQuantifierOccurrence.exists_of_mem hMem with
          ⟨other, hSelected⟩
        have hEq := hUnique
          (MaxQuantifierOccurrence.disjLeft other _) hSelected
        cases hEq
      have hUnchanged :
          replaceMaxQuantSubCore A occurrence.selected replacement = A :=
        replaceMaxQuantSub_eq_self_of_not_mem
          A occurrence.selected replacement
          (MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence)
          hNotMem
      simp only [MaxQuantifierOccurrence.replace,
        MaxQuantifierOccurrence.selected]
      simp only [replaceMaxQuantSubCore]
      split
      · rename_i hEq
        rcases MaxQuantifierOccurrence.selected_eq_all_or_ex occurrence with
          ⟨x, D, hSelected⟩ | ⟨x, D, hSelected⟩ <;>
            rw [hSelected] at hEq <;> cases hEq
      · rw [ih hInnerUnique, hUnchanged]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- On the rectified-domain distinct-binding invariant used throughout §7.4,
exact occurrence replacement agrees with Definition 7.4.2's legacy
syntax-directed operation. -/
theorem MaxQuantifierOccurrence.replace_eq_replaceMaxQuantSub_of_distinct
    {L : Language} [DecidableEq (FormulaN L)] {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L)
    (hDistinct : distinctQuantifierBindings A) :
    occurrence.replace replacement =
      replaceMaxQuantSubCore A occurrence.selected replacement :=
  occurrence.replace_eq_replaceMaxQuantSub_of_unique replacement
    (occurrence.isUnique_of_distinctQuantifierBindings hDistinct)

-- ===================================================================
-- Example 7.4.3 (companion type): ReplExFunc
-- ===================================================================

/-- Example 7.4.3 (companion type): Function symbols for the
replacement example language: f (unary). -/
@[blueprint "chap7__example_7_4_3"]
inductive ReplExFunc : Type where
  | f : ReplExFunc

-- ===================================================================
-- Example 7.4.3 (companion type): ReplExConst
-- ===================================================================

/-- Example 7.4.3 (companion type): Constant symbols for the
replacement example language: a and b. -/
@[blueprint "chap7__example_7_4_3"]
inductive ReplExConst : Type where
  | a : ReplExConst
  | b : ReplExConst

-- ===================================================================
-- Example 7.4.3 (companion def): replExLang
-- ===================================================================

/-- Example 7.4.3 (companion def): Language for the replacement example with predicates P (unary), Q (unary), R (binary), unary function f, constants a and b, and no equality. -/
@[blueprint "chap7__example_7_4_3"]
def replExLang : Language where
  hasEquality := false
  funSymbols := ReplExFunc
  funArity := fun | .f => 1
  constSymbols := ReplExConst
  predSymbols := NnfExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 2

-- ===================================================================
-- Example 7.4.3 (companion def): replExVec1
-- ===================================================================

/-- Example 7.4.3 (companion def): Build a Fin 1 -> Term from a single
term in replExLang. -/
@[blueprint "chap7__example_7_4_3"]
def replExVec1 (t : Term replExLang) : Fin 1 → Term replExLang
  | ⟨0, _⟩ => t

-- ===================================================================
-- Example 7.4.3 (companion def): replExVec2
-- ===================================================================

/-- Example 7.4.3 (companion def): Build a Fin 2 -> Term from two terms
in replExLang. -/
@[blueprint "chap7__example_7_4_3"]
def replExVec2 (t1 t2 : Term replExLang) :
    Fin 2 → Term replExLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- ===================================================================
-- Example 7.4.3 (companion def): replEx_fa
-- ===================================================================

/-- Example 7.4.3 (companion def): The term f(a) used as the substitution
term in the replacement. -/
@[blueprint "chap7__example_7_4_3"]
def replEx_fa : Term replExLang :=
  Term.func ReplExFunc.f (replExVec1 (Term.const ReplExConst.a))

-- ===================================================================
-- Example 7.4.3: replaceExFormula
-- ===================================================================

/-- Example 7.4.3: The formula A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))). Variables: u = 0, x = 1, y = 2. -/
@[blueprint "chap7__example_7_4_3"]
def replaceExFormula : FormulaN replExLang :=
  FormulaN.disj
    (FormulaN.all 0 (FormulaN.predN .P (replExVec1 (.var 0))))
    (FormulaN.conj
      (FormulaN.predN .Q (replExVec1 (.const ReplExConst.b)))
      (FormulaN.all 1
        (FormulaN.disj
          (FormulaN.neg (FormulaN.predN .P (replExVec1 (.var 1))))
          (FormulaN.all 2
            (FormulaN.predN .R (replExVec2 (.var 1) (.var 2)))))))

-- ===================================================================
-- Example 7.4.3 (companion def): replaceExTarget
-- ===================================================================

/-- Example 7.4.3 (companion def): B = forall x(not P(x) or forall y R(x, y)), the maximal quantified subformula being replaced. Variables: x = 1, y = 2. -/
@[blueprint "chap7__example_7_4_3"]
def replaceExTarget : FormulaN replExLang :=
  FormulaN.all 1
    (FormulaN.disj
      (FormulaN.neg (FormulaN.predN .P (replExVec1 (.var 1))))
      (FormulaN.all 2
        (FormulaN.predN .R (replExVec2 (.var 1) (.var 2)))))

-- ===================================================================
-- Example 7.4.3 (companion def): replaceExReplacement
-- ===================================================================

/-- Example 7.4.3 (companion def): C = (not P(f(a)) or forall y R(f(a), y)), the replacement formula obtained by instantiating x with f(a) in the body of B. Variables: y = 2. -/
@[blueprint "chap7__example_7_4_3"]
def replaceExReplacement : FormulaN replExLang :=
  FormulaN.disj
    (FormulaN.neg (FormulaN.predN .P (replExVec1 replEx_fa)))
    (FormulaN.all 2
      (FormulaN.predN .R (replExVec2 replEx_fa (.var 2))))

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfRule

/-- Definition 7.4.3 (companion): The conclusion of the stored equality-free
rule instance. Atomic conclusions are bare; cut unions independent contexts. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  rule.val.conclusion

/-- Definition 7.4.3 (companion): The actual premises of the stored rule.
Cut has independent contexts, and quantified replacement follows the exact
constructor-carried maximal occurrence. -/
@[blueprint "chap7__definition_7_4_3"]
def premises {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) :
    List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :=
  rule.val.premises

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The rule-local free-for and eigenvariable freshness requirements. -/
def CoreSideConditions {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop := rule.val.LogicalSideConditions

/-- Definition 7.4.3 (companion): A legal equality-free inference has NNF
premises and conclusion, satisfies free-for/eigenvariable freshness, and has
a rectified conclusion. Bare atomic admission is evidence in the rule itself. -/
@[blueprint "chap7__definition_7_4_3"]
def SideConditions {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) : Prop :=
  rule.val.SideConditions

end G2nnfRule
end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfRule
namespace SideConditions

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem core {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {rule : G2nnfRule L hL}
    (hSC : rule.SideConditions) : rule.CoreSideConditions := hSC.logical

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
theorem allRectified {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {rule : G2nnfRule L hL}
    (hSC : rule.SideConditions) : AllRectified rule.conclusion :=
  hSC.conclusionRectified

end SideConditions
end G2nnfRule
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Definition 7.4.3 (required companion): Equality-free proof trees use the
shared indexed recursion with BareAtomicAxiom admission at every inference,
no extra axioms, and no open leaves. Every node has NNF and rectification
evidence; child indices match the actual rule premises. -/
@[blueprint "chap7__definition_7_4_3"]
abbrev G2nnfProofTree {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] :=
  G2nnfProofTreeCore (L := L) G2nnfRuleCore.BareAtomicAxiom (fun _ => False)

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfProofTree

/-- Definition 7.4.3 (companion): The conclusion is the proof tree's index. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfProofTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) : T.conclusion = (Gamma, Delta) := rfl

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Rectification holds at every proof node. -/
theorem allRectified {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) : AllRectified (Gamma, Delta) := by
  cases T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ hExtra _ _ => exact hExtra.elim
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

end G2nnfProofTree
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Definition 7.4.3 (required companion): Equality-free deductions use the
same recursion and bare-axiom admission as proofs, with NNF rectified open
leaves allowed. Extra axioms remain excluded at every depth. -/
@[blueprint "chap7__definition_7_4_3"]
abbrev G2nnfDeductionTree {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] :=
  G2nnfDeductionTreeCore (L := L) G2nnfRuleCore.BareAtomicAxiom
    (fun _ => False) (fun _ => True)

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfDeductionTree

/-- Definition 7.4.3 (companion): The deduction's indexed conclusion. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfDeductionTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfDeductionTree hL Gamma Delta) : T.conclusion = (Gamma, Delta) := rfl

/-- Definition 7.4.3 (companion): Every open leaf is an admissible bare atomic
axiom. Ordinary axiom nodes are already certified by their constructor. -/
@[blueprint "chap7__definition_7_4_3"]
def isProof {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Gamma Delta : LCS.Finset (FormulaN L)} → G2nnfDeductionTree hL Gamma Delta → Prop
  | _, _, .leaf Gamma Delta _ _ _ =>
      ∃ rule : G2nnfRule L hL,
        rule.premises.length = 0 ∧ rule.SideConditions ∧
        rule.conclusion = (Gamma, Delta)
  | _, _, .extraAxiom _ _ _ _ _ => False
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise _ _ _ _ sub => isProof (hL := hL) sub
  | _, _, .twoPremise _ _ _ _ sub1 sub2 =>
      isProof (hL := hL) sub1 ∧ isProof (hL := hL) sub2

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.Trees, LCS.CutElim.Interpolation.VariableSubstitution, LCS.CutElim.LK.Part1, LCS.CutElim.LKe, LCS.FirstOrder.Equality.Part1, LCS.FirstOrder.Gentzen.Part1, LCS.FirstOrder.Gentzen.Part2, LCS.FirstOrder.Gentzen.Search.NoFunction.Examples, LCS.FirstOrder.Gentzen.Search.NoFunction.Search, LCS.Propositional.Systems.G
/-- Definition 7.4.3 (companion): Close each certified deduction leaf by its
bare axiom, preserving the indexed conclusion and each internal inference.
As in the existing interface, extraction of a leaf's existential rule witness
is noncomputable. -/
noncomputable def toProofTree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Gamma Delta : LCS.Finset (FormulaN L)} →
    (T : G2nnfDeductionTree hL Gamma Delta) → isProof (hL := hL) T →
      G2nnfProofTree hL Gamma Delta
  | _, _, .leaf Gamma Delta _ _ _, hp => by
      let rule := Classical.choose hp
      have hspec := Classical.choose_spec hp
      have hTree : G2nnfProofTree hL rule.conclusion.1 rule.conclusion.2 :=
        .axiom_ rule.val rule.property hspec.1 hspec.2.1
      rw [hspec.2.2] at hTree
      exact hTree
  | _, _, .extraAxiom _ _ hExtra _ _, _ => hExtra.elim
  | _, _, .axiom_ rule hAdmit hAxiom hSC, _ => .axiom_ rule hAdmit hAxiom hSC
  | _, _, .onePremise rule hAdmit hPrem hSC sub, hp =>
      .onePremise rule hAdmit hPrem hSC (toProofTree (hL := hL) sub hp)
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2, hp =>
      .twoPremise rule hAdmit hPrem hSC
        (toProofTree (hL := hL) sub1 hp.1) (toProofTree (hL := hL) sub2 hp.2)

end G2nnfDeductionTree
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Definition 7.4.3 (companion): Provability in the equality-free, bare-axiom
NNF calculus, witnessed by a proof tree with the given conclusion. -/
@[blueprint "chap7__definition_7_4_3"]
def g2nnfProvable {L : Language} (hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] (Gamma Delta : LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G2nnfProofTree hL Gamma Delta)

-- ===================================================================
-- Example 7.4.2 (companion theorem): qfExResult
-- ===================================================================

/-- Example 7.4.2 (companion theorem): The computation QF(A) = {forall u P(u), forall x(not P(x) or forall y R(x,y)), exists z P(z)}, verifying the textbook's claimed result for the formula A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))) or exists z P(z). -/
@[blueprint "chap7__example_7_4_2" (main := true)]
theorem qfExResult :
    maxQuantSubformulae (by rfl) qfExFormula =
      sng (FormulaN.all 0
            (FormulaN.predN NnfExPred.P (qfExVec1 0))) ∪
      (∅ ∪ sng (FormulaN.all 1
        (FormulaN.disj
          (FormulaN.neg (FormulaN.predN NnfExPred.P (qfExVec1 1)))
          (FormulaN.all 2
            (FormulaN.predN NnfExPred.R
              (qfExVec2 1 2)))))) ∪
      sng (FormulaN.ex 3
            (FormulaN.predN NnfExPred.P (qfExVec1 3))) 

-- ===================================================================
-- Example 7.4.2 (companion theorem): qfExNonMaximal
-- ===================================================================

/-- Example 7.4.2 (companion theorem): The formula forall y R(x, y) is NOT in QF(A) because it is nested inside the larger quantified formula forall x(not P(x) or forall y R(x, y)), which is itself a maximal quantified subformula. This demonstrates the maximality exclusion principle. -/
@[blueprint "chap7__example_7_4_2" (main := true)]
theorem qfExNonMaximal :
    ¬ Membership.mem
      (maxQuantSubformulae (by rfl) qfExFormula)
      (FormulaN.all 2
        (FormulaN.predN NnfExPred.R (qfExVec2 1 2))) 

-- ===================================================================
-- Example 7.4.3 (companion theorem): replaceExResult
-- ===================================================================

/-- Example 7.4.3 (companion theorem): Verifies that A[C/B] = forall u P(u) or (Q(b) and (not P(f(a)) or forall y R(f(a), y))), the textbook's stated result of replacing B = forall x(not P(x) or forall y R(x, y)) with C = (not P(f(a)) or forall y R(f(a), y)) in A = forall u P(u) or (Q(b) and forall x(not P(x) or forall y R(x, y))). -/
@[blueprint "chap7__example_7_4_3" (main := true)]
theorem replaceExResult [DecidableEq (FormulaN replExLang)] :
    replaceMaxQuantSub (by rfl) replaceExFormula replaceExTarget
      replaceExReplacement =
      FormulaN.disj
        (FormulaN.all 0
          (FormulaN.predN NnfExPred.P
            (replExVec1 (.var 0))))
        (FormulaN.conj
          (FormulaN.predN NnfExPred.Q
            (replExVec1 (.const ReplExConst.b)))
          (FormulaN.disj
            (FormulaN.neg
              (FormulaN.predN NnfExPred.P
                (replExVec1 replEx_fa)))
            (FormulaN.all 2
              (FormulaN.predN NnfExPred.R
                (replExVec2 replEx_fa (.var 2)))))) 

-- ===================================================================
-- Definition 7.4.4: G2nnfEqRule — G2nnf_= inference rules
-- ===================================================================

/-- Definition 7.4.4: The system G2nnf_= is obtained from G1nnf_= by adding
the quantifier rules of Definition 7.4.3 and weakening. Its ordinary atomic
axioms and equality axioms are contextual. Base rules include the independent
context cut; equality schemas are reused from `G1nnfEqAxiom`. -/
@[blueprint "chap7__definition_7_4_4" (main := true)]
inductive G2nnfEqRule (L : Language) (hL : L.hasEquality = true) : Type where
  /-- A general core rule with its own stored contexts. -/
  | base (r : G2nnfRuleCore L) : G2nnfEqRule L hL
  /-- An equality axiom schema shared with G1nnf_= (Def 6.4.6) -/
  | eqAxiom (ax : G1nnfEqAxiom L hL) : G2nnfEqRule L hL

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfEqRule

/-- Definition 7.4.4 (companion): The cut formula of a core cut;
all other core inferences and equality axioms return none. -/
@[blueprint "chap7__definition_7_4_4"]
def cutFormula {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Option (FormulaN L)
  | .base (.cut A _ _ _ _) => some A
  | .base _ => none
  | .eqAxiom _ => none

/-- Definition 7.4.4 (companion): The actual stored conclusion. Ordinary
contextual axioms and independent cuts use Core; equality schemas retain
their canonical G1nnf= frames via toSequent. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    G2nnfEqRule L hL → LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .base r => r.conclusion
  | .eqAxiom ax => ax.toSequent

/-- Definition 7.4.4 (companion): The stored core premises, or no premises
for an equality axiom. Ordinary contextual atomic axioms also have none. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def premises {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    G2nnfEqRule L hL → List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | .base r => r.premises
  | .eqAxiom _ => []

/-- Definition 7.4.4 (companion): Core rules, including contextual ordinary
axioms, satisfy Core side conditions. Equality axioms retain WellFormed for
their recursive negation closures, and every formula in the full contextual
conclusion must be NNF and rectified. No bare-axiom restriction is imposed. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def SideConditions {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] : G2nnfEqRule L hL → Prop
  | .base r => r.SideConditions
  | .eqAxiom ax => ax.WellFormed ∧ AllNNF ax.toSequent ∧ AllRectified ax.toSequent









end G2nnfEqRule
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Definition 7.4.4 (companion): An extra-axiom sequent is exactly the
canonical sequent of a well-formed G1nnf= equality schema. The tree carrier
separately enforces NNF and rectification on the entire sequent. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def G2nnfEqRule.EqualityAxiomSequent {L : Language}
    (hL : L.hasEquality = true)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  ∃ ax : G1nnfEqAxiom L hL, ax.WellFormed ∧ ax.toSequent = seq

/-- Definition 7.4.4 (required type): Equality proofs instantiate the shared
Core recursion with contextual ordinary rules and well-formed G1nnf= equality
axioms. Every node is NNF and rectified. Open leaves are excluded at every
depth; the equality-language witness fixes the available axiom schemas. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfEqProofTree {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] :=
  G2nnfProofTreeCore (L := L) (fun _ => True)
    (G2nnfEqRule.EqualityAxiomSequent hL)

/-- Definition 7.4.4 (companion): Equality deductions use the same contextual
Core rules and equality axioms as proofs, with NNF rectified open leaves. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfEqDeductionTree {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] :=
  G2nnfDeductionTreeCore (L := L) (fun _ => True)
    (G2nnfEqRule.EqualityAxiomSequent hL) (fun _ => True)

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfEqDeductionTree

/-- Definition 7.4.4 (companion): The equality deduction's indexed conclusion. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfEqDeductionTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfEqDeductionTree hL Gamma Delta) : T.conclusion = (Gamma, Delta) := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem allNNF {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfEqDeductionTree hL Gamma Delta) : AllNNF (Gamma, Delta) :=
  G2nnfDeductionTreeCore.allNNF T

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
theorem allRectified {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfEqDeductionTree hL Gamma Delta) : AllRectified (Gamma, Delta) := by
  cases T with
  | leaf _ _ _ _ hRect => exact hRect
  | extraAxiom _ _ _ _ hRect => exact hRect
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

end G2nnfEqDeductionTree
end LCS.Herbrand.NNFHauptsatz
end

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









end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfEqProofTree

/-- Definition 7.4.4 (companion def): Returns the conclusion sequent of a G2nnf_= proof tree. For the indexed tree this is just the type index `(Γ, Δ)`. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G2nnfEqProofTree hL Γ Δ) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Every node conclusion in a G2nnf= proof tree satisfies §7.4's standing
rectification invariant. -/
theorem allRectified {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) :
    AllRectified (Γ, Δ) := by
  cases T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ _ _ hRect => exact hRect
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The full conclusion at each equality-system node is in NNF. -/
theorem allNNF {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Gamma Delta) : AllNNF (Gamma, Delta) :=
  G2nnfDeductionTreeCore.allNNF T

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G2nnfEqProofTree hL Γ Δ) :
    T.conclusion = (Γ, Δ) := rfl

/-- Definition 7.4.4 (companion def): Extract the root-level cut formula of a G2nnf_= proof tree — that is, the `cutFormula` of the rule at the tree's root inference. Returns `none` for axiom leaves and for all non-cut inferences (equality axioms, weakening, propositional, quantifier rules). Used by `hasNoEssentialCuts` (Theorem 7.4.2). -/
@[blueprint "chap7__definition_7_4_4"]
def cutFormula {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} :
    G2nnfEqProofTree hL Γ Δ → Option (FormulaN L)
  | .leaf _ _ hOpen _ _ => hOpen.elim
  | .extraAxiom _ _ _ _ _ => none
  | .axiom_ rule _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula
  | .onePremise rule _ _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula
  | .twoPremise rule _ _ _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula

end G2nnfEqProofTree
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Theorem 7.4.2 (required def): A cut is inessential if its cut formula is a literal over the equality predicate, i.e., it has the form `s = t` or `neg(s = t)`. Inessential cuts are allowed in a "proof without essential cuts" by the sharpened Hauptsatz for G2nnf_= (Theorem 7.4.2). Mirrors the G1nnf_= notion from Def 6.4.9. -/
@[blueprint "chap7__theorem_7_4_2"]
def isInessentialCut {L : Language} : FormulaN L → Prop
  | .eq_ _ _ _ => True
  | .neg (.eq_ _ _ _) => True
  | _ => False

end LCS.Herbrand.NNFHauptsatz
end

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
namespace G2nnfEqProofTree

/-- Theorem 7.4.2 (required def): A G2nnf_= proof tree has no essential cuts iff every cut application in the tree uses an inessential cut formula (literal equality `s = t` or its negation `neg(s = t)`). Defined by structural recursion: an axiom leaf has no cuts; one-premise nodes propagate the sub-tree check; two-premise nodes additionally require that if the root rule has a cut formula (i.e., is a cut), that formula is inessential. -/
@[blueprint "chap7__theorem_7_4_2"]
def hasNoEssentialCuts {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => True
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise _ _ _ _ sub => hasNoEssentialCuts (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (match (G2nnfEqRule.base (hL := hL) rule).cutFormula with
      | some A => isInessentialCut A
      | none => True) ∧
    hasNoEssentialCuts (hL := hL) sub1 ∧ hasNoEssentialCuts (hL := hL) sub2

end G2nnfEqProofTree
end LCS.Herbrand.NNFHauptsatz
end

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

/-- Definition 7.4.4 (companion def): Provability in G2nnf_=. A sequent `(Γ, Δ)` is `g2nnfEqProvable` iff the shared NNF carrier has a closed proof with that conclusion, contextual core rules and well-formed equality axioms over the equality language. -/
@[blueprint "chap7__definition_7_4_4"]
def g2nnfEqProvable {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G2nnfEqProofTree hL Γ Δ)

end LCS.Herbrand.NNFHauptsatz
end

