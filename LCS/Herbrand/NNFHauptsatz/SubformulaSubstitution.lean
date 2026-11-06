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
import Attach
import LCS.Herbrand.NNFHauptsatz.SubformulaSubstitution.ProofsStamp

/-! # Herbrand.NNFHauptsatz.SubformulaSubstitution

Definition 7.4.2: substitution A[C/B] for a maximal quantified subformula,
with Example 7.4.3.
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
namespace MaxQuantifierOccurrence

/-- Replace exactly the selected occurrence and leave every other branch
unchanged.  No formula equality test is needed because the occurrence path
already determines the replacement site. -/
@[blueprint "chap7__definition_7_4_2"]
def replace {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    FormulaN L :=
  match occurrence with
  | .all _ _ => replacement
  | .ex _ _ => replacement
  | .conjLeft inner B => .conj (inner.replace replacement) B
  | .conjRight A inner => .conj A (inner.replace replacement)
  | .disjLeft inner B => .disj (inner.replace replacement) B
  | .disjRight A inner => .disj A (inner.replace replacement)

end MaxQuantifierOccurrence

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
end LCS.Herbrand.NNFHauptsatz
end
