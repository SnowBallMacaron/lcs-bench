import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.SHGTheorem.UniversalScope.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

/-- Definition 7.6.1: Given a rectified formula A in NNF, the set US(A) of pairs (B, L) where B is a subformula of A and L is a sequence of variables is defined inductively: - US_0 = {(A, [])} - US_{k+1} = US_k union: - {(C, L), (D, L) | (B, L) in US_k, B = C and D or B = C or D} - {(C, L) | (exists x C, L) in US_k} - {(C, y_1::...::y_m::x) | (forall x C, y_1::...::y_m) in US_k} USPair is an inductive derivation tree witnessing membership of a pair (B, L) in US(A). Each constructor records the step used to derive the pair from the base case (A, []). The universal scope of a subformula B is the sequence L of universally quantified variables on the path from A to B. The type `USPair L root sub scope` is indexed by the root formula `root`, the derived subformula `sub`, and the scope `scope` — so a value of this type genuinely witnesses `⟨sub, scope⟩ ∈ US(root)`. Each constructor's output index is forced by the textbook's derivation rule. -/
@[blueprint "chap7__definition_7_6_1"]
inductive USPair (L : Language) :
    FormulaN L → FormulaN L → List Nat → Type where
  /-- US base case: (A, []) is in US(A) for the root formula A -/
  | base (A : FormulaN L) : USPair L A A []
  /-- US conjunction step (left conjunct): if (C and D, scope) is in
      US_k, then (C, scope) is in US_{k+1} -/
  | conjLeft {A : FormulaN L} (C D : FormulaN L) (scope : List Nat)
      (parent : USPair L A (.conj C D) scope) :
      USPair L A C scope
  /-- US conjunction step (right conjunct): if (C and D, scope) is in
      US_k, then (D, scope) is in US_{k+1} -/
  | conjRight {A : FormulaN L} (C D : FormulaN L) (scope : List Nat)
      (parent : USPair L A (.conj C D) scope) :
      USPair L A D scope
  /-- US disjunction step (left disjunct): if (C or D, scope) is in
      US_k, then (C, scope) is in US_{k+1} -/
  | disjLeft {A : FormulaN L} (C D : FormulaN L) (scope : List Nat)
      (parent : USPair L A (.disj C D) scope) :
      USPair L A C scope
  /-- US disjunction step (right disjunct): if (C or D, scope) is in
      US_k, then (D, scope) is in US_{k+1} -/
  | disjRight {A : FormulaN L} (C D : FormulaN L) (scope : List Nat)
      (parent : USPair L A (.disj C D) scope) :
      USPair L A D scope
  /-- US existential quantifier step: if (exists x C, scope) is in
      US_k, then (C, scope) is in US_{k+1}. The existential quantifier
      is stripped without modifying the scope. -/
  | existStrip {A : FormulaN L} (x : Nat) (C : FormulaN L)
      (scope : List Nat)
      (parent : USPair L A (.ex x C) scope) :
      USPair L A C scope
  /-- US universal quantifier step: if (forall x C, scope) is in
      US_k, then (C, scope ++ [x]) is in US_{k+1}. The universally
      quantified variable x is appended to the scope. -/
  | univExtend {A : FormulaN L} (x : Nat) (C : FormulaN L)
      (scope : List Nat)
      (parent : USPair L A (.all x C) scope) :
      USPair L A C (scope ++ [x])

-- ===================================================================
-- Definition 7.6.1 (companion def): universalScopeAux
-- ===================================================================

/-- Definition 7.6.1: Preorder list of formula/scope pairs in the
US closure. Repeated occurrences retain separate list cells, even when
both their labels and scopes coincide. Conjunction and disjunction visit
both children, existential descent preserves the scope, and universal
descent appends its binder. Literals are leaves of this closure. -/
@[blueprint "chap7__definition_7_6_1"]
def universalScopeAux {L : Language} :
    FormulaN L → List Nat →
    List (FormulaN L × List Nat)
  | .conj C D, acc =>
    [(.conj C D, acc)] ++
    universalScopeAux C acc ++ universalScopeAux D acc
  | .disj C D, acc =>
    [(.disj C D, acc)] ++
    universalScopeAux C acc ++ universalScopeAux D acc
  | .ex x C, acc =>
    [(.ex x C, acc)] ++ universalScopeAux C acc
  | .all x C, acc =>
    [(.all x C, acc)] ++ universalScopeAux C (acc ++ [x])
  | other, acc => [(other, acc)]

-- ===================================================================
-- Definition 7.6.1 (companion def): USSet
-- ===================================================================

/-- Definition 7.6.1: The set of formula/scope pairs in the US closure
of a rectified NNF formula. This forgets occurrence identity; equal formula
labels may occur with different scopes. `universalScopeAt` selects an exact
occurrence, while this set records the resulting pairs. -/
@[blueprint "chap7__definition_7_6_1" (main := true)]
def USSet {L : Language}
    (A : FormulaN L)
    (_hNNF : A.isNNF)
    (_hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    Set (FormulaN L × List Nat) :=
  fun pair => pair ∈ universalScopeAux A []

-- ===================================================================
-- Example 7.6.2 (companion type): USExPred
-- ===================================================================

/-- Example 7.6.2 (companion type): Predicate symbols for the universal scope example: P1 (unary), Q1 (unary), P2 (binary), Q2 (binary). -/
@[blueprint "chap7__example_7_6_2"]
inductive USExPred : Type where
  | P1 : USExPred
  | Q1 : USExPred
  | P2 : USExPred
  | Q2 : USExPred

-- ===================================================================
-- Example 7.6.2 (companion type): USExConst
-- ===================================================================

/-- Example 7.6.2 (companion type): Constant symbols for the
universal scope example: a. -/
@[blueprint "chap7__example_7_6_2"]
inductive USExConst : Type where
  | a : USExConst

-- ===================================================================
-- Example 7.6.2 (companion def): usExLang
-- ===================================================================

/-- Example 7.6.2 (companion def): A language with predicates P1 (unary), Q1 (unary), P2 (binary), Q2 (binary), constant a, and no function symbols. -/
@[blueprint "chap7__example_7_6_2"]
def usExLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := USExConst
  predSymbols := USExPred
  predArity := fun
    | .P1 => 1
    | .Q1 => 1
    | .P2 => 2
    | .Q2 => 2

-- ===================================================================
-- Example 7.6.2 (helpers): usExVec1, usExVec2
-- ===================================================================

/-- Example 7.6.2 (companion def): Build a Fin 1 -> Term from a single
term in usExLang. -/
@[blueprint "chap7__example_7_6_2"]
def usExVec1 (t : Term usExLang) : Fin 1 → Term usExLang
  | ⟨0, _⟩ => t

/-- Example 7.6.2 (companion def): Build a Fin 2 -> Term from two terms
in usExLang. -/
@[blueprint "chap7__example_7_6_2"]
def usExVec2 (t1 t2 : Term usExLang) :
    Fin 2 → Term usExLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

/-- Example 7.6.2: The NNF formula A = forall x(P(a) or exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) or exists w Q(a, w). Variables: x = 0, y = 1, z = 2, u = 3, w = 4. -/
@[blueprint "chap7__example_7_6_2"]
def usExFormula : FormulaN usExLang :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (usExVec1 (.const USExConst.a)))
        (FormulaN.ex 1
          (FormulaN.conj
            (FormulaN.predN USExPred.Q1
              (usExVec1 (.var 1)))
            (FormulaN.all 2
              (FormulaN.disj
                (FormulaN.predN USExPred.P2
                  (usExVec2 (.var 1) (.var 2)))
                (FormulaN.ex 3
                  (FormulaN.predN USExPred.Q2
                    (usExVec2 (.var 0) (.var 3))))))))))
    (FormulaN.ex 4
      (FormulaN.predN USExPred.Q2
        (usExVec2 (.const USExConst.a) (.var 4))))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsYSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u))). Variables: x = 0, y = 1, z = 2, u = 3. Universal scope is <x>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsYSubformula : FormulaN usExLang :=
  FormulaN.ex 1
    (FormulaN.conj
      (FormulaN.predN USExPred.Q1
        (usExVec1 (.var 1)))
      (FormulaN.all 2
        (FormulaN.disj
          (FormulaN.predN USExPred.P2
            (usExVec2 (.var 1) (.var 2)))
          (FormulaN.ex 3
            (FormulaN.predN USExPred.Q2
              (usExVec2 (.var 0) (.var 3)))))))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsUSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists u Q(x, u).
Variables: x = 0, u = 3. Universal scope is <x, z>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsUSubformula : FormulaN usExLang :=
  FormulaN.ex 3
    (FormulaN.predN USExPred.Q2
      (usExVec2 (.var 0) (.var 3)))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsWSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists w Q(a, w).
Variables: w = 4. Universal scope is empty <>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsWSubformula : FormulaN usExLang :=
  FormulaN.ex 4
    (FormulaN.predN USExPred.Q2
      (usExVec2 (.const USExConst.a) (.var 4)))

end LCS.Herbrand.SHGTheorem
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

-- ===================================================================
-- Definition 7.6.1 (companion def): universalScope
-- ===================================================================

/-- Definition 7.6.1: Label-based membership in US(A) for a rectified
NNF root. This asserts that some occurrence of B has the given scope;
uniqueness belongs to a fixed occurrence, queried by `universalScopeAt`. -/
@[blueprint "chap7__definition_7_6_1"]
def universalScope {L : Language}
    (A B : FormulaN L) (scope : List Nat)
    (_hNNF : A.isNNF)
    (_hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    Prop :=
  (B, scope) ∈ universalScopeAux A []

/-- Follow an address in the US closure, carrying the ordered scope.
`false` selects the left child of a connective or the body of a quantifier;
`true` selects the right child of a connective. An empty address selects
the current node. Invalid steps return `none`; literals have no children. -/
@[blueprint "chap7__definition_7_6_1"]
def universalScopeAtAux {L : Language} :
    FormulaN L → List Bool → List Nat → Option (FormulaN L × List Nat)
  | A, [], scope => some (A, scope)
  | .conj C _, false :: path, scope
  | .disj C _, false :: path, scope => universalScopeAtAux C path scope
  | .conj _ D, true :: path, scope
  | .disj _ D, true :: path, scope => universalScopeAtAux D path scope
  | .ex _ C, false :: path, scope => universalScopeAtAux C path scope
  | .all x C, false :: path, scope => universalScopeAtAux C path (scope ++ [x])
  | _, _ :: _, _ => none

/-- Definition 7.6.1: Query the formula and unique ordered universal scope
at an occurrence of a rectified NNF formula (SQ047). Addresses are paths
from the root: `false` means left/body and `true` means right. The scope
contains exactly the universal binders above the selected node, in outer
to inner order. Equal labels at distinct addresses are queried separately.
Negated atoms are leaves, as in the defining US closure. -/
@[blueprint "chap7__definition_7_6_1" (main := true)]
def universalScopeAt {L : Language}
    (A : FormulaN L) (path : List Bool)
    (_hNNF : A.isNNF)
    (_hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    Option (FormulaN L × List Nat) :=
  universalScopeAtAux A path []

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsY
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u))) in the formula A is the single variable x = 0. That is, the pair (usExExistsYSubformula, [0]) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsY
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsYSubformula [0] hNNF hRect 

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsU
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists u Q(x, u) in the formula A is the variable sequence x, z (i.e., [0, 2]). That is, the pair (usExExistsUSubformula, [0, 2]) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsU
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsUSubformula [0, 2] hNNF hRect 

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsW
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists w Q(a, w) in the formula A is the empty sequence []. That is, the pair (usExExistsWSubformula, []) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsW
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsWSubformula [] hNNF hRect 

end LCS.Herbrand.SHGTheorem
end
